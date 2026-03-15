use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use rand::{seq::SliceRandom, CryptoRng, Rng, SeedableRng};
use scuttlebutt::{
    field::FiniteField,
    ring::FiniteRing,
    AbstractChannel, AesRng, Block,
};

use crate::dabits::OPRFSharing;

pub fn triple_client<F: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    parameters: (usize, usize, usize),
    fcom_p: &mut FComProver<F>,
    fcom_v: &mut FComVerifier<F>,
    channel: &mut C,
    rng: &mut RNG,
) -> Vec<(OPRFSharing<F>, OPRFSharing<F>, OPRFSharing<F>)> {
    let (ell, b, c) = parameters;
    let m = b * b * ell + c;

    // Step 1
    let mut a_i = Vec::with_capacity(m);
    let mut c_i_c = Vec::with_capacity(m);
    for _ in 0..m {
        let com = fcom_p.random(channel, rng).unwrap();
        a_i.push(com);
    }

    let delta_i = channel.read_serializable_seq::<F::PrimeField>(m).unwrap();
    let mut c_i_value = Vec::with_capacity(m);

    for i in 0..m {
        let m_a_i = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&a_i[i].mac().to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
                .unwrap()
                .into();
            F::PrimeField::from_uniform_bytes(&bytes)
        };
        let ci = m_a_i + delta_i[i] * a_i[i].value() * a_i[i].value();
        c_i_value.push(ci);
    }
    drop(delta_i);

    let com_c_mac = fcom_p.input(channel, rng, &c_i_value).unwrap();
    channel.flush().unwrap();
    for i in 0..m {
        let com_c = MacProver::<F>::new(c_i_value[i], com_c_mac[i]);
        c_i_c.push(com_c);
    }
    drop(com_c_mac);
    drop(c_i_value);

    let mut c_i_s = fcom_v.input(channel, rng, m).unwrap();
    let mut b_i = fcom_v.input(channel, rng, m).unwrap();

    // Step 2
    let seed = channel.read_block().unwrap();
    let mut seed_rng = AesRng::from_seed(seed);
    {
        let mut a_i_to_open = Vec::with_capacity(c);
        let mut c_i_c_to_open = Vec::with_capacity(c);
        let mut b_i_to_open = Vec::with_capacity(c);
        let mut c_i_s_to_open = Vec::with_capacity(c);
        let mut s = Vec::with_capacity(m);
        for _ in 0..(m - c) {
            s.push(0);
        }
        for _ in 0..c {
            s.push(1);
        }
        s.shuffle(&mut seed_rng);

        for i in 0..m {
            if s[i] == 1 {
                a_i_to_open.push(a_i[i]);
                b_i_to_open.push(b_i[i]);
                c_i_c_to_open.push(c_i_c[i]);
                c_i_s_to_open.push(c_i_s[i]);
            }
        }
        
        let _ = fcom_p.open(channel, &a_i_to_open).unwrap();
        let mut b_opened = Vec::with_capacity(c);
        let _ = fcom_v.open(channel, &b_i_to_open, &mut b_opened).unwrap();
        let _ = fcom_p.open(channel, &c_i_c_to_open).unwrap();
        let mut c_i_s_opened = Vec::with_capacity(c);
        let _ = fcom_v.open(channel, &c_i_s_to_open, &mut c_i_s_opened);
        
        for i in 0..c {
            let lhs = a_i_to_open[i].value() * b_opened[i];
            let rhs = c_i_c_to_open[i].value() + c_i_s_opened[i];
            assert_eq!(lhs, rhs);
        }
        for i in (0..m).rev() {
            if s[i] == 1 {
                a_i.remove(i);
                b_i.remove(i);
                c_i_c.remove(i);
                c_i_s.remove(i);
            }
        }
    }

    channel.flush().unwrap();

    let mut bucketing = Vec::with_capacity(ell * b * b);
    for _ in 0..b {
        for j in 0..(ell * b) {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);

    let mut buckets_index: Vec<Vec<usize>> = (0..ell*b).map(|_| Vec::with_capacity(b)).collect();

    for i in 0..(ell * b * b){
        let index = bucketing[i];
        buckets_index[index].push(i);
    }
    drop(bucketing);

    // Flatten buckets_index
    let mut buckets_index_flat: Vec<usize> = Vec::with_capacity(ell * b * b);
    for bucket in 0..(ell * b) {
        for k in 0..(b) {
            buckets_index_flat.push(buckets_index[bucket][k]);
        }
    }
    drop(buckets_index);

    {
        let mut d_to_open = Vec::with_capacity(ell * b * (b - 1));
        let mut e_to_open_tag = Vec::with_capacity(ell * b * (b - 1));
        
        for bucket in 0..(ell * b) {
            for k in 0..(b - 1) {
                let d = fcom_p.sub(a_i[buckets_index_flat[bucket*b + k + 1]], a_i[buckets_index_flat[bucket*b + 0]]);
                d_to_open.push(d);
                let e_mac = fcom_v.sub(b_i[buckets_index_flat[bucket*b + k + 1]], b_i[buckets_index_flat[bucket*b + 0]]);
                e_to_open_tag.push(e_mac);
            }
        }

        fcom_p.open(channel, &d_to_open).unwrap();
        channel.flush().unwrap();
        let mut e = Vec::new();
        fcom_v.open(channel, &e_to_open_tag, &mut e).unwrap();
        drop(e_to_open_tag);
        let d_opened_values = d_to_open.iter().map(|x| x.value()).collect::<Vec<_>>();
        drop(d_to_open);
        
        let mut f_value_to_open = Vec::with_capacity(ell * b * (b - 1));
        for bucket in 0..(ell * b) {
            for k in 0..(b - 1) {
                let e = e[bucket * (b - 1) + k];
                let d = d_opened_values[bucket * (b - 1) + k];

                let mut f_value = fcom_p.sub(c_i_c[buckets_index_flat[bucket*b + 0]], c_i_c[buckets_index_flat[bucket*b + k + 1]]);
                f_value = fcom_p.add(fcom_p.affine_mult_cst(e, a_i[buckets_index_flat[bucket*b + 0]]), f_value);
                f_value = fcom_p.affine_add_cst(d * e, f_value);
                f_value_to_open.push(f_value);
            }
        }
        fcom_p.open(channel, &f_value_to_open).unwrap();
        channel.flush().unwrap();
        let f_opened_values = f_value_to_open.iter().map(|x| x.value()).collect::<Vec<_>>();
        drop(f_value_to_open);

        let mut f_tag_to_open = Vec::with_capacity(ell * b * (b - 1));
        for bucket in 0..(ell * b) {
            for k in 0..(b - 1) {
                let d = d_opened_values[bucket * (b - 1) + k];
                let mut f_tag = fcom_v.sub(c_i_s[buckets_index_flat[bucket*b + 0]], c_i_s[buckets_index_flat[bucket*b + k + 1]]);
                f_tag = fcom_v.add(fcom_v.affine_mult_cst(d, b_i[buckets_index_flat[bucket*b + 0]]), f_tag);
                f_tag_to_open.push(f_tag);
            }
        }

        let mut f = Vec::with_capacity(f_tag_to_open.len());
        fcom_v.open(channel, &f_tag_to_open, &mut f).unwrap();

        for i in 0..(ell * b * (b - 1)) {
            assert_eq!(f[i] + f_opened_values[i], F::PrimeField::ZERO);
        }
        drop(f_tag_to_open);
    }

    let mut a_i_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        a_i_new.push(a_i[buckets_index_flat[bucket*b + 0]]);
    }
    drop(a_i);
    let a_i = a_i_new;

    let mut b_i_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        b_i_new.push(b_i[buckets_index_flat[bucket*b + 0]]);
    }
    drop(b_i);
    let b_i = b_i_new;

    let mut c_i_c_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        c_i_c_new.push(c_i_c[buckets_index_flat[bucket*b + 0]]);
    }
    drop(c_i_c);
    let c_i_c = c_i_c_new;

    let mut c_i_s_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        c_i_s_new.push(c_i_s[buckets_index_flat[bucket*b + 0]]);
    }
    drop(c_i_s);
    let c_i_s = c_i_s_new;
    drop(buckets_index_flat);

    // Step 3
    let mut bucketing = Vec::with_capacity(ell * b);
    for _ in 0..b {
        for j in 0..ell {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);
    
    let mut b_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    for i in 0..(ell * b) {
        let index = bucketing[i];
        b_buckets[index].push(b_i[i]);
    }
    drop(b_i);

    let mut d_to_open_tag = Vec::with_capacity(ell * (b - 1));

    let mut b_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(b - 1) {
            let d_tag = fcom_v.add(b_buckets[bucket][k + 1], b_buckets[bucket][0]);
            d_to_open_tag.push(d_tag);
        }
        b_out.push(b_buckets[bucket][0]);
    }
    drop(b_buckets);
    let mut d = Vec::new();
    fcom_v.open(channel, &d_to_open_tag, &mut d).unwrap();

    let mut c_s_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    for i in 0..(ell * b) {
        let index = bucketing[i];
        c_s_buckets[index].push(c_i_s[i]);
    }
    drop(c_i_s);

    let mut c_s_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(b - 1) {
            let c_s_prime = fcom_v.sub(c_s_buckets[bucket][0], c_s_buckets[bucket][k+1]);
            c_s_buckets[bucket][0] = c_s_prime;
        }
        c_s_out.push(c_s_buckets[bucket][0]);
    }
    drop(c_s_buckets);

    let mut a_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    for i in 0..(ell * b) {
        let index = bucketing[i];
        a_buckets[index].push(a_i[i]);
    }
    drop(a_i);

    let mut c_c_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    for i in 0..(ell * b) {
        let index = bucketing[i];
        c_c_buckets[index].push(c_i_c[i]);
    }
    drop(c_i_c);

    for bucket in 0..ell {
        for k in 0..(b - 1) {
            let d_value = d[bucket * (b - 1) + k];
            let mut c_prime = fcom_p.affine_mult_cst(d_value, a_buckets[bucket][k + 1]);
            c_prime = fcom_p.add(c_prime, c_c_buckets[bucket][0]);
            c_prime = fcom_p.sub(c_prime, c_c_buckets[bucket][k + 1]);

            let a_prime = fcom_p.add(a_buckets[bucket][k + 1], a_buckets[bucket][0]);

            a_buckets[bucket][0] = a_prime;
            c_c_buckets[bucket][0] = c_prime;
        }
    }

    let mut triples = Vec::with_capacity(ell);
    for i in 0..ell {
        let a = a_buckets[i][0];
        let b = b_out[i];
        let c_c = c_c_buckets[i][0];
        let c_s = c_s_out[i];
        let triple_a = OPRFSharing {
            0: a.value(),
            1: a,
            2: Default::default(),
        };
        let triple_b = OPRFSharing {
            0: Default::default(),
            1: Default::default(),
            2: b,
        };
        let triple_c = OPRFSharing {
            0: c_c.value(),
            1: c_c,
            2: c_s,
        };
        triples.push((triple_a, triple_b, triple_c));
    }
    return triples;
}


pub fn triple_server<F: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    parameters: (usize, usize, usize),
    fcom_p: &mut FComProver<F>,
    fcom_v: &mut FComVerifier<F>,
    channel: &mut C,
    rng: &mut RNG,
) -> Vec<(OPRFSharing<F>, OPRFSharing<F>, OPRFSharing<F>)> {
    let (ell, b, c) = parameters;
    let m = b * b * ell + c;

    // Step 1
    let mut a_i = Vec::with_capacity(m);
    let mut b_i = Vec::with_capacity(m);
    let mut c_i_s = Vec::with_capacity(m);

    let mut delta_i = Vec::with_capacity(m);
    let mut b_i_value = Vec::with_capacity(m);
    let mut c_i_value = Vec::with_capacity(m);

    for _ in 0..m {
        let com = fcom_v.random(channel, rng).unwrap();
        a_i.push(com);

        let m_0 = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&(com.mac()).to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
                .unwrap()
                .into();
            F::PrimeField::from_uniform_bytes(&bytes)
        };
        let m_1 = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&(com.mac() + fcom_v.get_delta()).to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
                .unwrap()
                .into();
            F::PrimeField::from_uniform_bytes(&bytes)
        };
        let m_2 = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&(com.mac() + fcom_v.get_delta() + fcom_v.get_delta()).to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
                .unwrap()
                .into();
            F::PrimeField::from_uniform_bytes(&bytes)
        };
        let bi = m_1 + m_1 + m_2;
        let ci = -m_0;
        let deltai = m_0 + m_1 + m_2;

        delta_i.push(deltai);
        b_i_value.push(bi);
        c_i_value.push(ci);
    }

    channel.write_serializable_seq(&delta_i).unwrap();
    channel.flush().unwrap();

    let mut c_i_c = fcom_v.input(channel, rng, m).unwrap();

    let com_c_mac = fcom_p.input(channel, rng, &c_i_value).unwrap();
    let com_b_mac = fcom_p.input(channel, rng, &b_i_value).unwrap();
    channel.flush().unwrap();

    for i in 0..m {
        let com_c = MacProver::<F>::new(c_i_value[i], com_c_mac[i]);
        let com_b = MacProver::<F>::new(b_i_value[i], com_b_mac[i]);
        b_i.push(com_b);
        c_i_s.push(com_c);
    }

    drop(delta_i);
    drop(com_c_mac);
    drop(com_b_mac);
    drop(c_i_value);
    drop(b_i_value);

    // Step 2
    // TODO This seed is not safe!!!
    let seed = rng.gen::<Block>();
    channel.write_block(&seed).unwrap();
    channel.flush().unwrap();
    let mut seed_rng = AesRng::from_seed(seed);
    let mut s: Vec<u8> = Vec::with_capacity(m);
    for _ in 0..(m - c) {
        s.push(0);
    }
    for _ in 0..c {
        s.push(1);
    }
    s.shuffle(&mut seed_rng);

    let mut a_i_to_open = Vec::with_capacity(c);
    let mut b_i_to_open = Vec::with_capacity(c);
    let mut c_i_c_to_open = Vec::with_capacity(c);
    let mut c_i_s_to_open = Vec::with_capacity(c);

    for i in 0..m {
        if s[i] == 1 {
            a_i_to_open.push(a_i[i]);
            b_i_to_open.push(b_i[i]);
            c_i_c_to_open.push(c_i_c[i]);
            c_i_s_to_open.push(c_i_s[i]);
        }
    }
    let mut a_opened = Vec::with_capacity(c);
    fcom_v.open(channel, &a_i_to_open, &mut a_opened).unwrap();
    fcom_p.open(channel, &b_i_to_open).unwrap();
    let mut c_i_c_opened = Vec::with_capacity(c);
    fcom_v
        .open(channel, &c_i_c_to_open, &mut c_i_c_opened)
        .unwrap();
    fcom_p.open(channel, &c_i_s_to_open).unwrap();
    channel.flush().unwrap();

    for i in 0..c {
        let lhs = a_opened[i] * b_i_to_open[i].value();
        let rhs = c_i_s_to_open[i].value() + c_i_c_opened[i];
        assert_eq!(lhs, rhs);
    }

    for i in (0..m).rev() {
        if s[i] == 1 {
            a_i.remove(i);
            b_i.remove(i);
            c_i_c.remove(i);
            c_i_s.remove(i);
        }
    }
    drop(s);

    let mut bucketing = Vec::with_capacity(ell * b * b);
    for _ in 0..b {
        for j in 0..(ell * b) {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);


    let mut buckets_index: Vec<Vec<usize>> = (0..ell*b).map(|_| Vec::with_capacity(b)).collect();

    for i in 0..(ell * b * b) {
        let index = bucketing[i];
        buckets_index[index].push(i);
    }
    drop(bucketing);

    // Flatten buckets_index
    let mut buckets_index_flat: Vec<usize> = Vec::with_capacity(ell * b * b);
    for bucket in 0..(ell * b) {
        for k in 0..(b) {
            buckets_index_flat.push(buckets_index[bucket][k]);
        }
    }
    drop(buckets_index);

    let mut d_to_open_tag = Vec::with_capacity(ell * b * (b - 1));
    let mut e_to_open = Vec::with_capacity(ell * b * (b - 1));

    for bucket in 0..(ell * b) {
        for k in 0..(b - 1) {
            let d_mac = fcom_v.sub(a_i[buckets_index_flat[bucket*b +k + 1]], a_i[buckets_index_flat[bucket*b + 0]]);
            d_to_open_tag.push(d_mac);
            let e = fcom_p.sub(b_i[buckets_index_flat[bucket*b +k + 1]], b_i[buckets_index_flat[bucket*b + 0]]);
            e_to_open.push(e);
        }
    }

    let mut d = Vec::new();
    fcom_v.open(channel, &d_to_open_tag, &mut d).unwrap();
    drop(d_to_open_tag);
    fcom_p.open(channel, &e_to_open).unwrap();
    channel.flush().unwrap();

    let mut f_tag_to_open = Vec::with_capacity(ell * b * (b - 1));
    for bucket in 0..(ell * b) {
        for k in 0..(b - 1) {
            let e = e_to_open[bucket * (b - 1) + k].value();
            let d = d[bucket * (b - 1) + k];

            let mut f_tag = fcom_v.sub(c_i_c[buckets_index_flat[bucket*b + 0]], c_i_c[buckets_index_flat[bucket*b +k + 1]]);
            f_tag = fcom_v.add(fcom_v.affine_mult_cst(e, a_i[buckets_index_flat[bucket*b + 0]]), f_tag);
            f_tag = fcom_v.affine_add_cst(d * e, f_tag);
            f_tag_to_open.push(f_tag);
        }
    }
    let mut f = Vec::with_capacity(f_tag_to_open.len());
    fcom_v.open(channel, &f_tag_to_open, &mut f).unwrap();
    drop(f_tag_to_open);
    drop(e_to_open);

    let mut f_value_to_open = Vec::with_capacity(ell * b * (b - 1));
    for bucket in 0..(ell * b) {
        for k in 0..(b - 1) {
            let d = d[bucket * (b - 1) + k];
            let mut f_value = fcom_p.sub(c_i_s[buckets_index_flat[bucket*b + 0]], c_i_s[buckets_index_flat[bucket*b +k + 1]]);
            f_value = fcom_p.add(fcom_p.affine_mult_cst(d, b_i[buckets_index_flat[bucket*b + 0]]), f_value);
            //f_value = fcom_p.affine_add_cst(d[0]*e.value(), f_value);
            f_value_to_open.push(f_value);
        }
    }

    
    fcom_p.open(channel, &f_value_to_open).unwrap();
    channel.flush().unwrap();

    for i in 0..(ell * b * (b - 1)) {
        assert_eq!(f[i] + f_value_to_open[i].value(), F::PrimeField::ZERO);
    }

    drop(f_value_to_open);

    let mut a_i_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        a_i_new.push(a_i[buckets_index_flat[bucket*b + 0]]);
    }
    drop(a_i);
    let a_i = a_i_new;

    let mut b_i_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        b_i_new.push(b_i[buckets_index_flat[bucket*b + 0]]);
    }
    drop(b_i);
    let b_i = b_i_new;

    let mut c_i_c_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        c_i_c_new.push(c_i_c[buckets_index_flat[bucket*b + 0]]);
    }
    drop(c_i_c);
    let c_i_c = c_i_c_new;

    let mut c_i_s_new = Vec::with_capacity(b * ell);
    for bucket in 0..(ell * b) {
        c_i_s_new.push(c_i_s[buckets_index_flat[bucket*b + 0]]);
    }
    drop(c_i_s);
    let c_i_s = c_i_s_new;

    // Step 3
    let mut bucketing = Vec::with_capacity(ell * b);
    for _ in 0..b {
        for j in 0..ell {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);
    let mut b_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    for i in 0..(ell * b) {
        let index = bucketing[i];
        b_buckets[index].push(b_i[i]);
    }
    drop(b_i);
    

    let mut d_to_open = Vec::with_capacity(ell * (b - 1));

    let mut b_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(b - 1) {
            let d_value = fcom_p.add(b_buckets[bucket][k + 1], b_buckets[bucket][0]);
            d_to_open.push(d_value);
        }
        b_out.push(b_buckets[bucket][0]);
    }
    drop(b_buckets);
    fcom_p.open(channel, &d_to_open).unwrap();
    channel.flush().unwrap();
    
    
    let mut c_s_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    for i in 0..(ell * b) {
        let index = bucketing[i];
        c_s_buckets[index].push(c_i_s[i]);
    }
    drop(c_i_s);

    let mut c_s_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(b - 1) {
            let c_prime = fcom_p.sub(c_s_buckets[bucket][0], c_s_buckets[bucket][k + 1]);
            c_s_buckets[bucket][0] = c_prime;
        }
        c_s_out.push(c_s_buckets[bucket][0]);
    }
    drop(c_s_buckets);

    let mut a_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();
    let mut c_c_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(b)).collect();

    for i in 0..(ell * b) {
        let index = bucketing[i];
        a_buckets[index].push(a_i[i]);
        c_c_buckets[index].push(c_i_c[i]);
    }
    drop(a_i);
    drop(c_i_c);

    for bucket in 0..ell {
        for k in 0..(b - 1) {
            let d_value = d_to_open[bucket * (b - 1) + k].value();
            let a_prime = fcom_v.add(a_buckets[bucket][k + 1], a_buckets[bucket][0]);
            let mut c_c_prime = fcom_v.affine_mult_cst(d_value, a_buckets[bucket][k + 1]);
            c_c_prime = fcom_v.add(c_c_prime, c_c_buckets[bucket][0]);
            c_c_prime = fcom_v.sub(c_c_prime, c_c_buckets[bucket][k + 1]);

            a_buckets[bucket][0] = a_prime;
            c_c_buckets[bucket][0] = c_c_prime;
        }
    }

    let mut triples = Vec::with_capacity(ell);
    for i in 0..ell {
        let a = a_buckets[i][0];
        let b = b_out[i];
        let c_c = c_c_buckets[i][0];
        let c_s = c_s_out[i];
        let triple_a = OPRFSharing {
            0: Default::default(),
            1: Default::default(),
            2: a,
        };
        let triple_b = OPRFSharing {
            0: b.value(),
            1: b,
            2: Default::default(),
        };
        let triple_c = OPRFSharing {
            0: c_s.value(),
            1: c_s,
            2: c_c,
        };
        triples.push((triple_a, triple_b, triple_c));
    }
    return triples;
}

#[cfg(test)]
mod test{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    use ocelot::svole::wykw::choose_lpn_parameters;
    use scuttlebutt::{field::{F64t, F3}, Channel};

    use super::*;

    #[test]
    fn triple_test() {
        let (client, server) = UnixStream::pair().unwrap();
        let ell = 4;
        let param = (ell, 2, 3);
        let (lpn_setup_params, lpn_extend_params) =
            choose_lpn_parameters::<F3>(param.0 * param.1 + param.2 / 2);
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom_p = FComProver::<F64t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let mut fcom_v = FComVerifier::<F64t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let triples = triple_client(param, &mut fcom_p, &mut fcom_v, &mut channel, &mut rng);
            return (triples, fcom_v.get_delta());
        });
        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom_v =
            FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let mut fcom_p =
            FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let triples_s = triple_server(param, &mut fcom_p, &mut fcom_v, &mut channel, &mut rng);

        let (triples_c, delta_c) = handle.join().unwrap();

        for i in 0..ell {
            let (_, triple_b, triple_c) = &triples_s[i];
            let (triple_a_c, _, triple_c_c) = &triples_c[i];
            assert_eq!((triple_a_c.0 * triple_b.0), (triple_c.0 + triple_c_c.0));
        }

        for i in 0..ell{
            let (triple_a, triple_b, triple_c) = &triples_s[i];
            let (triple_a_c, triple_b_c, triple_c_c) = &triples_c[i];
            assert_eq!(triple_a.2.mac(), -triple_a_c.0*fcom_v.get_delta() + triple_a_c.1.mac(), "Client A not authenticated at index {i}");
           
            assert_eq!(triple_b_c.2.mac(), - triple_b.0*delta_c + triple_b.1.mac(), "Server B not authenticated at index {i}");
           
            assert_eq!(triple_c.2.mac(), -triple_c_c.0*fcom_v.get_delta() + triple_c_c.1.mac(), "Client C not authenticated at index {i}");
           
            assert_eq!(triple_c_c.2.mac(), -triple_c.0*delta_c + triple_c.1.mac(), "Server C not authenticated at index {i}");
        }
    }
}