use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use rand::{seq::SliceRandom, CryptoRng, Rng, SeedableRng};
use scuttlebutt::{field::FiniteField, ring::FiniteRing, AbstractChannel, AesRng, Block};

use crate::dabits::OPRFSharing;



pub fn triple_client_half_auth<F: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    parameters: (usize, usize, usize),
    fcom_p: &mut FComProver<F>,
    fcom_v: &mut FComVerifier<F>,
    channel: &mut C,
    rng: &mut RNG,
) -> Vec<(OPRFSharing<F>, OPRFSharing<F>, OPRFSharing<F>)>{
    let (ell, bucket_b, c) = parameters;
    let m = bucket_b * bucket_b * ell + c;

    let mut a = Vec::with_capacity(m);
    for _ in 0..m {
        let com = fcom_p.random(channel, rng).unwrap();
        a.push(com);
    }

    let delta = channel.read_serializable_seq::<F::PrimeField>(m).unwrap();

    let mut c_0 = Vec::with_capacity(m);
    for i in 0..m {
        let m_a_i = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&a[i].mac().to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
                .unwrap()
                .into();
            F::PrimeField::from_uniform_bytes(&bytes)
        };
        let ci = m_a_i + delta[i] * a[i].value() * a[i].value();
        c_0.push(ci);
    }
    drop(delta);

    let mut b = fcom_v.input(channel, rng, m).unwrap();
    let mut c_1 = fcom_v.input(channel, rng, m).unwrap();

    let seed = rng.gen::<Block>();
    let mut seed_rng = AesRng::from_seed(seed);
    channel.write_block(&seed).unwrap();
    channel.flush().unwrap();


    // Sacrifice step
    let mut s = Vec::with_capacity(m);
    for _ in 0..(m - c) {
        s.push(0);
    }
    for _ in 0..c {
        s.push(1);
    }
    s.shuffle(&mut seed_rng);

    let mut a_local = Vec::with_capacity(c);
    let mut c_0_local = Vec::with_capacity(c);
    let mut b_to_open = Vec::with_capacity(c);
    let mut c_1_to_open = Vec::with_capacity(c);

    for i in 0..m{
        if s[i] == 1{
            a_local.push(a[i]);
            c_0_local.push(c_0[i]);
            b_to_open.push(b[i]);
            c_1_to_open.push(c_1[i]);
        }
    }

    let mut b_opened = Vec::with_capacity(c);
    fcom_v.open(channel, &b_to_open, &mut b_opened).unwrap();

    let mut c_1_opened = Vec::with_capacity(c);
    fcom_v.open(channel, &c_1_to_open, &mut c_1_opened).unwrap();

    for i in 0..c{
        assert_eq!(a_local[i].value() * b_opened[i], c_0_local[i] + c_1_opened[i]);
    }
    for i in (0..m).rev() {
        if s[i] == 1 {
            a.remove(i);
            b.remove(i);
            c_0.remove(i);
            c_1.remove(i);
        }
    }

    // Consistency bucketing
    let mut bucketing = Vec::with_capacity(ell * bucket_b * bucket_b);
    for _ in 0..bucket_b {
        for j in 0..(ell * bucket_b) {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);

    let mut buckets_index: Vec<Vec<usize>> = (0..ell*bucket_b).map(|_| Vec::with_capacity(bucket_b)).collect();

    for i in 0..(ell * bucket_b * bucket_b){
        let index = bucketing[i];
        buckets_index[index].push(i);
    }
    drop(bucketing);

    // Flatten buckets_index
    let mut buckets_index_flat: Vec<usize> = Vec::with_capacity(ell * bucket_b * bucket_b);
    for bucket in 0..(ell * bucket_b) {
        for k in 0..(bucket_b) {
            buckets_index_flat.push(buckets_index[bucket][k]);
        }
    }
    drop(buckets_index);
    {
        let mut e_to_open = Vec::with_capacity(ell * bucket_b * (bucket_b-1));
        let mut d_to_open = Vec::with_capacity(ell * bucket_b * (bucket_b-1));

        for bucket in 0..(ell * bucket_b) {
            for k in 0..(bucket_b - 1) {
                let d = fcom_p.sub(a[buckets_index_flat[bucket*bucket_b + k + 1]], a[buckets_index_flat[bucket*bucket_b + 0]]);
                d_to_open.push(d);
                let e_mac = fcom_v.sub(b[buckets_index_flat[bucket*bucket_b + k + 1]], b[buckets_index_flat[bucket*bucket_b + 0]]);
                e_to_open.push(e_mac);
            }
        }
        fcom_p.open(channel, &d_to_open).unwrap();
        let mut e = Vec::with_capacity(ell * bucket_b * (bucket_b-1));
        fcom_v.open(channel, &e_to_open, &mut e).unwrap();
        drop(e_to_open);

        let d = d_to_open.iter().map(|x| x.value()).collect::<Vec<_>>();
        drop(d_to_open);

        let mut f_to_open = Vec::with_capacity(ell * bucket_b * (bucket_b-1));
        for bucket in 0..(ell * bucket_b) {
            for k in 0..(bucket_b - 1) {
                let d = d[bucket * (bucket_b - 1) + k];
                let mut f_tag = fcom_v.sub(c_1[buckets_index_flat[bucket*bucket_b + 0]], c_1[buckets_index_flat[bucket*bucket_b + k + 1]]);
                f_tag = fcom_v.add(fcom_v.affine_mult_cst(d, b[buckets_index_flat[bucket*bucket_b + 0]]), f_tag);
                f_to_open.push(f_tag);
            }
        }
        let mut f = Vec::with_capacity(f_to_open.len());
        fcom_v.open(channel, &f_to_open, &mut f).unwrap();

        let mut f_local = Vec::with_capacity(ell * bucket_b * (bucket_b - 1));
        for bucket in 0..(ell * bucket_b) {
            for k in 0..(bucket_b - 1) {
                let e = e[bucket * (bucket_b - 1) + k];
                let d = d[bucket * (bucket_b - 1) + k];

                let mut f_value = c_0[buckets_index_flat[bucket*bucket_b + 0]]- c_0[buckets_index_flat[bucket*bucket_b + k + 1]];
                f_value += e * a[buckets_index_flat[bucket*bucket_b + 0]].value();
                f_value += d*e;
                f_local.push(f_value);
            }
        }

        for i in 0..(ell * bucket_b * (bucket_b - 1)) {
            assert_eq!(f[i] + f_local[i], F::PrimeField::ZERO);
        }
    }

    // Remove leakage buckets
    let mut a_i_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        a_i_new.push(a[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(a);
    let a = a_i_new;

    let mut b_i_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        b_i_new.push(b[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(b);
    let b = b_i_new;

    let mut c_i_c_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        c_i_c_new.push(c_0[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(c_0);
    let c_0 = c_i_c_new;

    let mut c_i_s_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        c_i_s_new.push(c_1[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(c_1);
    let c_1 = c_i_s_new;
    drop(buckets_index_flat);

    let mut bucketing = Vec::with_capacity(ell * bucket_b);
    for _ in 0..bucket_b {
        for j in 0..ell {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);
    
    let mut b_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        b_buckets[index].push(b[i]);
    }
    drop(b);
    
    let mut d_to_open_tag = Vec::with_capacity(ell * (bucket_b - 1));
    let mut b_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(bucket_b - 1) {
            let d_tag = fcom_v.add(b_buckets[bucket][k + 1], b_buckets[bucket][0]);
            d_to_open_tag.push(d_tag);
        }
        b_out.push(b_buckets[bucket][0]);
    }
    drop(b_buckets);
    let mut d = Vec::new();
    fcom_v.open(channel, &d_to_open_tag, &mut d).unwrap();

    let mut c_1_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        c_1_buckets[index].push(c_1[i]);
    }
    drop(c_1);
    let mut c_1_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(bucket_b - 1) {
            let c_s_prime = fcom_v.sub(c_1_buckets[bucket][0], c_1_buckets[bucket][k+1]);
            c_1_buckets[bucket][0] = c_s_prime;
        }
        c_1_out.push(c_1_buckets[bucket][0]);
    }
    drop(c_1_buckets);

    let mut a_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        a_buckets[index].push(a[i]);
    }
    drop(a);

    let mut c_0_buckets: Vec<Vec<F::PrimeField>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        c_0_buckets[index].push(c_0[i]);
    }
    drop(c_0);

    for bucket in 0..ell {
        for k in 0..(bucket_b - 1) {
            let d_value = d[bucket * (bucket_b - 1) + k];
            let mut c_prime = d_value* a_buckets[bucket][k + 1].value();
            c_prime += c_0_buckets[bucket][0];
            c_prime -=  c_0_buckets[bucket][k + 1];

            let a_prime = fcom_p.add(a_buckets[bucket][k + 1], a_buckets[bucket][0]);

            a_buckets[bucket][0] = a_prime;
            c_0_buckets[bucket][0] = c_prime;
        }
    }

    let mut triples = Vec::with_capacity(ell);
    for i in 0..ell {
        let a = a_buckets[i][0];
        let b = b_out[i];
        let c_c = c_0_buckets[i][0];
        let c_s = c_1_out[i];
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
            0: c_c,
            1: MacProver::new(c_c, F::ZERO),
            2: c_s,
        };
        triples.push((triple_a, triple_b, triple_c));
    }
    return triples;
}

pub fn triple_server_half_auth<F: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    parameters: (usize, usize, usize),
    fcom_p: &mut FComProver<F>,
    fcom_v: &mut FComVerifier<F>,
    channel: &mut C,
    rng: &mut RNG,
) -> Vec<(OPRFSharing<F>, OPRFSharing<F>, OPRFSharing<F>)>{
    let (ell, bucket_b, c) = parameters;
    let m = bucket_b * bucket_b * ell + c;

    
    let mut a = Vec::with_capacity(m);
    let mut delta = Vec::with_capacity(m);
    let mut b = Vec::with_capacity(m);
    let mut c_1 = Vec::with_capacity(m);

    let mut b_value = Vec::with_capacity(m);
    let mut c_1_value = Vec::with_capacity(m);

    for _ in 0..m {
        let com = fcom_v.random(channel, rng).unwrap();
        a.push(com);

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

        delta.push(deltai);
        b_value.push(bi);
        c_1_value.push(ci);
    }

    channel.write_serializable_seq(&delta).unwrap();
    
    let b_mac = fcom_p.input(channel, rng, &b_value).unwrap();
    let c_1_mac = fcom_p.input(channel, rng, &c_1_value).unwrap();
    channel.flush().unwrap();
    
    for i in 0..m {
        let com_c = MacProver::<F>::new(c_1_value[i], c_1_mac[i]);
        let com_b = MacProver::<F>::new(b_value[i], b_mac[i]);
        b.push(com_b);
        c_1.push(com_c);
    }

    let seed = channel.read_block().unwrap();
    let mut seed_rng = AesRng::from_seed(seed);


    // Sacrifice step
    let mut s = Vec::with_capacity(m);
    for _ in 0..(m - c) {
        s.push(0);
    }
    for _ in 0..c {
        s.push(1);
    }
    s.shuffle(&mut seed_rng);

    let mut a_local = Vec::with_capacity(c);
    let mut b_to_open = Vec::with_capacity(c);
    let mut c_1_to_open = Vec::with_capacity(c);

    for i in 0..m{
        if s[i] == 1{
            a_local.push(a[i]);
            b_to_open.push(b[i]);
            c_1_to_open.push(c_1[i]);
        }
    }

    fcom_p.open(channel, &b_to_open).unwrap();
    fcom_p.open(channel, &c_1_to_open).unwrap();

    for i in (0..m).rev() {
        if s[i] == 1 {
            a.remove(i);
            b.remove(i);
            c_1.remove(i);
        }
    }

    // Consistency bucketing
    let mut bucketing = Vec::with_capacity(ell * bucket_b * bucket_b);
    for _ in 0..bucket_b {
        for j in 0..(ell * bucket_b) {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);

    let mut buckets_index: Vec<Vec<usize>> = (0..ell*bucket_b).map(|_| Vec::with_capacity(bucket_b)).collect();

    for i in 0..(ell * bucket_b * bucket_b){
        let index = bucketing[i];
        buckets_index[index].push(i);
    }
    drop(bucketing);

    // Flatten buckets_index
    let mut buckets_index_flat: Vec<usize> = Vec::with_capacity(ell * bucket_b * bucket_b);
    for bucket in 0..(ell * bucket_b) {
        for k in 0..(bucket_b) {
            buckets_index_flat.push(buckets_index[bucket][k]);
        }
    }
    drop(buckets_index);
    {
        let mut e_to_open = Vec::with_capacity(ell * bucket_b * (bucket_b-1));
        let mut d_to_open = Vec::with_capacity(ell * bucket_b * (bucket_b-1));

        for bucket in 0..(ell * bucket_b) {
            for k in 0..(bucket_b - 1) {
                let d = fcom_v.sub(a[buckets_index_flat[bucket*bucket_b + k + 1]], a[buckets_index_flat[bucket*bucket_b + 0]]);
                d_to_open.push(d);
                let e_mac = fcom_p.sub(b[buckets_index_flat[bucket*bucket_b + k + 1]], b[buckets_index_flat[bucket*bucket_b + 0]]);
                e_to_open.push(e_mac);
            }
        }
        let mut d = Vec::with_capacity(ell * bucket_b * (bucket_b-1));
        fcom_v.open(channel, &d_to_open, &mut d).unwrap();
        drop(d_to_open);
        
        fcom_p.open(channel, &e_to_open).unwrap();
        drop(e_to_open);

        let mut f_to_open = Vec::with_capacity(ell * bucket_b * (bucket_b-1));
        for bucket in 0..(ell * bucket_b) {
            for k in 0..(bucket_b - 1) {
                let d = d[bucket * (bucket_b - 1) + k];
                let mut f_tag = fcom_p.sub(c_1[buckets_index_flat[bucket*bucket_b + 0]], c_1[buckets_index_flat[bucket*bucket_b + k + 1]]);
                f_tag = fcom_p.add(fcom_p.affine_mult_cst(d, b[buckets_index_flat[bucket*bucket_b + 0]]), f_tag);
                f_to_open.push(f_tag);
            }
        }
        fcom_p.open(channel, &f_to_open).unwrap();
    }

    // Remove leakage buckets
    let mut a_i_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        a_i_new.push(a[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(a);
    let a = a_i_new;

    let mut b_i_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        b_i_new.push(b[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(b);
    let b = b_i_new;

    let mut c_i_s_new = Vec::with_capacity(bucket_b * ell);
    for bucket in 0..(ell * bucket_b) {
        c_i_s_new.push(c_1[buckets_index_flat[bucket*bucket_b + 0]]);
    }
    drop(c_1);
    let c_1 = c_i_s_new;
    drop(buckets_index_flat);

    let mut bucketing = Vec::with_capacity(ell * bucket_b);
    for _ in 0..bucket_b {
        for j in 0..ell {
            bucketing.push(j);
        }
    }
    bucketing.shuffle(&mut seed_rng);
    
    let mut b_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        b_buckets[index].push(b[i]);
    }
    drop(b);
    
    let mut d_to_open_tag = Vec::with_capacity(ell * (bucket_b - 1));
    let mut b_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(bucket_b - 1) {
            let d_tag = fcom_p.add(b_buckets[bucket][k + 1], b_buckets[bucket][0]);
            d_to_open_tag.push(d_tag);
        }
        b_out.push(b_buckets[bucket][0]);
    }
    drop(b_buckets);
    fcom_p.open(channel, &d_to_open_tag).unwrap();

    let mut c_1_buckets: Vec<Vec<MacProver<F>>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        c_1_buckets[index].push(c_1[i]);
    }
    drop(c_1);
    let mut c_1_out = Vec::with_capacity(ell);
    for bucket in 0..ell {
        for k in 0..(bucket_b - 1) {
            let c_s_prime = fcom_p.sub(c_1_buckets[bucket][0], c_1_buckets[bucket][k+1]);
            c_1_buckets[bucket][0] = c_s_prime;
        }
        c_1_out.push(c_1_buckets[bucket][0]);
    }
    drop(c_1_buckets);

    let mut a_buckets: Vec<Vec<MacVerifier<F>>> = (0..ell).map(|_| Vec::with_capacity(bucket_b)).collect();
    for i in 0..(ell * bucket_b) {
        let index = bucketing[i];
        a_buckets[index].push(a[i]);
    }
    drop(a);

    for bucket in 0..ell {
        for k in 0..(bucket_b - 1) {
            let a_prime = fcom_v.add(a_buckets[bucket][k + 1], a_buckets[bucket][0]);
            a_buckets[bucket][0] = a_prime;
        }
    }

    let mut triples = Vec::with_capacity(ell);
    for i in 0..ell {
        let a = a_buckets[i][0];
        let b = b_out[i];
        let c_s = c_1_out[i];
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
            2: Default::default(),
        };
        triples.push((triple_a, triple_b, triple_c));
    }
    return triples;
}


#[cfg(test)]
mod test{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    use ocelot::svole::wykw::choose_lpn_parameters;
    use scuttlebutt::{field::F82t, Channel};

    use super::*;

    #[test]
    fn triple_test() {
        let (client, server) = UnixStream::pair().unwrap();
        let ell = 1000;
        let param = (ell, 3, 3);
        let (lpn_setup_params, lpn_extend_params) =
            choose_lpn_parameters::<<F82t as FiniteField>::PrimeField>(param.0 * param.1 + param.2 / 2);
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom_p = FComProver::<F82t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let mut fcom_v = FComVerifier::<F82t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let triples = triple_client_half_auth(param, &mut fcom_p, &mut fcom_v, &mut channel, &mut rng);
            return (triples, fcom_v.get_delta());
        });
        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom_v =
            FComVerifier::<F82t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let mut fcom_p =
            FComProver::<F82t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let triples_s = triple_server_half_auth(param, &mut fcom_p, &mut fcom_v, &mut channel, &mut rng);

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
           
            assert_eq!(triple_c_c.2.mac(), -triple_c.0*delta_c + triple_c.1.mac(), "Server C not authenticated at index {i}");
        }
    }
}