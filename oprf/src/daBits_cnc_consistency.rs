use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use rand::{seq::SliceRandom, CryptoRng, Rng, SeedableRng};
use scuttlebutt::{
    field::FiniteField,
    AbstractChannel, AesRng, Block,
};

pub fn get_bucket_size(batch_size: usize) -> usize{
    // TODO add for more sizes
    if batch_size < 1<<9{
        return 6
    }
    return 5;
}
pub fn candidate_client<F: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    parameters: (usize, usize, usize),
    fcom2: &mut FComProver<F>,
    fcom3: &mut FComProver<Fp>,
    channel: &mut C,
    rng: &mut RNG,
) -> (Vec<MacProver<F>>, Vec<MacProver<Fp>>) 
where u8: From<<F as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>{
    let (ell, b, c) = parameters;
    let m = b * ell + c;

    // Step 1 commit to m=b*ell + c candidates
    let mut v2 = Vec::with_capacity(m as usize);
    let mut v3 = Vec::with_capacity(m as usize);
    for _ in 0..m {
        let com2 = fcom2.random(channel, rng).unwrap();
        v2.push(com2);
    }
    let com2_values: Vec<Fp::PrimeField> = v2
        .iter()
        .map(|x| {
            let value = Fp::PrimeField::try_from(u8::from(x.value()));
            let value = match value {
                Ok(val) => val,
                Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
            };
            value
        })
        .collect();
    let com3_mac = fcom3.input(channel, rng, com2_values.as_slice()).unwrap();
    for i in 0..m {
        let com3 = MacProver::<Fp>::new(com2_values[i], com3_mac[i]);
        v3.push(com3);
    }
    let _ = channel.flush();

    // step 2 consistency check both ways

    // step 2.1 Open as subset S of size C
    let seed = channel.read_block().unwrap();
    let mut s = Vec::with_capacity(m as usize);
    for _ in 0..c {
        s.push(1);
    }
    for _ in 0..(m - c) {
        s.push(0);
    }
    let mut seed_rng = AesRng::from_seed(seed);
    s.shuffle(&mut seed_rng);

    let mut to_open = Vec::with_capacity(c as usize);
    let mut to_check = Vec::with_capacity(c as usize);
    for i in 0..m {
        let index = i as usize;
        if s[index] == 1 {
            to_open.push(v2[index].clone());
            to_check.push(v3[index].clone());
        }
    }
    for i in (0..m).rev() {
        if s[i] == 1 {
            v2.remove(i as usize);
            v3.remove(i as usize);
        }
    }

    let _ = fcom2.open(channel, &to_open);
    for i in 0..c {
        let value = Fp::PrimeField::try_from(u8::from(to_open[i as usize].value()));
        let value = match value {
            Ok(val) => val,
            Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
        };
        to_check[i as usize] = fcom3.affine_add_cst(-value, to_check[i as usize]);
    }
    let _ = fcom3.check_zero(channel, &to_check).unwrap();

    // step 2.2 Bucket intro ell buckets of size B
    let mut bucket = Vec::with_capacity((ell * b) as usize);
    for _ in 0..b {
        for j in 0..ell {
            bucket.push(j);
        }
    }
    let _ = channel.flush();

    let seed = channel.read_block().unwrap();
    let mut seed_rng = AesRng::from_seed(seed);
    bucket.shuffle(&mut seed_rng);

    let mut buckets2 = vec![vec![]; ell as usize];
    let mut buckets3 = vec![vec![]; ell as usize];

    for i in 0..(b * ell) {
        buckets2[bucket[i as usize] as usize].push(v2[i as usize].clone());
        buckets3[bucket[i as usize] as usize].push(v3[i as usize].clone());
    }

    let mut v2_out = Vec::with_capacity(ell as usize);
    let mut v3_out = Vec::with_capacity(ell as usize);

    let mut all_bk = Vec::with_capacity(ell * (b - 1) as usize);
    let mut all_ck_to_open = Vec::with_capacity(ell * (b - 1) as usize);
    for bucket in 0..ell {
        // step 2.2.1 Open c^k mod 2 = b^1 + b^k mod 2
        let mut ck_to_open = vec![Default::default(); (b - 1) as usize];
        for k in 0..(b - 1) {
            let ck = fcom2.add(
                buckets2[bucket as usize][0],
                buckets2[bucket as usize][k + 1 as usize],
            );
            ck_to_open[k as usize] = ck;
        }
        //let _ = fcom2.open(channel, &ck_to_open);
        for i in 0..(b - 1) {
            all_ck_to_open.push(ck_to_open[i as usize].clone());
        }
    }
    let _ = fcom2.open(channel, &all_ck_to_open);

    for bucket in 0..ell {
        // step 2.2.2 Compute \hat{b}^k mod 3 = b^1 + c^k + c^k * b^1 mod 3
        // step 2.2.3 Compute \tilde{b}^k - \hat{b}^k mod 3
        let mut bk = vec![Default::default(); (b - 1) as usize];
        let ck_to_open =
            &all_ck_to_open[(bucket * (b - 1)) as usize..((bucket + 1) * (b - 1)) as usize];
        for k in 0..(b - 1) {
            let ck = Fp::PrimeField::try_from(u8::from(ck_to_open[k as usize].value()));
            let ck = match ck {
                Ok(val) => val,
                Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
            };
            let b1 = buckets3[bucket as usize][0];
            let mut bk_hat = fcom3.affine_mult_cst(ck, b1);
            bk_hat = fcom3.affine_add_cst(ck, bk_hat);
            bk_hat = fcom3.add(bk_hat, b1);

            bk[k as usize] = fcom3.sub(buckets3[bucket as usize][k + 1 as usize], bk_hat);
        }
        for i in 0..(b - 1) {
            all_bk.push(bk[i as usize].clone());
        }
        // step 2.2.4 ZK-verify step 2.2.3 equals zero
        v2_out.push(buckets2[bucket as usize][0].clone());
        v3_out.push(buckets3[bucket as usize][0].clone());
    }
    let _ = fcom3.check_zero(channel, &all_bk).unwrap();

    return (v2_out, v3_out);
}

pub fn candidate_server<F: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    parameters: (usize, usize, usize),
    fcom2: &mut FComVerifier<F>,
    fcom3: &mut FComVerifier<Fp>,
    channel: &mut C,
    rng: &mut RNG,
) -> (Vec<MacVerifier<F>>, Vec<MacVerifier<Fp>>)
where u8: From<<F as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8> {
    let (ell, b, c) = parameters;
    let m = b * ell + c;

    // Step 1 commit to m=b*ell + c candidates
    let mut v2 = Vec::with_capacity(m as usize);
    let mut v3 = Vec::with_capacity(m as usize);
    for _ in 0..m {
        let com2 = fcom2.random(channel, rng).unwrap();
        v2.push(com2);
    }
    let com3_mac = fcom3.input(channel, rng, m).unwrap();
    for i in 0..m {
        v3.push(com3_mac[i]);
    }
    // step 2 consistency check both ways

    // step 2.1 Open as subset S of size C
    let seed = rng.gen::<Block>();
    let _ = channel.write_block(&seed).unwrap();
    let _ = channel.flush();
    let mut s = Vec::with_capacity(m as usize);
    for _ in 0..c {
        s.push(1);
    }
    for _ in 0..(m - c) {
        s.push(0);
    }
    let mut seed_rng = AesRng::from_seed(seed);
    s.shuffle(&mut seed_rng);

    let mut to_open = Vec::with_capacity(c as usize);
    let mut to_check = Vec::with_capacity(c as usize);
    for i in 0..m {
        let index = i as usize;
        if s[index] == 1 {
            to_open.push(v2[index].clone());
            to_check.push(v3[index].clone());
        }
    }
    for i in (0..m).rev() {
        if s[i] == 1 {
            v2.remove(i as usize);
            v3.remove(i as usize);
        }
    }
    let mut openings = Vec::new();
    fcom2.open(channel, &to_open, &mut openings).unwrap();
    for i in 0..c {
        let value = Fp::PrimeField::try_from(u8::from(openings[i as usize]));
        let value = match value {
            Ok(val) => val,
            Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
        };
        to_check[i as usize] = fcom3.affine_add_cst(-value, to_check[i as usize]);
    }
    let _ = fcom3.check_zero(channel, rng, &to_check).unwrap();

    // step 2.2 Bucket intro ell buckets of size B
    let mut bucket = Vec::with_capacity((ell * b) as usize);
    for _ in 0..b {
        for j in 0..ell {
            bucket.push(j);
        }
    }
    let seed = rng.gen::<Block>();
    let _ = channel.write_block(&seed).unwrap();
    let _ = channel.flush();
    let mut seed_rng = AesRng::from_seed(seed);
    bucket.shuffle(&mut seed_rng);

    let mut buckets2 = vec![vec![]; ell as usize];
    let mut buckets3 = vec![vec![]; ell as usize];

    for i in 0..(b * ell) {
        buckets2[bucket[i as usize] as usize].push(v2[i as usize].clone());
        buckets3[bucket[i as usize] as usize].push(v3[i as usize].clone());
    }

    let mut v2_out = Vec::with_capacity(ell as usize);
    let mut v3_out = Vec::with_capacity(ell as usize);

    let mut all_bk = Vec::with_capacity(ell * (b - 1) as usize);
    let mut all_ck_to_open = Vec::with_capacity(ell * (b - 1) as usize);
    for bucket in 0..ell {
        // step 2.2.1 Open c^k mod 2 = b^1 + b^k mod 2
        let mut ck_to_open = vec![Default::default(); (b - 1) as usize];
        for k in 0..(b - 1) {
            let ck = fcom2.add(
                buckets2[bucket as usize][0],
                buckets2[bucket as usize][k + 1 as usize],
            );
            ck_to_open[k as usize] = ck;
        }
        for i in 0..(b - 1) {
            all_ck_to_open.push(ck_to_open[i as usize].clone());
        }
    }
    let mut openings = Vec::new();
    let _ = fcom2.open(channel, &all_ck_to_open, &mut openings).unwrap();

    for bucket in 0..ell {
        // step 2.2.2 Compute \hat{b}^k mod 3 = b^1 + c^k + c^k * b^1 mod 3
        // step 2.2.3 Compute \tilde{b}^k - \hat{b}^k mod 3
        let mut bk = vec![Default::default(); (b - 1) as usize];
        let openings_slice =
            &openings[(bucket * (b - 1)) as usize..((bucket + 1) * (b - 1)) as usize];
        for k in 0..(b - 1) {
            let ck= Fp::PrimeField::try_from(u8::from(openings_slice[k as usize]));
            let ck = match ck {
                Ok(val) => val,
                Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
            };
            let b1 = buckets3[bucket as usize][0];
            let mut bk_hat = fcom3.affine_mult_cst(ck, b1);
            bk_hat = fcom3.affine_add_cst(ck, bk_hat);
            bk_hat = fcom3.add(bk_hat, b1);

            bk[k as usize] = fcom3.sub(buckets3[bucket as usize][k + 1 as usize], bk_hat);
        }
        // step 2.2.4 ZK-verify step 2.2.3 equals zero
        for i in 0..(b - 1) {
            all_bk.push(bk[i as usize].clone());
        }
        v2_out.push(buckets2[bucket as usize][0].clone());
        v3_out.push(buckets3[bucket as usize][0].clone());
    }
    let _ = fcom3.check_zero(channel, rng, &all_bk).unwrap();
    return (v2_out, v3_out);
}

#[cfg(test)]
mod test{
    use super::*;
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    use ocelot::svole::wykw::choose_lpn_parameters;
    use scuttlebutt::{field::{F64b, F64t, F3}, Channel};

    #[test]
    fn cnc_dabit_test() {
        let (client, server) = UnixStream::pair().unwrap();
        let param = (4096, 2, 3);
        let (lpn_setup_params, lpn_extend_params) =
            choose_lpn_parameters::<F3>(param.0 * param.1 + param.2 / 2);
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom2 = FComProver::<F64b>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let mut fcom3 = FComProver::<F64t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let (v2, v3) = candidate_client(param, &mut fcom2, &mut fcom3, &mut channel, &mut rng);
            return (v2, v3);
        });
        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom2 =
            FComVerifier::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let mut fcom3 =
            FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let (s_2, s_3) = candidate_server(param, &mut fcom2, &mut fcom3, &mut channel, &mut rng);

        let (c2, c3) = handle.join().unwrap();
        for i in 0..(param.0) {
            let c_2: u8 = c2[i].value().into();
            let c_3: u8 = c3[i].value().into();
            assert_eq!(c_2, c_3);
        }

        for i in 0..param.0{
            assert_eq!(s_2[i].mac(), -c2[i].value()*fcom2.get_delta() + c2[i].mac());
            assert_eq!(s_3[i].mac(), -c3[i].value()*fcom3.get_delta() + c3[i].mac());
        }
    }
}