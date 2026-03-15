use hd_quicksilver::{hd_quicksilver::{HDMacProver, HDMacVerifier, QSStateProver, QSStateVerifier}, homcom::{FComProver, FComVerifier, MacProver, MacVerifier}};
use rand::{seq::SliceRandom, CryptoRng, Rng, SeedableRng};
use scuttlebutt::{
    field::{FiniteField, F2}, ring::FiniteRing, AbstractChannel, AesRng, Block
};


// We currently define the matrix P as
//     | 1 1 1 0 0 |
// P = | 1 0 0 1 0 | = [A I_3]
//     | 0 1 0 0 1 |
// As the parity check matrix for a linear code [5, 2, 3].
pub struct ParityCheckMatrix<F: FiniteField> {
    pub b: usize,
    pub n: usize,
    pub k: usize,
    pub zk_d: usize,
    pub matrix: Vec<Vec<F>>,
}

pub fn small_code() -> ParityCheckMatrix<F2> {
    ParityCheckMatrix {
        b: 6,
        n: 3,
        k: 3,
        zk_d: 3,
        matrix: vec![
            vec![F2::ONE, F2::ONE, F2::ZERO,    F2::ONE,  F2::ZERO, F2::ZERO],
            vec![F2::ONE, F2::ZERO, F2::ONE,    F2::ZERO, F2::ONE,  F2::ZERO],
            vec![F2::ZERO, F2::ONE, F2::ZERO,    F2::ZERO, F2::ZERO, F2::ONE],
        ],
    }
}

pub fn medium_code() -> ParityCheckMatrix<F2> {
    ParityCheckMatrix {
        b: 7,
        n: 3,
        k: 4,
        zk_d: 4,
        matrix: vec![
            vec![F2::ONE, F2::ONE, F2::ZERO, F2::ONE,   F2::ONE,  F2::ZERO, F2::ZERO],
            vec![F2::ONE, F2::ZERO, F2::ONE, F2::ONE,   F2::ZERO, F2::ONE,  F2::ZERO],
            vec![F2::ZERO, F2::ONE, F2::ONE, F2::ONE,   F2::ZERO, F2::ZERO, F2::ONE],
        ],
    }
}
    
pub fn large_cpde() -> ParityCheckMatrix<F2> {
    ParityCheckMatrix {
        b: 12,
        n: 5,
        k: 7,
        zk_d: 6,
        matrix: vec![
            vec![F2::ONE, F2::ONE, F2::ZERO, F2::ONE, F2::ONE, F2::ZERO, F2::ZERO,  F2::ONE, F2::ZERO, F2::ZERO, F2::ZERO, F2::ZERO,],
            vec![F2::ONE, F2::ZERO, F2::ONE, F2::ONE, F2::ZERO, F2::ONE, F2::ZERO,  F2::ZERO, F2::ONE, F2::ZERO, F2::ZERO, F2::ZERO,],
            vec![F2::ZERO, F2::ONE, F2::ONE, F2::ONE, F2::ZERO, F2::ZERO, F2::ONE,  F2::ZERO, F2::ZERO, F2::ONE, F2::ZERO, F2::ZERO,],
            vec![F2::ONE, F2::ONE, F2::ZERO, F2::ZERO, F2::ONE, F2::ONE, F2::ONE,   F2::ZERO, F2::ZERO, F2::ZERO, F2::ONE, F2::ZERO,],
            vec![F2::ONE, F2::ZERO, F2::ONE, F2::ZERO, F2::ONE, F2::ONE, F2::ONE,   F2::ZERO, F2::ZERO, F2::ZERO, F2::ZERO, F2::ONE,],
        ],
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodeType {
    Small,
    Medium,
    Large,
}

pub fn code_candidate_client<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    fcom2: &mut FComProver<Fb>,
    fcom3: &mut FComProver<Fp>,
    channel: &mut C,
    rng: &mut RNG,
    code: &CodeType,
) -> (Vec<MacProver<Fb>>, Vec<MacProver<Fp>>)
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{   
    let parity_check_matrix = match code {
        CodeType::Small => small_code(),
        CodeType::Medium => medium_code(),
        CodeType::Large => large_cpde(),
    };
    
    let k = parity_check_matrix.k;
    let b = parity_check_matrix.b;
    let c = 40; // \kappa

    let ell = {
        let x = if output_size % parity_check_matrix.k != 0 {
            //println!("Warning: The wanted size is not a multiple of the code's k. Adjusting to the next multiple of k.");
            output_size + (parity_check_matrix.k - (output_size % parity_check_matrix.k))
        } else {
            output_size
        };
        x/k
    };

    let m = b * ell + c;

    // Input: Commit to m candidates
    let mut v2 = Vec::with_capacity(m as usize);
    let mut v3 = Vec::with_capacity(m as usize);

    for _ in 0..m {
        let com2 = fcom2.random(channel, rng).unwrap();
        v2.push(com2);
    }
    let mut com2_values: Vec<Fp::PrimeField> = Vec::with_capacity(m as usize);
    for i in 0..m{
        let value = u8::from(v2[i].value());
        let fp_value = Fp::PrimeField::try_from(value);
        match fp_value {
            Ok(val) => com2_values.push(val),
            Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
        }
    }
    /*
    v2
        .iter()
        .map(|x| (u8::from(x.value())).try_into().unwrap())
        .collect();
    */
    let com3_mac = fcom3.input(channel, rng, com2_values.as_slice()).unwrap();
    for i in 0..m {
        let com3 = MacProver::<Fp>::new(com2_values[i], com3_mac[i]);
        v3.push(com3);
    }
    drop(com3_mac);
    drop(com2_values);
    channel.flush().unwrap();

    // Step 0: Check that commitment mod 3 are bits
    let chi: Fp = Fp::random(rng);
    let mut qs_prover = QSStateProver::<Fp, 2>::init_with_chi(chi);

    for i in 0..v3.len(){
        let mut prod_left: HDMacProver<Fp, 2> = v3[i].into();
        let mut prod_right: HDMacProver<Fp, 2> = v3[i].into();
        let mut one: HDMacProver<Fp, 2_> = HDMacProver::new_constant(Fp::ONE);
        one.sub_assign(&prod_right);
        prod_left.mul_assign(&one);
        qs_prover.check_zero(&prod_left);
    }
    qs_prover.finalize(channel, rng, fcom3).unwrap();

    // Step 1: Select subset S of size C given by the verifier
    let seed = channel.read_block().unwrap();
    let mut seed_rng = AesRng::from_seed(seed);
    let mut s = Vec::with_capacity(m as usize);
    for _ in 0..c {
        s.push(1);
    }
    for _ in 0..(m - c) {
        s.push(0);
    }
    s.shuffle(&mut seed_rng);

    // Step 2: Open subset S
    let mut to_open = Vec::with_capacity(c as usize);
    let mut to_check = Vec::with_capacity(c as usize);

    for i in (0..m).rev() {
        if s[i] == 1 {
            to_open.push(v2[i]);
            to_check.push(v3[i]);
            v2.remove(i);
            v3.remove(i);
        }
    }

    fcom2.open(channel, &to_open).unwrap();
    for i in 0..c {
        let value = Fp::PrimeField::try_from(u8::from(to_open[i as usize].value()));
        match value {
            Ok(val) => to_check[i as usize] = fcom3.affine_add_cst(-val, to_check[i as usize]),
            Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
        }
    }
    fcom3.check_zero(channel, &to_check).unwrap();

    // Step 3: Get a random permutation defined by the verifier
    // and group these into \ell buckets of size B
    let mut bucket_index = Vec::with_capacity((ell * b) as usize);
    for _ in 0..b {
        for i in 0..ell {
            bucket_index.push(i);
        }
    }
    
    bucket_index.shuffle(&mut seed_rng);

    let mut buckets2 = vec![vec![]; ell as usize];
    let mut buckets3 = vec![vec![]; ell as usize];

    for i in 0..(b * ell) {
        buckets2[bucket_index[i as usize] as usize].push(v2[i as usize]);
        buckets3[bucket_index[i as usize] as usize].push(v3[i as usize]);
    }
    drop(v2);
    drop(v3);
    drop(bucket_index);

    // Step 4: Check buckets for consistency
    let chi: Fp = Fp::random(rng);
    let mut qs_prover = QSStateProver::<Fp, 3>::init_with_chi(chi);
    let mut c_to_open = Vec::with_capacity(ell * (b-k));
    for bucket in 0..ell {
        // Step 4.a
        for i in 0..b-k{
            let mut c = MacProver::default();
            for j in 0..b{
                if parity_check_matrix.matrix[i][j] == F2::ONE {
                    c = fcom2.add(c, buckets2[bucket][j]);
                }
            }
            c_to_open.push(c);
        }
    }

    // step 4.b
    fcom2.open(channel, &c_to_open).unwrap();

    for bucket in 0..ell {
        // step 4.c
        let mut to_check = Vec::with_capacity(b-k);
        for i in 0..b-k{
            let mut xor_left = HDMacProver::<Fp, 3>::default();
            let mut xor_right = HDMacProver::<Fp, 3>::default();
            for j in 0..b/2{
                if parity_check_matrix.matrix[i][j] == F2::ONE {
                    xor_left.xor_assign(&buckets3[bucket][j].into());
                }
            }
            for j in b/2..b{
                if parity_check_matrix.matrix[i][j] == F2::ONE {
                    xor_right.xor_assign(&buckets3[bucket][j].into());
                }
            }

            let val_results = Fp::PrimeField::try_from(u8::from(c_to_open[bucket*(b-k)+i].value()));
            let val = match val_results {
                Ok(val) => val,
                Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
            };

            if val == Fp::PrimeField::ZERO{
                xor_left.sub_assign(&xor_right);
                //xor_left.sub_assign_constant((val).into());
            } else {
                xor_left.add_assign(&xor_right);
                xor_left.sub_assign_constant(val.into());
            }
            //xor.sub_assign_constant(F3::try_from(u8::from(c_to_open[bucket*(b-k) + i].value())).unwrap().into());
            to_check.push(xor_left);
        }
        for xor in to_check.iter() {
            qs_prover.check_zero(xor);
        }
    }
    qs_prover.finalize(channel, rng, fcom3).unwrap();

    // Step 5: Outpur first k candidates from buckets
    let mut v2_out = Vec::with_capacity(ell*k as usize);
    let mut v3_out = Vec::with_capacity(ell*k as usize);
    for bucket in 0..ell{
        for i in 0..k{
            v2_out.push(buckets2[bucket][i]);
            v3_out.push(buckets3[bucket][i]);
        }
    }

    (v2_out, v3_out)
}

pub fn code_candidate_server<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    fcom2: &mut FComVerifier<Fb>,
    fcom3: &mut FComVerifier<Fp>,
    channel: &mut C,
    rng: &mut RNG,
    code: &CodeType,
) -> (Vec<MacVerifier<Fb>>, Vec<MacVerifier<Fp>>)
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>{
    let parity_check_matrix = match code {
        CodeType::Small => small_code(),
        CodeType::Medium => medium_code(),
        CodeType::Large => large_cpde(),
    };
    
    let k = parity_check_matrix.k;
    let b = parity_check_matrix.b;
    let c = 40; // \kappa

    let ell = {
        let x = if output_size % parity_check_matrix.k != 0 {
            //println!("Warning: The wanted size is not a multiple of the code's k. Adjusting to the next multiple of k.");
            output_size + (parity_check_matrix.k - (output_size % parity_check_matrix.k))
        } else {
            output_size
        };
        x/k
    };

    let m = b * ell + c;

    // Input: Commit to m candidates
    let mut v2 = Vec::with_capacity(m as usize);

    for _ in 0..m {
        let com2 = fcom2.random(channel, rng).unwrap();
        v2.push(com2);
    }
    let mut v3 = fcom3.input(channel, rng, m).unwrap();
    channel.flush().unwrap();

    // Step 0: check commitment mod 3 to be bits
    let delta =  fcom3.get_delta();
    let chi: Fp = Fp::random(rng);
    let mut qs_verifier = QSStateVerifier::<Fp>::init_with_delta_and_chi(delta, chi);
    for i in 0..v3.len(){
        let mut prod_left: HDMacVerifier<Fp> = v3[i].into();
        let mut prod_right: HDMacVerifier<Fp> = v3[i].into();
        let mut one: HDMacVerifier<Fp> = HDMacVerifier::new_constant(delta, Fp::ONE);
        one.sub_assign(delta, &prod_right);
        prod_left.mul_assign(&one);
        qs_verifier.check_zero(&prod_left);
    }
    qs_verifier.finalize_and_verify::<C, RNG, 2>(channel, rng, fcom3).unwrap();

    // Step 1: Select subset S of size C given by the verifier
    let seed = rng.gen::<Block>();
    channel.write_block(&seed).unwrap();
    channel.flush().unwrap();
    let mut seed_rng = AesRng::from_seed(seed);
    let mut s = Vec::with_capacity(m as usize);
    for _ in 0..c {
        s.push(1);
    }
    for _ in 0..(m - c) {
        s.push(0);
    }
    s.shuffle(&mut seed_rng);

    // Step 2: Open subset S
    let mut to_open = Vec::with_capacity(c as usize);
    let mut to_check = Vec::with_capacity(c as usize);

    for i in (0..m).rev() {
        if s[i] == 1 {
            to_open.push(v2[i]);
            to_check.push(v3[i]);
            v2.remove(i);
            v3.remove(i);
        }
    }

    let mut c_openings = Vec::new();
    fcom2.open(channel, &to_open, &mut c_openings).unwrap();

    for i in 0..c {
        let value = Fp::PrimeField::try_from(u8::from(c_openings[i as usize]));
        let value = match value {
            Ok(val) => val,
            Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
        };
        to_check[i as usize] = fcom3.affine_add_cst(-value, to_check[i as usize]);
    }
    fcom3.check_zero(channel, rng, &to_check).unwrap();

    // Step 3: Get a random permutation defined by the verifier
    // and group these into \ell buckets of size B
    let mut bucket_index = Vec::with_capacity((ell * b) as usize);
    for _ in 0..b {
        for i in 0..ell {
            bucket_index.push(i);
        }
    }
    bucket_index.shuffle(&mut seed_rng);

    let mut buckets2 = vec![vec![]; ell as usize];
    let mut buckets3 = vec![vec![]; ell as usize];

    for i in 0..(b * ell) {
        buckets2[bucket_index[i as usize] as usize].push(v2[i as usize]);
        buckets3[bucket_index[i as usize] as usize].push(v3[i as usize]);
    }
    drop(v2);
    drop(v3);
    drop(bucket_index);

    // Step 4: Check buckets for consistency
    let delta =  fcom3.get_delta();
    let chi: Fp = Fp::random(rng);
    let mut qs_verifier = QSStateVerifier::<Fp>::init_with_delta_and_chi(delta, chi);
    let mut c_to_open = Vec::with_capacity(ell * (b-k));
    for bucket in 0..ell {
        // Step 4.a
        for i in 0..b-k{
            let mut c = MacVerifier::default();
            for j in 0..b{
                if parity_check_matrix.matrix[i][j] == F2::ONE {
                    c = fcom2.add(c, buckets2[bucket][j]);
                }
            }
            c_to_open.push(c);
        }        
    }
    // step 4.b
    let mut c_opening = Vec::new();
    fcom2.open(channel, &c_to_open, &mut c_opening).unwrap();

        // step 4.c
    for bucket in 0..ell {
        let mut to_check = Vec::with_capacity(b-k);
        for i in 0..b-k{
            let mut xor_left = HDMacVerifier::<Fp>::default();
            let mut xor_right = HDMacVerifier::<Fp>::default();
            for j in 0..b/2{
                if parity_check_matrix.matrix[i][j] == F2::ONE {
                    xor_left.xor_assign(delta, &buckets3[bucket][j].into());
                }
            }
            for j in b/2..b{
                if parity_check_matrix.matrix[i][j] == F2::ONE {
                    xor_right.xor_assign(delta, &buckets3[bucket][j].into());
                }
            }
            let value = Fp::PrimeField::try_from(u8::from(c_opening[bucket * (b-k) + i]));
            let value = match value {
                Ok(val) => val,
                Err(_) => panic!("Failed to convert u8 to Fp::PrimeField"),
            };

            if value == Fp::PrimeField::ZERO{
                xor_left.sub_assign(delta, &xor_right);
                //xor_left.sub_assign_constant(delta, value.into());
            }else{
                xor_left.add_assign(delta, &xor_right);
                xor_left.add_assign_constant(delta, value.into());
            }
            to_check.push(xor_left);
        }
        for xor in to_check.iter() {
            qs_verifier.check_zero(xor);
        }
    }
    qs_verifier.finalize_and_verify::<C, RNG, 6>(channel, rng, fcom3).unwrap();

    // Step 5: Outpur first k candidates from buckets
    let mut v2_out = Vec::with_capacity(ell*k as usize);
    let mut v3_out = Vec::with_capacity(ell*k as usize);
    for bucket in 0..ell{
        for i in 0..k{
            v2_out.push(buckets2[bucket][i]);
            v3_out.push(buckets3[bucket][i]);
        }
    }

    (v2_out, v3_out)
}

#[cfg(test)]
mod test{
    use super::*;
    use std::{
        io::{BufReader, BufWriter},
        os::unix::net::UnixStream,
    };

    use ocelot::svole::wykw::choose_lpn_parameters;
    use rand::SeedableRng;
    use scuttlebutt::{
        field::{F64b, F64t, F3},
        AesRng, Channel,
    };

    use hd_quicksilver::homcom::FComProver;

    #[test]
    fn test_code_consistency(){
        let (client, server) = UnixStream::pair().unwrap();
        let ell = 98;
        let param = ell;
        let code = CodeType::Large;
        let (lpn_setup_params, lpn_extend_params) =
        choose_lpn_parameters::<F3>(2 * param);
        let handle  = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom2 = FComProver::<F64b>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params.clone(),
                lpn_extend_params.clone(),
            ).unwrap();
            let mut fcom3 = FComProver::<F64t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params.clone(),
                lpn_extend_params.clone(),
            ).unwrap();
            let vecs = code_candidate_client(param, &mut fcom2, &mut fcom3, &mut channel, &mut rng, &code);
            return (vecs.0, vecs.1);
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom2 = FComVerifier::<F64b>::init(
            &mut channel,
            &mut rng,
            lpn_setup_params.clone(),
            lpn_extend_params.clone(),
        ).unwrap();
        let mut fcom3 = FComVerifier::<F64t>::init(
            &mut channel,
            &mut rng,
            lpn_setup_params.clone(),
            lpn_extend_params.clone(),
        ).unwrap();
        let vecs = code_candidate_server(param, &mut fcom2, &mut fcom3, &mut channel, &mut rng, &code);
        
        let (v2, v3) = handle.join().unwrap();

        for i in 0..ell{
            let c2: u8 = v2[i].value().into();
            let c3: u8 = v3[i].value().into();
            assert_eq!(c2, c3);
        }

        for i in 0..ell{
            assert_eq!(v2[i].value() * fcom2.get_delta() + v2[i].mac(), vecs.0[i].mac());
            assert_eq!(-v3[i].value() * fcom3.get_delta() + v3[i].mac(), vecs.1[i].mac());
        }
    }
}