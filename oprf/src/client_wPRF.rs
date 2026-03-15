use ocelot::svole::wykw::choose_lpn_parameters;
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{F256b, FiniteField, F3}, ring::FiniteRing, AbstractChannel};
use crate::{daBits_cnc_consistency::{candidate_client, candidate_server, get_bucket_size}, daBits_code_consistency::{code_candidate_client, code_candidate_server, CodeType}, habits::ha_bit_server, matrix_util::compute_row_using_table};
use hd_quicksilver::homcom::MacVerifier;

use crate::{dabits::OPRFSharing, habits::ha_bit_client, vole_util::*};
use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver};


pub fn c_preprocess_client<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    batch_size: usize,
) -> ((Vec<OPRFSharing<Fb>>, Vec<Fp::PrimeField>), 
(Vec<MacProver<Fb>>, Vec<MacProver<Fp>>),
      FComProver<Fp>, FComProver<Fb>, FComProver<Fb>)
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{
    let n = 256;

    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<Fp>(batch_size*n*2+400);
    let mut fcom_p_3 = FComProver::<Fp>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    let a  = fcom_p_3.extract_svole_sender();
    
    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<Fb>(batch_size*n*3);
    let mut fcom_p_2 = FComProver::<Fb>::init_from_previous_setup_sender(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();

    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<Fb>(batch_size*n);
    let fcom_k = FComProver::<Fb>::init_from_previous_setup_sender(channel, rng, fcom_k_params, fcom_k_params_extend, a).unwrap();

    let (lpn_share_setup_params, lpn_share_extend_params) = choose_lpn_parameters::<Fb>(batch_size*n);
    let fcom_k_delta = FComProver::<Fb>::init_from_previous_setup_sender(channel, rng, lpn_share_setup_params, lpn_share_extend_params, a).unwrap();

    let mut ha_bits: (Vec<OPRFSharing<Fb>>, Vec<Fp::PrimeField>) = (Vec::new(), Vec::new());
    let mut encoding_dabits: (Vec<MacProver<Fb>>, Vec<MacProver<Fp>>) = (Vec::new(), Vec::new());
    if n*batch_size > 1<<21{
        let interations = (n*batch_size) / (1<<20);
        for _ in 0..(interations-1){
            let habits= ha_bit_client::<Fb, Fp, _, _>(1<<20, &mut fcom_p_2, channel, rng);
            ha_bits.0.extend(habits.0);
            ha_bits.1.extend(habits.1);
            let encoding = code_candidate_client(1<<20, &mut fcom_p_2, &mut fcom_p_3, channel, rng, &CodeType::Large);
            encoding_dabits.0.extend(encoding.0);
            encoding_dabits.1.extend(encoding.1);
        }
        let habits= ha_bit_client::<Fb, Fp, _, _>(n*batch_size - (interations-1)*(1<<20), &mut fcom_p_2, channel, rng);
        ha_bits.0.extend(habits.0);
        ha_bits.1.extend(habits.1);
        let encoding = code_candidate_client(n*batch_size - (interations-1)*(1<<20), &mut fcom_p_2, &mut fcom_p_3, channel, rng, &CodeType::Large);
        encoding_dabits.0.extend(encoding.0);
        encoding_dabits.1.extend(encoding.1);
    } else {
        ha_bits = ha_bit_client::<Fb, Fp, _, _>(n*batch_size, &mut fcom_p_2, channel, rng);
        if n*batch_size >= 1<<14{
            encoding_dabits = code_candidate_client(n*batch_size, &mut fcom_p_2, &mut fcom_p_3, channel, rng, &CodeType::Large);
        }else{
            let bucket_size = get_bucket_size(n*batch_size);
            encoding_dabits = candidate_client((n*batch_size, bucket_size, 3), &mut fcom_p_2, &mut fcom_p_3, channel, rng)
        }
        
    }


    return (ha_bits, encoding_dabits, fcom_p_3, fcom_k, fcom_k_delta);
}

pub fn c_preprocess_server<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    batch_size: usize,
    key: Fb,
) -> ((Vec<OPRFSharing<Fb>>, Vec<Fp::PrimeField>), 
(Vec<MacVerifier<Fb>>, Vec<MacVerifier<Fp>>),
FComVerifier<Fb>, FComVerifier<Fp>, FComVerifier<Fb>, FComVerifier<Fb>)
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{
    let n = 256;

    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<Fp>(batch_size*n*2+400);
    let mut fcom_v_3 = FComVerifier::<Fp>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    let a = fcom_v_3.extract_svole_receiver();
    
    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<Fb>(batch_size*n*3);
    let mut fcom_v_2 = FComVerifier::<Fb>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();

    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<Fb>(batch_size*n);
    let fcom_k: FComVerifier<Fb> = FComVerifier::<Fb>::init_with_picked_delta_and_ot_receiver(channel, rng, fcom_k_params, fcom_k_params_extend, key, a).unwrap();

    let (lpn_share_setup_params, lpn_share_extend_params) = choose_lpn_parameters::<Fb>(batch_size*n);
    let fcom_k_delta = FComVerifier::<Fb>::init_with_picked_delta_and_ot_receiver(channel, rng, lpn_share_setup_params, lpn_share_extend_params, key* fcom_v_2.get_delta(), a).unwrap();
    
    let mut ha_bits: (Vec<OPRFSharing<Fb>>, Vec<Fp::PrimeField>) = (Vec::new(), Vec::new());
    let mut encoding_dabits: (Vec<MacVerifier<Fb>>, Vec<MacVerifier<Fp>>) = (Vec::new(), Vec::new());
    if n*batch_size > 1<<21{
        let interations = (n*batch_size) / (1<<20);
        for _ in 0..(interations-1){
            let habits= ha_bit_server::<Fb, Fp, _, _>(1<<20, &mut fcom_v_2, channel, rng);
            ha_bits.0.extend(habits.0);
            ha_bits.1.extend(habits.1);
            let encoding = code_candidate_server(1<<20, &mut fcom_v_2, &mut fcom_v_3, channel, rng, &CodeType::Large);
            encoding_dabits.0.extend(encoding.0);
            encoding_dabits.1.extend(encoding.1);
        }
        let habits= ha_bit_server::<Fb, Fp, _, _>(n*batch_size - (interations-1)*(1<<20), &mut fcom_v_2, channel, rng);
        ha_bits.0.extend(habits.0);
        ha_bits.1.extend(habits.1);
        let encoding = code_candidate_server(n*batch_size - (interations-1)*(1<<20), &mut fcom_v_2, &mut fcom_v_3, channel, rng, &CodeType::Large);
            encoding_dabits.0.extend(encoding.0);
            encoding_dabits.1.extend(encoding.1);
    } else {
        ha_bits = ha_bit_server::<Fb, Fp, _, _>(n*batch_size, &mut fcom_v_2, channel, rng);
        if n*batch_size >= 1<<14{   
            encoding_dabits = code_candidate_server(n*batch_size, &mut fcom_v_2, &mut fcom_v_3, channel, rng, &CodeType::Large);
        }else{
            let bucket_size = get_bucket_size(n*batch_size);
            encoding_dabits = candidate_server((n*batch_size, bucket_size, 3), &mut fcom_v_2, &mut fcom_v_3, channel, rng)
        }
    }


    return (ha_bits, encoding_dabits, fcom_v_2, fcom_v_3, fcom_k, fcom_k_delta);
}

pub fn c_w_prf_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
    inputs: Vec<F256b>,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b_tables: Vec<F3>,
    ha_bits: (Vec<OPRFSharing<F256b>>, Vec<F3>),
    input_coms: Vec<F256b>,
    fcom_k_delta: &mut FComProver<F256b>,
) -> Vec<F3>{
    let n = 256;
    let t = 82;
   
    let mut mac_share = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let x = inputs[j];
        // Authenticate client share
        let (value_c_share, z_0) = lift_prover_vole(fcom_k_delta, channel, rng, n);
        let diff = value_c_share - x;
        channel.write_serializable(&diff).unwrap();

        mac_share.push(z_0);
    }
    channel.flush().unwrap();

    // Convert shares to F3
    let mut habit_2_values = Vec::with_capacity(batch_size);
    let mut habit_2_mac = Vec::with_capacity(batch_size);

    for j in 0..batch_size{
        let mut bit_2_value: F256b = ha_bits.0[0 + j*n].0.into();
        let mut bit_2_mac   = ha_bits.0[0 + j*n].1.mac();
        
        let mut pow = F256b::ONE;
        for i in 1..n{
            pow.shift_left_once();
            bit_2_value = bit_2_value + ha_bits.0[i + j*n].0 * pow;
            bit_2_mac = bit_2_mac + ha_bits.0[i + j*n].1.mac().pow_mul(i);
        }
        habit_2_values.push(bit_2_value);
        habit_2_mac.push(bit_2_mac);
    }

    let mut c_to_open = Vec::with_capacity(batch_size);
    let mut c_macs = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_c = habit_2_values[j] + input_coms[j];
        let c_mac = habit_2_mac[j] + mac_share[j];
        c_to_open.push(c_c);
        c_macs.push(c_mac);
    };
    drop(mac_share);
    drop(habit_2_values);
    drop(habit_2_mac);
    open_extension_mac_prover(channel, &c_to_open, &c_macs).unwrap();

    let c_server = channel.read_serializable_seq::<F256b>(c_to_open.len()).unwrap();

    let mut c = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let val = c_to_open[j] + c_server[j];
        c.push(val);
    }
    drop(c_server);
    drop(c_to_open);
    drop(c_macs);

    let mut out_share = Vec::new();
    for j in 0..batch_size{
        let mut c_bit_string = [F3::ZERO; 256];
        for i in 0..128{
            let c_i = (c[j].low >> i) & 1;
            let c_i: F3 = F3::try_from(c_i).unwrap();
            c_bit_string[i] = c_i;
            let c_i = (c[j].high >> i) & 1;
            let c_i: F3 = F3::try_from(c_i).unwrap();
            c_bit_string[i + 128] = c_i;
        }

        let mut value_share = [F3::ZERO; 256];

        for i in 0..n{
            let b_3_i = ha_bits.1[i + j*n];
            let val = b_3_i + c_bit_string[i]*b_3_i;
            value_share[i] = val;
        }

        let values = compute_row_using_table(&b_tables, value_share.into());
        for i in 0..t{
            out_share.push(values[i]);
        }
    }

    let out_share_server = channel.read_serializable_seq::<F3>(out_share.len()).unwrap();

    let mut out = Vec::new();
    for i in 0..t*batch_size{
        let value = out_share[i] + out_share_server[i];
        out.push(value);
    }
    out
}

pub fn c_w_prf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    _key: F256b,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b_tables: Vec<F3>,
    ha_bits: (Vec<OPRFSharing<F256b>>, Vec<F3>),
    fcom_v: &mut FComVerifier<F256b>,
    fcom_k_delta: &mut FComVerifier<F256b>,
    input_coms: Vec<F256b>,
) -> (){
    let n = 256;
    let t = 82;

    let mut key_share = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let mut z_1 = lift_verifier_vole(fcom_k_delta, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        z_1 = z_1 - fcom_k_delta.get_delta() * d;

        key_share.push(fcom_v.get_delta() * input_coms[j] - z_1);
    }

    // Convert shares to F3
    let mut habit_2_values = Vec::with_capacity(batch_size);
    let mut habit_2_key = Vec::with_capacity(batch_size);

    for j in 0..batch_size{
        let mut bit_2_value: F256b = ha_bits.0[0+j*n].0.into();
        let mut bit_2_key   = ha_bits.0[0+j*n].2.mac();
        
        let mut pow = F256b::ONE;
        for i in 1..n{
            pow.shift_left_once();
            bit_2_value = bit_2_value + ha_bits.0[i + j*n].0 * pow;
            bit_2_key = bit_2_key + ha_bits.0[i + j*n].2.mac().pow_mul(i);
        }
        habit_2_values.push(bit_2_value);
        habit_2_key.push(bit_2_key);
    }

    let mut c_to_open = Vec::with_capacity(batch_size);
    let mut c_keys = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_c = habit_2_values[j] + input_coms[j];
        let c_key = habit_2_key[j] + key_share[j];
        c_to_open.push(c_c);
        c_keys.push(c_key);
    };
    drop(key_share);
    drop(habit_2_values);
    drop(habit_2_key);
    let mut c_opened: Vec<F256b> = Vec::new();
    open_extension_mac_verifier(channel, &c_keys, fcom_v.get_delta(), &mut c_opened).unwrap();

    channel.write_serializable_seq(&c_to_open).unwrap();
    channel.flush().unwrap();

    let mut c = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let val = c_opened[j] + c_to_open[j];
        c.push(val);
    }
    drop(c_opened);
    drop(c_keys);

    let mut out_share = Vec::new();
    for j in 0..batch_size{
        let mut c_bit_string = [F3::ZERO; 256];
        for i in 0..128{
            let c_i = (c[j].low >> i) & 1;
            let c_i: F3 = F3::try_from(c_i).unwrap();
            c_bit_string[i] = c_i;
            let c_i = (c[j].high >> i) & 1;
            let c_i: F3 = F3::try_from(c_i).unwrap();
            c_bit_string[i + 128] = c_i;
        }

        let mut value_share = [F3::ZERO; 256];

        for i in 0..n{
            let b_3_i = ha_bits.1[i + j*n];
            let val = c_bit_string[i] + b_3_i + c_bit_string[i]*b_3_i;
            value_share[i] = val;
        }

        let values = compute_row_using_table(&b_tables, value_share.into());
        for i in 0..t{
            out_share.push(values[i]);
        }
    }

    channel.write_serializable_seq::<F3>(&out_share).unwrap();
    channel.flush().unwrap();
}

#[cfg(test)]
mod tests{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    use rand::SeedableRng;
    use scuttlebutt::{field::{F256b, F64b, F82t, F3}, AesRng, Block, Channel};

    use crate::{full_wPRF::{w_prf_clear, w_prf_client_commit_to_input, w_prf_server_commit_to_input}, matrix_util::generate_precompute_tables};

    use super::*;

    #[test]
    fn c_w_prf_test_single(){
        let seed = Block::from([0; 16]);

        let mut b_rng = AesRng::from_seed(seed);
        let mut b_m: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b_m[i][j] = F3::random(&mut b_rng);
            }
        }
        let b = generate_precompute_tables(b_m);
        let b_s = b.clone();
        let key = F256b::from(F64b::from(50u64));
        let inputs = vec![F256b::random(&mut b_rng)];
        let len = inputs.len();
        let clear = inputs.iter().map(|x| w_prf_clear(key, *x, b_m)).collect::<Vec<_>>();

        let (client, server) = UnixStream::pair().unwrap();

        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);

            let (habits, _, _, mut fcom_k, mut fcom_k_delta) = c_preprocess_client::<F256b, F82t, _, _>(&mut channel, &mut rng, len);
            let input_coms = w_prf_client_commit_to_input(&inputs, len, &mut channel, &mut rng, &mut fcom_k);
            c_w_prf_client(inputs, len, &mut channel, &mut rng, b, habits, input_coms, &mut fcom_k_delta)
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let (habits, _, mut fcom_v_2, _, mut fcom_k, mut fcom_k_delta) = c_preprocess_server::<F256b, F82t, _, _>(&mut channel, &mut rng, len, key);
        let input_coms = w_prf_server_commit_to_input(len, &mut channel, &mut rng, &mut fcom_k);
        c_w_prf_server(key, len, &mut channel, &mut rng, b_s, habits, &mut fcom_v_2, &mut fcom_k_delta, input_coms);

        let fk_x = handle.join().unwrap();

        for j in 0..len{
            for i in 0..82{
                assert_eq!(fk_x[j*82 + i], clear[j][i], "Output of wPRF does not match clear output at index {i} for input {j}");
            }
        }

    }

    #[test]
    fn c_w_prf_test_batch(){
        let seed = Block::from([0; 16]);

        let mut b_rng = AesRng::from_seed(seed);
        let mut b: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b[i][j] = F3::random(&mut b_rng);
            }
        }
        let bc = generate_precompute_tables(b);
        let bs = bc.clone();

        let key = F256b::from(F64b::from(50u64));
        let inputs = vec![F256b::random(&mut b_rng), F256b::random(&mut b_rng), F256b::random(&mut b_rng)];
        let len = inputs.len();
        let clear = inputs.iter().map(|x| w_prf_clear(key, *x, b)).collect::<Vec<_>>();

        let (client, server) = UnixStream::pair().unwrap();

        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);

            let (habits, _, _, mut fcom_k, mut fcom_k_delta) = c_preprocess_client::<F256b, F82t, _, _>(&mut channel, &mut rng, len);
            let input_coms = w_prf_client_commit_to_input(&inputs, len, &mut channel, &mut rng, &mut fcom_k);
            c_w_prf_client(inputs, len, &mut channel, &mut rng, bc, habits, input_coms, &mut fcom_k_delta)
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let (habits, _, mut fcom_v_2, _, mut fcom_k, mut fcom_k_delta) = c_preprocess_server::<F256b, F82t, _, _>(&mut channel, &mut rng, len, key);
        let input_coms = w_prf_server_commit_to_input(len, &mut channel, &mut rng, &mut fcom_k);
        c_w_prf_server(key, len, &mut channel, &mut rng, bs, habits, &mut fcom_v_2, &mut fcom_k_delta, input_coms);

        let fk_x = handle.join().unwrap();

        for j in 0..len{
            for i in 0..82{
                assert_eq!(fk_x[j*82 + i], clear[j][i], "Output of wPRF does not match clear output at index {i} for input {j}");
            }
        }

    }
}