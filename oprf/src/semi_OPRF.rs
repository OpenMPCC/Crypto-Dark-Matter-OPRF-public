use ocelot::svole::wykw::choose_lpn_parameters;
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{F256b, F64b, F2, F3}, ring::FiniteRing, AbstractChannel};

use crate::{vole_util::{lift_prover_vole, lift_verifier_vole}, matrix_util::compute_row_using_table, ot_d_bits::{ot_d_bits_client, ot_d_bits_server}}; 
use hd_quicksilver::homcom::{FComProver, FComVerifier};

pub fn semi_preprocesses_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C, 
    rng: &mut RNG,
    batch_size: usize,
) -> (FComProver<F256b>, Vec<(u8, F3)>) {
    let n = 256;
    let vole_size = ((batch_size*n) as f64 * 1.5) as usize;
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F64b>(vole_size as usize);
    let mut fcom_p_2 = FComProver::<F64b>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    
    let d_bits = ot_d_bits_client(batch_size*n, channel, rng, &mut fcom_p_2);
    
    let prev_ot = fcom_p_2.extract_svole_sender();
    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<F256b>(batch_size*n);
    let fcom_k = FComProver::<F256b>::init_from_previous_setup_sender(channel, rng, fcom_k_params, fcom_k_params_extend, prev_ot).unwrap();

    return (fcom_k, d_bits);
}

pub fn semi_preprocesses_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C, 
    rng: &mut RNG,
    batch_size: usize,
) -> (FComVerifier<F256b>, Vec<(u8, F3)>) {
    let n = 256;
    let vole_size = ((batch_size*n) as f64 * 1.5) as usize;
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F64b>(vole_size as usize);
    let mut fcom_v_2 = FComVerifier::<F64b>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();

    let d_bits = ot_d_bits_server(batch_size*n, channel, rng, &mut fcom_v_2);

    let prev_ot = fcom_v_2.extract_svole_receiver();
    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<F256b>(batch_size*n);
    let fcom_k = FComVerifier::<F256b>::init_from_previous_setup_receiver(channel, rng, fcom_k_params, fcom_k_params_extend, prev_ot).unwrap();

    return (fcom_k, d_bits);
}

pub fn semi_oprf_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
    inputs: Vec<F256b>,
    batch_size: usize,
    d_bits: Vec<(u8, F3)>,
    channel: &mut C, 
    rng: &mut RNG,
    b_tables: Vec<F3>, 
    fcom_k: &mut FComProver<F256b>,
) -> Vec<F3>{
    let n = 256;
    let t = 82;

    let mut c_share = Vec::with_capacity(batch_size);
    for i in 0..batch_size{
        let (value, share) = lift_prover_vole(fcom_k, channel, rng, n);
        let input = inputs[i];
        let diff = value - input;
        channel.write_serializable(&diff).unwrap();
        c_share.push(share);
    }
    channel.flush().unwrap();

    //Lift dBits
    let mut d_bit_2_values = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let mut d_bit_2_value: F256b = F2::try_from(d_bits[0+j*n].0).unwrap().into();
        let mut pow = F256b::ONE;
        for i in 1..n{
            pow.shift_left_once();
            d_bit_2_value += F2::try_from(d_bits[i+j*n].0).unwrap() * pow;
        }
        d_bit_2_values.push(d_bit_2_value);
    }

    // Open masked value
    let mut c_to_open = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let value = c_share[j] + d_bit_2_values[j];
        c_to_open.push(value);
    }
    channel.write_serializable_seq(&c_to_open).unwrap();
    channel.flush().unwrap();

    let c_opened: Vec<F256b> = channel.read_serializable_seq(batch_size).unwrap();


    // Convert to F3
    let mut out_values = Vec::with_capacity(batch_size*t);
    let mut c_bit_string = [F3::ZERO; 256];
    for j in 0..batch_size{
        let mut values = [F3::ZERO; 256];
        let c = c_opened[j] + c_to_open[j];

        // Decompose c into bits
        for i in 0..128{
            let c_i = (c.low >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i] = c_i;
            let c_i = (c.high >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i + 128] = c_i;
        }

        // Convert values
        for i in 0..n{
            let c_i = c_bit_string[i];
            values[i] = c_i + d_bits[i+j*n].1 + c_i*d_bits[i+j*n].1;
        }

        // Apply B
        let values = compute_row_using_table(&b_tables, values.into());
        for i in 0..t{
            out_values.push(values[i]);
        }
    }

    let out_values_server: Vec<F3> = channel.read_serializable_seq(out_values.len()).unwrap();
    let mut out = Vec::with_capacity(out_values.len());
    for i in 0..out_values.len(){
        out.push(out_values[i] + out_values_server[i]);
    }
    out
}

pub fn semi_oprf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    _key: F256b,
    batch_size: usize,
    d_bits: Vec<(u8, F3)>,
    channel: &mut C, 
    rng: &mut RNG,
    b_tables: Vec<F3>, 
    fcom_k: &mut FComVerifier<F256b>,
) -> (){
    let n = 256;
    let t = 82;

    let mut c_share = Vec::with_capacity(batch_size);
    for _ in 0..batch_size{
        // Multiply input
        let mut y_1 = lift_verifier_vole(fcom_k, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        y_1 = y_1 - fcom_k.get_delta() * d;
        c_share.push(y_1);
    }

    //Lift dBits
    let mut d_bit_2_values = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let mut d_bit_2_value: F256b = F2::try_from(d_bits[0+j*n].0).unwrap().into();
        let mut pow = F256b::ONE;
        for i in 1..n{
            pow.shift_left_once();
            d_bit_2_value += F2::try_from(d_bits[i+j*n].0).unwrap() * pow;
        }
        d_bit_2_values.push(d_bit_2_value);
    }

    // Open masked value
    let c_opened: Vec<F256b> = channel.read_serializable_seq(batch_size).unwrap();
    
    let mut c_to_open = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let value = c_share[j] + d_bit_2_values[j];
        c_to_open.push(value);
    }
    channel.write_serializable_seq(&c_to_open).unwrap();
    channel.flush().unwrap();

    // Convert to F3
    let mut out_values = Vec::with_capacity(batch_size*t);
    let mut c_bit_string = [F3::ZERO; 256];
    for j in 0..batch_size{
        let mut values = [F3::ZERO; 256];
        let c = c_opened[j] + c_to_open[j];

        // Decompose c into bits
        for i in 0..128{
            let c_i = (c.low >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i] = c_i;
            let c_i = (c.high >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i + 128] = c_i;
        }

        // Convert values
        for i in 0..n{
            let c_i = c_bit_string[i];
            values[i] = d_bits[i+j*n].1 + c_i*d_bits[i+j*n].1;
        }

        // Apply B
        let values = compute_row_using_table(&b_tables, values.into());
        for i in 0..t{
            out_values.push(values[i]);
        }
    }

    channel.write_serializable_seq(&out_values).unwrap();
    channel.flush().unwrap();
}

#[cfg(test)]
mod test{
    use std::io::{BufReader, BufWriter};
    use std::os::unix::net::UnixStream;

    use rand::SeedableRng;
    
    use scuttlebutt::{AesRng, Block, Channel};

    use super::*;
    
    use crate::full_wPRF::w_prf_clear;
    
    use crate::matrix_util::generate_precompute_tables;
    

    #[test]
    fn test_semi_oprf() {
        let seed = Block::from([0; 16]);

        let mut b_rng = AesRng::from_seed(seed);
        let mut b_m: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b_m[i][j] = F3::random(&mut b_rng);
            }
        }

        let bc = generate_precompute_tables(b_m);
        let bs = bc.clone();
        
        let batch_size = 1;
        let input = F256b::random(&mut b_rng);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let inputs = vec![input];

            let (mut fcom_k, d_bits) = semi_preprocesses_client(&mut channel, &mut rng, batch_size);
            let out = semi_oprf_client(inputs, batch_size, d_bits, &mut channel, &mut rng, bc, &mut fcom_k);
            out
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let (mut fcom_k, d_bits) = semi_preprocesses_server(&mut channel, &mut rng, batch_size);
        let key = fcom_k.get_delta();
        semi_oprf_server(key, batch_size, d_bits, &mut channel, &mut rng, bs, &mut fcom_k);

        let fk_x = handle.join().unwrap();

        // Verify the output
        let expected_out = w_prf_clear(key, input, b_m);
        for i in 0..82{
            assert_eq!(fk_x[i], expected_out[i], "Mismatch at index {}", i);
        }

    }

    #[test]
    fn test_semi_oprf_batch() {
        let seed = Block::from([0; 16]);

        let mut b_rng = AesRng::from_seed(seed);
        let mut b_m: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b_m[i][j] = F3::random(&mut b_rng);
            }
        }

        let bc = generate_precompute_tables(b_m);
        let bs = bc.clone();
        
        let batch_size = 4;
        let inputs = vec![F256b::random(&mut b_rng), F256b::random(&mut b_rng), F256b::random(&mut b_rng),F256b::random(&mut b_rng)];
        let inputs_expected = inputs.clone();

        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);

            let (mut fcom_k, d_bits) = semi_preprocesses_client(&mut channel, &mut rng, batch_size);
            let out = semi_oprf_client(inputs, batch_size, d_bits, &mut channel, &mut rng, bc, &mut fcom_k);
            out
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let (mut fcom_k, d_bits) = semi_preprocesses_server(&mut channel, &mut rng, batch_size);
        let key = fcom_k.get_delta();
        semi_oprf_server(key, batch_size, d_bits, &mut channel, &mut rng, bs, &mut fcom_k);

        let fk_x = handle.join().unwrap();

        let expected_output = inputs_expected.iter().map(|input| {
            let encoded_input = input;
            w_prf_clear(key, *encoded_input, b_m)
        }).collect::<Vec<_>>();

        // Verify the output
        for j in 0..4{
            for i in 0..82{
                assert_eq!(fk_x[i + 82*j], expected_output[j][i], "Mismatch at index {}", i);
            }
        }

    }
}