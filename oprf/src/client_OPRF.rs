use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{F128b, F256b, F82t, F3}, ring::FiniteRing, AbstractChannel};

use crate::{client_wPRF::{c_w_prf_client, c_w_prf_server}, dabits::OPRFSharing, full_wPRF::{w_prf_client_commit_to_input, w_prf_server_commit_to_input}, input_encoding::{apply_gadget, apply_parity_check_matrix_f82t, generate_linear_code, encode_input}, vole_util::*};
use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};

pub struct CDMOPRFHalfReceiver{
    // VOLE correlations
    pub f2_p: FComProver<F256b>,
    pub f3_p: FComProver<F82t>,
    pub fk: FComProver<F256b>,
    pub fk_delta: FComProver<F256b>,

    // Preprocessing
    pub ha_bits: (Vec<OPRFSharing<F256b>>, Vec<F3>),
    pub encoding_la_bits: (Vec<MacProver<F256b>>, Vec<MacProver<F82t>>),

    // CMD Setting
    pub b: [[F3; 256];82],
    pub b_tables: Vec<F3>,
}

pub struct CDMOPRFHalfSender{
    // VOLE correlations
    pub f2_p: FComVerifier<F256b>,
    pub f3_p: FComVerifier<F82t>,
    pub fk: FComVerifier<F256b>,
    pub fk_delta: FComVerifier<F256b>,

    // Preprocessing
    pub ha_bits: (Vec<OPRFSharing<F256b>>, Vec<F3>),
    pub encoding_la_bits: (Vec<MacVerifier<F256b>>, Vec<MacVerifier<F82t>>),

    // CMD Setting
    pub b: [[F3; 256];82],
    pub b_tables: Vec<F3>,
}

pub fn c_oprf_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
    input: Vec<F128b>,
    channel: &mut C,
    rng: &mut RNG,
    b_tables: Vec<F3>,
    ha_bits: (Vec<OPRFSharing<F256b>>, Vec<F3>),
    encoding_da_bits: (Vec<MacProver<F256b>>, Vec<MacProver<F82t>>),
    fcom_p_3: &mut FComProver<F82t>,
    fcom_k: &mut FComProver<F256b>,
    fcom_k_delta: &mut FComProver<F256b>,
) -> Vec<F3> {
    let(g, gadget, h) = generate_linear_code();
    let mut encoded_inputs = Vec::with_capacity(input.len());
    for i in input{
        let encoded = encode_input(i, g);
        encoded_inputs.push(encoded);
    }
    let batch_size = encoded_inputs.len();
        
    let n = 256;

    let (dabits_2, dabits_3) = encoding_da_bits;

    let coms = w_prf_client_commit_to_input(&encoded_inputs, batch_size, channel, rng, fcom_k);

    let diff = channel.read_serializable::<F256b>().unwrap();

    // Lift dabits
    let mut dabit_2_values = Vec::with_capacity(batch_size);
    let mut dabit_2_mac = Vec::with_capacity(batch_size);

    for j in 0..batch_size{
        let mut bit_2_value: F256b = dabits_2[0 + j*n].value().into();
        let mut bit_2_mac   = dabits_2[0 + j*n].mac() + dabits_2[0 + j*n].value() * diff;
        
        let mut pow = F256b::ONE;
        for i in 1..n{
            pow.shift_left_once();
            bit_2_value = bit_2_value + dabits_2[i + j*n].value() * pow;
            bit_2_mac = bit_2_mac + (dabits_2[i + j*n].mac() + dabits_2[i + j*n].value() * diff).pow_mul(i);
        }
        dabit_2_values.push(bit_2_value);
        dabit_2_mac.push(bit_2_mac);
    }

    let mut c_to_open = Vec::with_capacity(batch_size);
    let mut c_macs = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_c = dabit_2_values[j] + encoded_inputs[j];
        let c_mac = dabit_2_mac[j] + coms[j];
        c_to_open.push(c_c);
        c_macs.push(c_mac);
    };
    open_extension_mac_prover(channel, &c_to_open, &c_macs).unwrap();
    drop(c_macs);
    drop(dabit_2_mac);
    drop(dabit_2_values);

    // Convert mac to F3 and apply gadget & H
    let mut check_macs = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let mut mac_f3 = Vec::with_capacity(254);

        let mut c_bit_string = [F3::ZERO; 256];
        for i in 0..128{
            let value = (c_to_open[j].low >> i) & 1;
            c_bit_string[i] = F3{msb: 0, lsb: value as u8};
            let value = (c_to_open[j].high >> i) & 1;
            c_bit_string[i+128] = F3{msb: 0, lsb: value as u8};
        }

        for i in 0..2{
            let dabit3_i = dabits_3[i+j*n];
            let c_i = c_bit_string[i];
            let mac = dabit3_i.mac() + c_i * dabit3_i.mac();
            let mac = MacProver::new(F3::ONE, mac);
            let mac = fcom_p_3.affine_add_cst(F3::ONE + F3::ONE, mac);
            check_macs.push(mac);
        }

        // Convert to F3
        for i in 2..256{
            let dabit3_i = dabits_3[i+j*n];
            let c_i = c_bit_string[i];

            let mac = dabit3_i.mac() + c_i * dabit3_i.mac();
            mac_f3.push(mac);
        }

        mac_f3.reverse();

        // apply gadget
        let gadget_out = apply_gadget(mac_f3.try_into().unwrap(), gadget);

        // apply H
        let check_matrix: [F82t; 63] = apply_parity_check_matrix_f82t(gadget_out, h);
        for i in 0..63{
            check_macs.push(MacProver::new(F3::ZERO,check_matrix[i]));
        }
    }

    fcom_p_3.check_zero(channel, &check_macs).unwrap();
    drop(check_macs);
    c_w_prf_client(encoded_inputs, batch_size, channel, rng, b_tables, ha_bits, coms, fcom_k_delta)

}

pub fn c_oprf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    key: F256b, 
    batch_size: usize,
    channel: &mut C, 
    rng: &mut RNG,
    b_tables: Vec<F3>,
    ha_bits: (Vec<OPRFSharing<F256b>>, Vec<F3>),
    encoding_da_bits: (Vec<MacVerifier<F256b>>, Vec<MacVerifier<F82t>>),
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_v_3: &mut FComVerifier<F82t>,
    fcom_k: &mut FComVerifier<F256b>,
    fcom_k_delta: &mut FComVerifier<F256b>,
)-> () {
    let n = 256;
    let(_, gadget, h) = generate_linear_code();

    let (dabits_2, dabits_3) = encoding_da_bits;

    let coms = w_prf_server_commit_to_input(batch_size, channel, rng, fcom_k);

    // Change Delta of commitment
    let diff = fcom_v_2.get_delta() - fcom_k.get_delta();
    channel.write_serializable(&diff).unwrap();
    channel.flush().unwrap();

    // Lift dabits
    let mut dabit_2_mac = Vec::with_capacity(batch_size);

    for j in 0..batch_size{
        let mut bit_2_mac   = dabits_2[0 + j*n].mac();
        
        let mut pow = F256b::ONE;
        for i in 1..n{
            pow.shift_left_once();
            bit_2_mac = bit_2_mac + dabits_2[i + j*n].mac() * pow;
        }
        dabit_2_mac.push(bit_2_mac);
    }

    let mut c_keys = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_mac = dabit_2_mac[j] + coms[j];
        c_keys.push(c_mac);
    };
    let mut c_values = Vec::with_capacity(batch_size);
    open_extension_mac_verifier(channel, &c_keys, fcom_k.get_delta(), &mut c_values).unwrap();
    drop(dabit_2_mac);
    drop(c_keys);

    // Convert mac to F3 and apply gadget & H
    let mut check_macs = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let mut mac_f3 = Vec::with_capacity(254);
        let mut c_bit_string = [F3::ZERO; 256];
        for i in 0..128{
            let value = (c_values[j].low >> i) & 1;
            c_bit_string[i] = F3{msb: 0, lsb: value as u8};
            let value = (c_values[j].high >> i) & 1;
            c_bit_string[i+128] = F3{msb: 0, lsb: value as u8};
        }

        for i in 0..2{
            let dabit3_i = dabits_3[i+j*n];
            let c_i = c_bit_string[i];
    
            let mac = -(c_i*fcom_v_3.get_delta()) + dabit3_i.mac() + c_i * dabit3_i.mac();
            let mac = MacVerifier::new(mac);
            let mac = fcom_v_3.affine_add_cst(F3::ONE + F3::ONE, mac);
            check_macs.push(mac);
        }

        // Convert to F3
        for i in 2..256{
            let dabit3_i = dabits_3[i+j*n];
            let c_i = c_bit_string[i];

            let mac = -(c_i*fcom_v_3.get_delta()) + dabit3_i.mac() + c_i * dabit3_i.mac();
            mac_f3.push(mac);
        }

        mac_f3.reverse();

        // apply gadget
        let gadget_out = apply_gadget(mac_f3.try_into().unwrap(), gadget);

        // apply H
        let check_matrix: [F82t; 63] = apply_parity_check_matrix_f82t(gadget_out, h);
        for i in 0..63{
            check_macs.push(MacVerifier::new(check_matrix[i]));
        }
    }

    fcom_v_3.check_zero(channel, rng, &check_macs).unwrap();
    drop(check_macs);

    c_w_prf_server(key, batch_size, channel, rng, b_tables, ha_bits, fcom_v_2, fcom_k_delta, coms);

}


#[cfg(test)]
mod test{
    
    use std::io::{BufReader, BufWriter};
    use std::os::unix::net::UnixStream;

    use rand::SeedableRng;
    
    use scuttlebutt::{AesRng, Block, Channel};

    use super::*;
    use crate::client_wPRF::{c_preprocess_client, c_preprocess_server};
    
    use crate::full_wPRF::w_prf_clear;
    use crate::matrix_util::generate_precompute_tables;

    #[test]
    fn test_oprf() {
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


        let input = F128b::random(&mut b_rng);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let inputs = vec![input];

            let (habits, encoding_dabits, mut fcom_p_3, mut fcom_k, mut fcom_k_delta) = c_preprocess_client(&mut channel, &mut rng, 1);
            let out = c_oprf_client(inputs, &mut channel, &mut rng, bc, habits, encoding_dabits, &mut fcom_p_3, &mut fcom_k, &mut fcom_k_delta);
                out
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let key = F256b::random(&mut rng);
        let batch_size = 1;
        let (habits, encoding_dabits, mut fcom_v_2, mut fcom_v_3, mut fcom_k, mut fcom_k_delta) = c_preprocess_server(&mut channel, &mut rng, batch_size, key);
        let _ = c_oprf_server(key, batch_size, &mut channel, &mut rng, bs, habits, encoding_dabits, &mut fcom_v_2, &mut fcom_v_3, &mut fcom_k, &mut fcom_k_delta);
          
        let fk_x = handle.join().unwrap();

        // Verify the output
        let encoded_input = encode_input(input, generate_linear_code().0);
        let expected_out = w_prf_clear(key, encoded_input, b);
        for i in 0..82{
            assert_eq!(fk_x[i], expected_out[i], "Mismatch at index {}", i);
        }

    }

    #[test]
    fn test_oprf_batch() {
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

        let mut inputs = Vec::new();
        for _ in 0..10{
            let input = F128b::random(&mut b_rng);
            inputs.push(input);
        }
        let mut rng = AesRng::from_seed(seed);
        let key = F256b::random(&mut rng);
        let batch_size = inputs.len();


        let expected_output = inputs.iter().map(|input| {
            let encoded_input = encode_input(input.clone(), generate_linear_code().0);
            w_prf_clear(key, encoded_input, b)
        }).collect::<Vec<_>>();

        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);

            let (habits, encoding_dabits, mut fcom_p_3, mut fcom_k, mut fcom_k_delta) = c_preprocess_client(&mut channel, &mut rng, batch_size);
            let out = c_oprf_client(inputs, &mut channel, &mut rng, bc, habits, encoding_dabits, &mut fcom_p_3, &mut fcom_k, &mut fcom_k_delta);
                out
        });

        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let (habits, encoding_dabits, mut fcom_v_2, mut fcom_v_3, mut fcom_k, mut fcom_k_delta) = c_preprocess_server(&mut channel, &mut rng, batch_size, key);
        let _ = c_oprf_server(key, batch_size, &mut channel, &mut rng, bs, habits, encoding_dabits, &mut fcom_v_2, &mut fcom_v_3, &mut fcom_k, &mut fcom_k_delta);
            
        let fk_x = handle.join().unwrap();
            
            // Verify the output
        for j in 0..10{
            for i in 0..82{
                assert_eq!(fk_x[i + 82*j], expected_output[j][i], "Mismatch at index {}", i);
            }
        }

    }
}