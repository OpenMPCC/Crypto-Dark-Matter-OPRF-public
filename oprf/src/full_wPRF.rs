use hd_quicksilver::{hd_quicksilver::{HDMacProver, HDMacVerifier, QSStateProver, QSStateVerifier}, homcom::{FComProver, FComVerifier, MacProver, MacVerifier}};
use ocelot::svole::wykw::choose_lpn_parameters;
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{polynomial::GeneralPolynomial, F256b, F82t, FiniteField, F3}, ring::FiniteRing, AbstractChannel};
use smallvec::smallvec;
use crate::{daBits_code_consistency::{code_candidate_client, code_candidate_server, CodeType}, dabits::{dabit_client, dabit_server, OPRFExtensionSharing, OPRFSharing}, matrix_util::compute_row_using_table, vole_util::*, OPRF::OPRFSetting};

pub fn preprocess_client<Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    batch_size: usize,
) -> (Vec<(crate::dabits::OPRFExtensionSharing<F256b>, Vec<crate::dabits::OPRFSharing<Fp>>)>, 
(Vec<MacProver<F256b>>, Vec<MacProver<Fp>>), FComProver<F256b>,
      FComVerifier<F256b>, FComVerifier<Fp>, FComProver<Fp>, FComProver<F256b>, FComProver<F256b>, F256b)
where Fp::PrimeField: TryFrom<u8>
{
    let n = 256;

    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<Fp>(batch_size*n*20);
    let mut fcom_v_3 = FComVerifier::<Fp>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    let a = fcom_v_3.extract_svole_receiver();

    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<Fp>(batch_size*n*11 + batch_size*n*2);
    let mut fcom_p_3 = FComProver::<Fp>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params, lpn_extend_params, a).unwrap();

    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*n*3 + batch_size*n*2);
    let mut fcom_p_2 = FComProver::<F256b>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();
    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*n*2);
    let mut fcom_v_2 = FComVerifier::<F256b>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();

    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<F256b>(batch_size*n*2 + 512);
    let mut fcom_k = FComProver::<F256b>::init_from_previous_setup_receiver(channel, rng, fcom_k_params, fcom_k_params_extend, a).unwrap();

    let (lpn_share_setup_params, lpn_share_extend_params) = choose_lpn_parameters::<F256b>(batch_size*n);
    let fcom_k_delta = FComProver::<F256b>::init_from_previous_setup_receiver(channel, rng, lpn_share_setup_params, lpn_share_extend_params, a).unwrap();

    let mut da_bits: Vec<(crate::dabits::OPRFExtensionSharing<F256b>, Vec<crate::dabits::OPRFSharing<Fp>>)> = Vec::new();

    if n*batch_size > 1<<21{
        let iterations = (n*batch_size) / (1<<20);
        for i in 0..iterations{
            let mut output_size = 1<<20;
            if i == iterations -1 {
                output_size = n*batch_size - (iterations-1)*(1<<20);
            }
            let da_bits_part: Vec<(crate::dabits::OPRFSharing<F256b>, crate::dabits::OPRFSharing<Fp>)> = dabit_client(
                1<<20, 
                &mut fcom_p_2,
                &mut fcom_v_2,
                &mut fcom_p_3,
                &mut fcom_v_3,
                channel, 
                rng,
                OPRFSetting::RevealOutput);

            for j in 0..(output_size/n){
                let mut f3_parts = Vec::with_capacity(n);
                f3_parts.push( da_bits_part[j*n].1);

                let mut value: F256b = da_bits_part[j*n].0.0.into();
                let mut mac = da_bits_part[j*n].0.1.mac();
                let mut key = da_bits_part[j*n].0.2.mac();
                let mut pow = F256b::ONE;
                for k in 1..n{
                    pow.shift_left_once();
                    value += da_bits_part[k +j*n].0.0 * pow;
                    mac += da_bits_part[k +j*n].0.1.mac().pow_mul(k);
                    key += da_bits_part[k +j*n].0.2.mac().pow_mul(k);
                    f3_parts.push( da_bits_part[k + j*n].1);
                }
                let extension_sharing = OPRFExtensionSharing(value, mac, key);
                da_bits.push((extension_sharing, f3_parts));
            }

        }
    } else {
        let da_bits_part = dabit_client(
            batch_size*n, 
            &mut fcom_p_2,
            &mut fcom_v_2,
            &mut fcom_p_3,
            &mut fcom_v_3,
            channel, 
            rng,
            OPRFSetting::RevealOutput);

        for j in 0..(batch_size*n/n){
            let mut f3_parts = Vec::with_capacity(n);
            f3_parts.push( da_bits_part[j*n].1);

            let mut value: F256b = da_bits_part[j*n].0.0.into();
            let mut mac = da_bits_part[j*n].0.1.mac();
            let mut key = da_bits_part[j*n].0.2.mac();
            let mut pow = F256b::ONE;
            for k in 1..n{
                pow.shift_left_once();
                value += da_bits_part[k +j*n].0.0 * pow;
                mac += da_bits_part[k +j*n].0.1.mac().pow_mul(k);
                key += da_bits_part[k +j*n].0.2.mac().pow_mul(k);
                f3_parts.push( da_bits_part[k + j*n].1);
            }
            let extension_sharing = OPRFExtensionSharing(value, mac, key);
            da_bits.push((extension_sharing, f3_parts));
        }

    }


    let mut encodings: (Vec<MacProver<F256b>>, Vec<MacProver<Fp>>) = (Vec::new(), Vec::new());
    if n*batch_size > 1<<21{
        let interations = (n*batch_size) / (1<<20);
        for _ in 0..(interations-1){
            let encoding_part: (Vec<MacProver<F256b>>, Vec<MacProver<Fp>>) = code_candidate_client(
                1<<20, 
                &mut fcom_p_2,
                &mut fcom_p_3,
                channel, 
                rng,
                &CodeType::Large);
            encodings.0.extend(encoding_part.0);
            encodings.1.extend(encoding_part.1);
        }
        let encoding_part: (Vec<MacProver<F256b>>, Vec<MacProver<Fp>>) = code_candidate_client(
            n*batch_size - (interations-1)*(1<<20), 
            &mut fcom_p_2,
            &mut fcom_p_3,
            channel, 
            rng,
            &CodeType::Large);
            encodings.0.extend(encoding_part.0);
            encodings.1.extend(encoding_part.1);
    } else {
        encodings = code_candidate_client(
            batch_size*n, 
            &mut fcom_p_2,
            &mut fcom_p_3,
            channel, 
            rng,
            &CodeType::Large);
    }

    let (value, mac_delta) = lift_prover_vole(&mut fcom_k, channel, rng, n);
    let diff = value - fcom_v_2.get_delta();
    channel.write_serializable(&diff).unwrap();
    channel.flush().unwrap();

    let mut k_key = lift_verifier_vole(&mut fcom_v_2, channel, rng, n);
    let d: F256b = channel.read_serializable().unwrap();
    k_key = k_key - fcom_v_2.get_delta() * d;

    weak_equality_first(channel, rng, &mut [mac_delta - k_key].into(), &mut fcom_p_2).unwrap();

    return (da_bits, encodings, fcom_p_2, fcom_v_2, fcom_v_3, fcom_p_3, fcom_k, fcom_k_delta, mac_delta);
}

pub fn preprocess_server<Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    batch_size: usize,
) -> (Vec<(crate::dabits::OPRFExtensionSharing<F256b>, Vec<crate::dabits::OPRFSharing<Fp>>)>, 
      (Vec<MacVerifier<F256b>>, Vec<MacVerifier<Fp>>), FComProver<F256b>,
      FComVerifier<F256b>, FComProver<Fp>, FComVerifier<Fp>, FComVerifier<F256b>, FComVerifier<F256b>, F256b)
where 
Fp::PrimeField: TryFrom<u8>
{
    let n = 256;
    
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<Fp>(batch_size*n*20);
    let mut fcom_p_3 = FComProver::<Fp>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    let a = fcom_p_3.extract_svole_sender();
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<Fp>(batch_size*n*11 + batch_size*n*2);
    let mut fcom_v_3 = FComVerifier::<Fp>::init_from_previous_setup_sender(channel, rng, lpn_setup_params, lpn_extend_params, a).unwrap();

    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*n*3 + batch_size*n*2);
    let mut fcom_v_2 = FComVerifier::<F256b>::init_from_previous_setup_sender(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();
    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*n*2);
    let mut fcom_p_2 = FComProver::<F256b>::init_from_previous_setup_sender(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a ).unwrap();

    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<F256b>(batch_size*n*2 + 512);
    let mut fcom_k: FComVerifier<F256b> = FComVerifier::<F256b>::init_from_previous_setup_sender(channel, rng, fcom_k_params, fcom_k_params_extend, a).unwrap();

    let (lpn_share_setup_params, lpn_share_extend_params) = choose_lpn_parameters::<F256b>(batch_size*n);
    let fcom_k_delta = FComVerifier::<F256b>::init_with_picked_delta_and_ot(channel, rng, lpn_share_setup_params, lpn_share_extend_params, fcom_k.get_delta()* fcom_v_2.get_delta(), a).unwrap();

    let mut da_bits: Vec<(crate::dabits::OPRFExtensionSharing<F256b>, Vec<crate::dabits::OPRFSharing<Fp>>)> = Vec::new();
    
    if n*batch_size > 1<<21{
        let iterations = (n*batch_size) / (1<<20);
        for i in 0..iterations{
            let mut output_size = 1<<20;
            if i == iterations -1 {
                output_size = n*batch_size - (iterations-1)*(1<<20);
            }
            let da_bits_part: Vec<(crate::dabits::OPRFSharing<F256b>, crate::dabits::OPRFSharing<Fp>)> = dabit_server(
                output_size, 
                &mut fcom_p_2,
                &mut fcom_v_2,
                &mut fcom_p_3,
                &mut fcom_v_3,
                channel, 
                rng,
                OPRFSetting::RevealOutput);
            for j in 0..(output_size/n){
                let mut f3_parts = Vec::with_capacity(n);
                f3_parts.push( da_bits_part[j*n].1);

                let mut value: F256b = da_bits_part[j*n].0.0.into();
                let mut mac = da_bits_part[j*n].0.1.mac();
                let mut key = da_bits_part[j*n].0.2.mac();
                let mut pow = F256b::ONE;
                for k in 1..n{
                    pow.shift_left_once();
                    value += da_bits_part[k +j*n].0.0 * pow;
                    mac += da_bits_part[k +j*n].0.1.mac().pow_mul(k);
                    key += da_bits_part[k +j*n].0.2.mac().pow_mul(k);
                    f3_parts.push( da_bits_part[k + j*n].1);
                }
                let extension_sharing = OPRFExtensionSharing(value, mac, key);
                da_bits.push((extension_sharing, f3_parts));
            }
        }
    } else {
        let da_bits_part = dabit_server(
            batch_size*n, 
            &mut fcom_p_2,
            &mut fcom_v_2,
            &mut fcom_p_3,
            &mut fcom_v_3,
            channel, 
            rng,
            OPRFSetting::RevealOutput);
        for j in 0..(batch_size*n/n){
            let mut f3_parts = Vec::with_capacity(n);
            f3_parts.push( da_bits_part[j*n].1);

            let mut value: F256b = da_bits_part[j*n].0.0.into();
            let mut mac = da_bits_part[j*n].0.1.mac();
            let mut key = da_bits_part[j*n].0.2.mac();
            let mut pow = F256b::ONE;
            for k in 1..n{
                pow.shift_left_once();
                value += da_bits_part[k +j*n].0.0 * pow;
                mac += da_bits_part[k +j*n].0.1.mac().pow_mul(k);
                key += da_bits_part[k +j*n].0.2.mac().pow_mul(k);
                f3_parts.push( da_bits_part[k + j*n].1);
            }
            let extension_sharing = OPRFExtensionSharing(value, mac, key);
            da_bits.push((extension_sharing, f3_parts));
        }
    }

    let mut encodings = (Vec::new(), Vec::new());
    if n*batch_size > 1<<21{
        let interations = (n*batch_size) / (1<<20);
        for _ in 0..(interations-1){
            let encoding_part: (Vec<MacVerifier<F256b>>, Vec<MacVerifier<Fp>>) = code_candidate_server(
                1<<20, 
                &mut fcom_v_2,
                &mut fcom_v_3,
                channel, 
                rng,
                &CodeType::Large);
            encodings.0.extend(encoding_part.0);
            encodings.1.extend(encoding_part.1);
        }
        let encoding_part: (Vec<MacVerifier<F256b>>, Vec<MacVerifier<Fp>>) = code_candidate_server(
            n*batch_size - (interations-1)*(1<<20), 
            &mut fcom_v_2,
            &mut fcom_v_3,
            channel, 
            rng,
            &CodeType::Large);
            encodings.0.extend(encoding_part.0);
            encodings.1.extend(encoding_part.1);
    }else{
        encodings = code_candidate_server(
            batch_size*n, 
            &mut fcom_v_2,
            &mut fcom_v_3,
            channel, 
            rng,
            &CodeType::Large);
    }
    
    let mut key_delta = lift_verifier_vole(&mut fcom_k, channel, rng, n);
    let d: F256b = channel.read_serializable().unwrap();
    key_delta = key_delta - fcom_k.get_delta() * d;

    let (value, mac_k) = lift_prover_vole(&mut fcom_p_2, channel, rng, n);
    let diff = value - fcom_k.get_delta();
    channel.write_serializable(&diff).unwrap();
    channel.flush().unwrap();

    weak_equality_second(channel, rng, &mut [mac_k-key_delta].into(), &mut fcom_v_2).unwrap();

    return (da_bits, encodings, fcom_p_2, fcom_v_2, fcom_p_3, fcom_v_3, fcom_k, fcom_k_delta, key_delta);
}


pub fn w_prf_client_commit_to_input<C: AbstractChannel, RNG: CryptoRng + Rng>(
    inputs: &Vec<F256b>,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    fcom_k: &mut FComProver<F256b>,
) -> Vec<F256b>{
    let n = 256;

    let mut value_client_share = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let (value_input, y_0) = lift_prover_vole(fcom_k, channel, rng, n);
        let x = inputs[j];
        let diff = value_input - x;
        channel.write_serializable(&diff).unwrap();
        value_client_share.push(y_0);
    }
    channel.flush().unwrap();
    value_client_share
}

pub fn w_prf_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
    inputs: Vec<F256b>,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: &mut [[F3;256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_v_3: &mut FComVerifier<F82t>,
    fcom_k: &mut FComProver<F256b>,
    fcom_k_delta: &mut FComProver<F256b>,
    mac_delta: F256b,
) -> Vec<F3>{
    let value_client_share = w_prf_client_commit_to_input(&inputs, batch_size, channel, rng, fcom_k);
    w_prf_client_with_commitment(inputs, batch_size, channel, rng, b, b_tables, da_bits, fcom_p_2, fcom_v_2, fcom_v_3, fcom_k, fcom_k_delta, value_client_share, mac_delta)
}

pub fn w_prf_client_with_commitment<C: AbstractChannel, RNG: CryptoRng + Rng>(
    inputs: Vec<F256b>,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: &mut [[F3;256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_v_3: &mut FComVerifier<F82t>,
    fcom_k: &mut FComProver<F256b>,
    fcom_k_delta: &mut FComProver<F256b>,
    input_com: Vec<F256b>,
    mac_delta: F256b,
) -> Vec<F3>{
    let n = 256;
    let t = 82;

    assert_eq!(inputs.len(), batch_size, "Inputs length does not match batch size");

    let (value_client_share, mac_client_share, key_server_share) = authenticated_vole_client(inputs, batch_size, channel, rng, fcom_p_2, fcom_v_2, fcom_k, fcom_k_delta, input_com, mac_delta, n);

    let c = open_c_client(batch_size, channel, da_bits, fcom_v_2, value_client_share, mac_client_share, key_server_share);
    
    let out = convert_and_reveal_client(batch_size, channel, b, b_tables, da_bits, fcom_v_3, n, t, c);
    out
}

pub fn secret_shared_w_prf_client_with_commitment<C: AbstractChannel, RNG: CryptoRng + Rng>(
    inputs: Vec<F256b>,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: &mut [[F3;256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_v_3: &mut FComVerifier<F82t>,
    fcom_k: &mut FComProver<F256b>,
    fcom_k_delta: &mut FComProver<F256b>,
    input_com: Vec<F256b>,
    mac_delta: F256b,
) -> Vec<OPRFSharing<F82t>>{
    let n = 256;
    let t = 82;

    assert_eq!(inputs.len(), batch_size, "Inputs length does not match batch size");

    let (value_client_share, mac_client_share, key_server_share) = authenticated_vole_client(inputs, batch_size, channel, rng, fcom_p_2, fcom_v_2, fcom_k, fcom_k_delta, input_com, mac_delta, n);

    let c = open_c_client(batch_size, channel, da_bits, fcom_v_2, value_client_share, mac_client_share, key_server_share);
    
    let out = convert_client(batch_size, b, b_tables, da_bits, fcom_v_3, n, t, c);
    out
}

fn convert_and_reveal_client<C: AbstractChannel>(batch_size: usize, channel: &mut C, b: &mut [[F3; 256]; 82], b_tables: &mut Vec<F3>, da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>, fcom_v_3: &mut FComVerifier<F82t>, n: usize, t: usize, c: Vec<F256b>) -> Vec<F3> {
    // Convert the mask to F3 and apply B
    let mut out_value_share: Vec<F3> = Vec::with_capacity(batch_size*t);
    let mut out_key_server_share: Vec<MacVerifier<F82t>> = Vec::with_capacity(batch_size*t);
    let mut c_bit_string = [F3::ZERO; 256];
    let mut value_client_share_f3 = [F3::ZERO; 256];
    for j in 0..batch_size{
        let mut key_server_share_f3 = Vec::with_capacity(n);
    
        for i in 0..128{
            let c_i = (c[j].low >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i] = c_i;
            let c_i = (c[j].high >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i + 128] = c_i;
        }

        let da_bit_i = &da_bits[j].1;
        for i in 0..n{
            let da_bit_i = da_bit_i[i];


            let c_i: F3 = c_bit_string[i];
            let val = da_bit_i.0 + c_i * da_bit_i.0;
            value_client_share_f3[i] = val;
            let key = -(c_i * fcom_v_3.get_delta()) + da_bit_i.2.mac() + c_i*da_bit_i.2.mac();
            key_server_share_f3.push(key);

        }

        let outs = compute_row_using_table(&b_tables, value_client_share_f3);
        for i in 0..t{
            out_value_share.push(outs[i]);
        }
        for i in 0..t{
            let key = F82t::compute_vector(b[i], &key_server_share_f3);
            out_key_server_share.push(MacVerifier::new(key));
        }
    }

    let mut out_values_server = Vec::with_capacity(batch_size*t);
    fcom_v_3.open(channel, &out_key_server_share, &mut out_values_server).unwrap();

    let mut out = Vec::with_capacity(t*batch_size);
    for i in 0..t*batch_size{
        let value = out_value_share[i] + out_values_server[i];
        out.push(value);
    }
    out
}

fn convert_client(batch_size: usize, b: &mut [[F3; 256]; 82], b_tables: &mut Vec<F3>, da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>, fcom_v_3: &mut FComVerifier<F82t>, n: usize, t: usize, c: Vec<F256b>) 
-> Vec<OPRFSharing<F82t>> {
    // Convert the mask to F3 and apply B
    let mut c_bit_string = [F3::ZERO; 256];
    let mut value_client_share_f3 = [F3::ZERO; 256];
    
    let mut out_shares = Vec::with_capacity(batch_size*t);
    
    for j in 0..batch_size{
        let mut mac_server_share_f3 = Vec::with_capacity(n);
        let mut key_server_share_f3 = Vec::with_capacity(n);
    
        for i in 0..128{
            let c_i = (c[j].low >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i] = c_i;
            let c_i = (c[j].high >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i + 128] = c_i;
        }

        let da_bit_i = &da_bits[j].1;
        for i in 0..n{
            let da_bit_i = da_bit_i[i];


            let c_i: F3 = c_bit_string[i];
            let val = da_bit_i.0 + c_i * da_bit_i.0;
            value_client_share_f3[i] = val;
            let mac = da_bit_i.1.mac() + c_i*da_bit_i.1.mac();
            mac_server_share_f3.push(mac);
            let key = -(c_i * fcom_v_3.get_delta()) + da_bit_i.2.mac() + c_i*da_bit_i.2.mac();
            key_server_share_f3.push(key);

        }

        let outs = compute_row_using_table(&b_tables, value_client_share_f3);
        for i in 0..t{
            let mac = F82t::compute_vector(b[i], &mac_server_share_f3);
            let key = F82t::compute_vector(b[i], &key_server_share_f3);
            let share = OPRFSharing{
                0: outs[i],
                1: MacProver::new(outs[i], mac),
                2: MacVerifier::new(key),
            };
            out_shares.push(share);
        }
    }
    
    out_shares
}

fn open_c_client<C: AbstractChannel>
(batch_size: usize, channel: &mut C, da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>, fcom_v_2: &mut FComVerifier<F256b>, value_client_share: Vec<F256b>, mac_client_share: Vec<F256b>, key_server_share: Vec<F256b>) -> Vec<F256b> {
    // Convert shares to F3
    // Prepare dabits for conversion
    let mut dabit_2_values = Vec::with_capacity(batch_size);
    let mut dabit_2_mac = Vec::with_capacity(batch_size);
    let mut dabit_2_keys = Vec::with_capacity(batch_size);

    for j in 0..batch_size{
        dabit_2_values.push(da_bits[j].0.0);
        dabit_2_mac.push(da_bits[j].0.1);
        dabit_2_keys.push(da_bits[j].0.2);
    }
    
    // Open the masked share
    let mut c_to_open = Vec::with_capacity(batch_size);
    let mut c_macs = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_c = dabit_2_values[j] + value_client_share[j];
        let c_mac = dabit_2_mac[j] + mac_client_share[j];
        c_to_open.push(c_c);
        c_macs.push(c_mac);
    };
    open_extension_mac_prover(channel, &c_to_open, &c_macs).unwrap();


    let mut c_keys = Vec::with_capacity(batch_size);
    let mut c_s_values = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_s_key = dabit_2_keys[j] + key_server_share[j];
        c_keys.push(c_s_key);
    }
    open_extension_mac_verifier(channel, &c_keys, fcom_v_2.get_delta(), &mut c_s_values).unwrap();


    let mut c = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let val = c_to_open[j] + c_s_values[j];
        c.push(val);
    }
    c
}

fn authenticated_vole_client<C: AbstractChannel, RNG: CryptoRng + Rng>
(inputs: Vec<F256b>, batch_size: usize, channel: &mut C, rng: &mut RNG, fcom_p_2: &mut FComProver<F256b>, fcom_v_2: &mut FComVerifier<F256b>, fcom_k: &mut FComProver<F256b>, fcom_k_delta: &mut FComProver<F256b>, input_com: Vec<F256b>, mac_delta: F256b, n: usize) -> (Vec<F256b>, Vec<F256b>, Vec<F256b>) {
    // Online phase
    let mut value_client_share = Vec::with_capacity(batch_size);
    let mut mac_client_share = Vec::with_capacity(batch_size);
    let mut key_server_share = Vec::with_capacity(batch_size);
    
    // Checks
    let chi = F256b::random(rng);
    let mut qs_prover = QSStateProver::<F256b, 2>::init_with_chi(chi);
    let s: F256b = F256b::random(rng);

    for j in 0..batch_size{        
        let x = inputs[j];
        // Authenticate client share
        let (value_c_share, z_0) = lift_prover_vole(fcom_k_delta, channel, rng, n);
        let diff = value_c_share - x;
        channel.write_serializable(&diff).unwrap();
    
        // Authenticate server share
        let (value_s_share, m_0) = lift_prover_vole(fcom_k, channel, rng, n);
        let product = x * fcom_v_2.get_delta();
        let diff = value_s_share - product;
        channel.write_serializable(&diff).unwrap();

        value_client_share.push(input_com[j]);
        mac_client_share.push(z_0);
        key_server_share.push(fcom_v_2.get_delta() * input_com[j] - m_0);

        let mut delta: HDMacProver<F256b, 2> = HDMacProver{poly: GeneralPolynomial{constant: -mac_delta, coefficients: smallvec![fcom_v_2.get_delta().into()]}, qs_degree: 1};
        let y: HDMacProver<F256b, 2> = HDMacProver{poly: GeneralPolynomial{constant: -input_com[j], coefficients: smallvec![x.into()]}, qs_degree: 1};
        let delta_y: HDMacProver<F256b, 2> = HDMacProver{poly: GeneralPolynomial{constant: -m_0, coefficients: smallvec![product.into()]}, qs_degree: 1};
        delta.mul_assign(&y);
        delta.sub_assign(&delta_y);
        qs_prover.check_zero(&delta);
    }
    qs_prover.finalize(channel, rng, fcom_k).unwrap();

    {
        // One extra commitment for authentication
        let (value, e) = lift_prover_vole(fcom_k, channel, rng, n);
        let diff = value - s;
        channel.write_serializable(&diff).unwrap();

        let (value, t) = lift_prover_vole(fcom_p_2, channel, rng, n);
        let diff = value - e;
        channel.write_serializable(&diff).unwrap();

        let (value, e_bar) = lift_prover_vole(fcom_k_delta, channel, rng, n);
        let diff = value - s;
        channel.write_serializable(&diff).unwrap();
        channel.flush().unwrap();
    
        weak_equality_second(channel, rng, &mut [e_bar - t].into(), fcom_v_2).unwrap();
    }
    (value_client_share, mac_client_share, key_server_share)
}

pub fn w_prf_server_commit_to_input<C: AbstractChannel, RNG: CryptoRng + Rng>(
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    fcom_k: &mut FComVerifier<F256b>
) -> Vec<F256b> {
    let n = 256;
    
    let mut value_server_share = Vec::with_capacity(batch_size);
    for _ in 0..batch_size{
        // Multiply input
        let mut y_1 = lift_verifier_vole(fcom_k, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        y_1 = y_1 - fcom_k.get_delta() * d;
        value_server_share.push(y_1);
    }
    value_server_share
}

pub fn w_prf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    key: F256b,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: [[F3;256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_p_3: &mut FComProver<F82t>,
    fcom_k: &mut FComVerifier<F256b>,
    fcom_k_delta: &mut FComVerifier<F256b>,
    key_delta: F256b,
) -> () {
    let value_server_share = w_prf_server_commit_to_input(batch_size, channel, rng, fcom_k);
    w_prf_server_with_commitment(key, batch_size, channel, rng, b, b_tables, da_bits, fcom_p_2, fcom_v_2, fcom_p_3, fcom_k, fcom_k_delta, value_server_share, key_delta);
}

pub fn secret_shared_w_prf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    key: F256b,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: [[F3;256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_k: &mut FComVerifier<F256b>,
    fcom_k_delta: &mut FComVerifier<F256b>,
    key_delta: F256b,
) -> Vec<OPRFSharing<F82t>> {
    let value_server_share = w_prf_server_commit_to_input(batch_size, channel, rng, fcom_k);
    secret_shared_w_prf_server_with_commitment(key, batch_size, channel, rng, b, b_tables, da_bits, fcom_p_2, fcom_v_2, fcom_k, fcom_k_delta, value_server_share, key_delta)
}

pub fn w_prf_server_with_commitment<C: AbstractChannel, RNG: CryptoRng + Rng>(
    _key: F256b,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: [[F3; 256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_p_3: &mut FComProver<F82t>,
    fcom_k: &mut FComVerifier<F256b>,
    fcom_k_delta: &mut FComVerifier<F256b>,
    value_server_share: Vec<F256b>,
    key_delta: F256b,
) -> (){
    let n = 256;
    let t = 82;

    let (mac_server_share, key_client_share) = authenticate_vole_server(batch_size, channel, rng, fcom_p_2, fcom_v_2, fcom_k, fcom_k_delta, &value_server_share, key_delta, n);

    let c = open_c_server(batch_size, channel, da_bits, fcom_v_2, value_server_share, mac_server_share, key_client_share);

    convert_and_reveal_server(batch_size, channel, b, b_tables, da_bits, fcom_p_3, n, t, c);
}

pub fn secret_shared_w_prf_server_with_commitment<C: AbstractChannel, RNG: CryptoRng + Rng>(
    _key: F256b,
    batch_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    b: [[F3; 256];82],
    b_tables: &mut Vec<F3>,
    da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    fcom_p_2: &mut FComProver<F256b>,
    fcom_v_2: &mut FComVerifier<F256b>,
    fcom_k: &mut FComVerifier<F256b>,
    fcom_k_delta: &mut FComVerifier<F256b>,
    value_server_share: Vec<F256b>,
    key_delta: F256b,
) -> Vec<OPRFSharing<F82t>>{
    let n = 256;
    let t = 82;

    let (mac_server_share, key_client_share) = authenticate_vole_server(batch_size, channel, rng, fcom_p_2, fcom_v_2, fcom_k, fcom_k_delta, &value_server_share, key_delta, n);

    let c = open_c_server(batch_size, channel, da_bits, fcom_v_2, value_server_share, mac_server_share, key_client_share);

    convert_server(batch_size, b, b_tables, da_bits, n, t, c)
}

fn convert_and_reveal_server<C: AbstractChannel>(batch_size: usize, channel: &mut C, b: [[F3; 256]; 82], b_tables: &mut Vec<F3>, da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>, fcom_p_3: &mut FComProver<F82t>, n: usize, t: usize, c: Vec<F256b>) {
    // Convert the mask to F3
    let mut out_value_share: Vec<MacProver<F82t>> = Vec::with_capacity(batch_size*t);
    let mut value_server_share_f3 = [F3::ZERO; 256];
    let mut c_bit_string = [F3::ZERO; 256];
    for j in 0..batch_size{
        let mut mac_server_share_f3 = Vec::with_capacity(n);
    
        for i in 0..128{
            let c_i = (c[j].low >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i] = c_i;
            let c_i = (c[j].high >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i + 128] = c_i;
        }
    
        let da_bit_i = &da_bits[j].1;
        for i in 0..n{
            let da_bit_i = da_bit_i[i];

            let c_i: F3 = c_bit_string[i];
            let val = c_i + da_bit_i.0 + c_i * da_bit_i.0;
            value_server_share_f3[i] = val;

            let mac = da_bit_i.1.mac() + c_i * da_bit_i.1.mac();
            mac_server_share_f3.push(mac);
        }
    
        let outs = compute_row_using_table(&b_tables, value_server_share_f3);

        // Multiply the sharing with B
        for i in 0..t{
            let mac = F82t::compute_vector(b[i], &mac_server_share_f3);
            out_value_share.push(MacProver::new(outs[i], mac));
        }
    }

    fcom_p_3.open(channel, &out_value_share).unwrap();
}

fn convert_server(batch_size: usize, b: [[F3; 256]; 82], b_tables: &mut Vec<F3>, da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>, n: usize, t: usize, c: Vec<F256b>) 
-> Vec<OPRFSharing<F82t>>{
    // Convert the mask to F3
    let mut value_server_share_f3 = [F3::ZERO; 256];
    let mut c_bit_string = [F3::ZERO; 256];
    let mut out_shares = Vec::with_capacity(batch_size*t);
    for j in 0..batch_size{
        let mut mac_server_share_f3 = Vec::with_capacity(n);
        let mut key_server_share_f3 = Vec::with_capacity(n);
    
        for i in 0..128{
            let c_i = (c[j].low >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i] = c_i;
            let c_i = (c[j].high >> i) & 1;
            let c_i: F3 = F3{msb: 0, lsb: c_i as u8};
            c_bit_string[i + 128] = c_i;
        }
    
        let da_bit_i = &da_bits[j].1;
        for i in 0..n{
            let da_bit_i = da_bit_i[i];

            let c_i: F3 = c_bit_string[i];
            let val = c_i + da_bit_i.0 + c_i * da_bit_i.0;
            value_server_share_f3[i] = val;

            let mac = da_bit_i.1.mac() + c_i * da_bit_i.1.mac();
            mac_server_share_f3.push(mac);

            let key = da_bit_i.2.mac() + c_i * da_bit_i.2.mac();
            key_server_share_f3.push(key);

        }
    
        let outs = compute_row_using_table(&b_tables, value_server_share_f3);

        // Multiply the sharing with B
        for i in 0..t{
            let mac = F82t::compute_vector(b[i], &mac_server_share_f3);
            let key = F82t::compute_vector(b[i], &key_server_share_f3);
            let share = OPRFSharing{
                0: outs[i],
                1: MacProver::new(outs[1], mac),
                2: MacVerifier::new(key)
            };
            out_shares.push(share);
        }
    }
    out_shares
}

fn open_c_server<C: AbstractChannel>(batch_size: usize, channel: &mut C, da_bits: &mut Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>, fcom_v_2: &mut FComVerifier<F256b>, value_server_share: Vec<F256b>, mac_server_share: Vec<F256b>, key_client_share: Vec<F256b>) -> Vec<F256b> {
    // Conver share to F3
    // Prepare dabits for conversion
    let mut dabit_2_values = Vec::with_capacity(batch_size);
    let mut dabit_2_mac = Vec::with_capacity(batch_size);
    let mut dabit_2_keys = Vec::with_capacity(batch_size);

    for j in 0..batch_size{
        dabit_2_values.push(da_bits[j].0.0);
        dabit_2_mac.push(da_bits[j].0.1);
        dabit_2_keys.push(da_bits[j].0.2);
    }
    
    // Open the masked share
    let mut c_keys = Vec::with_capacity(batch_size);
    let mut c_c_values = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_c_key = dabit_2_keys[j] + key_client_share[j];
        c_keys.push(c_c_key);
    }
    open_extension_mac_verifier(channel, &c_keys, fcom_v_2.get_delta(), &mut c_c_values).unwrap();


    let mut c_to_open = Vec::with_capacity(batch_size);
    let mut c_macs = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let c_s = dabit_2_values[j] + value_server_share[j];
        let c_s_mac = dabit_2_mac[j] + mac_server_share[j];
        c_to_open.push(c_s);
        c_macs.push(c_s_mac);
    }
    open_extension_mac_prover(channel, &c_to_open, &c_macs).unwrap();

    let mut c = Vec::with_capacity(batch_size);
    for j in 0..batch_size{
        let val = c_to_open[j] + c_c_values[j];
        c.push(val);
    }
    c
}

fn authenticate_vole_server<C: AbstractChannel, RNG: CryptoRng + Rng>(batch_size: usize, channel: &mut C, rng: &mut RNG, fcom_p_2: &mut FComProver<F256b>, fcom_v_2: &mut FComVerifier<F256b>, fcom_k: &mut FComVerifier<F256b>, fcom_k_delta: &mut FComVerifier<F256b>, value_server_share: &Vec<F256b>, key_delta: F256b, n: usize) -> (Vec<F256b>, Vec<F256b>) {
    let mut mac_server_share = Vec::with_capacity(batch_size);
    let mut key_client_share = Vec::with_capacity(batch_size);

    let delta =  fcom_k.get_delta();
    let chi = F256b::random(rng);
    let mut qs_verifier = QSStateVerifier::<F256b>::init_with_delta_and_chi(delta, chi);

    for j in 0..batch_size{
        // authenticate client share
        let mut z_1 = lift_verifier_vole(fcom_k_delta, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        z_1 = z_1 - fcom_k_delta.get_delta() * d;
    
        // authenticate server share
        let mut m_1 = lift_verifier_vole(fcom_k, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        m_1 = m_1 - fcom_k.get_delta() * d;
    
        mac_server_share.push(m_1);
        key_client_share.push(fcom_v_2.get_delta() * value_server_share[j] - z_1);      
    
        let mut delta: HDMacVerifier<F256b> = HDMacVerifier{mac: -key_delta, qs_degree: 1};
        let y: HDMacVerifier<F256b> = HDMacVerifier{mac: -value_server_share[j], qs_degree: 1};
        let delta_y: HDMacVerifier<F256b> = HDMacVerifier{mac: -m_1, qs_degree: 1};
        delta.mul_assign(&y);
        delta.sub_assign(fcom_k.get_delta(), &delta_y);
        qs_verifier.check_zero(&delta);
    }
    qs_verifier.finalize_and_verify::<C, RNG, 2>(channel, rng, fcom_k).unwrap();
    {
        let mut f = lift_verifier_vole(fcom_k, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        f = f - fcom_k.get_delta() * d;

        let mut u = lift_verifier_vole(fcom_v_2, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        u = u - fcom_v_2.get_delta() * d;

        let mut f_bar = lift_verifier_vole(fcom_k_delta, channel, rng, n);
        let d: F256b = channel.read_serializable().unwrap();
        f_bar = f_bar - fcom_k_delta.get_delta() * d;

        weak_equality_first(channel, rng, &mut [u -f_bar + fcom_v_2.get_delta()*f].into(), fcom_p_2).unwrap();
    }
    (mac_server_share, key_client_share)
}

pub fn w_prf_clear(
    key: F256b,
    input: F256b,
    b: [[F3; 256];82],
) -> Vec<F3>{
    let product = key * input;

    //Decompose product into F3
    let mut product_decompose = Vec::new();

    for i in 0..128{
        let c_i = (product.low >> i) & 1;
        let c_i: F3 = F3::try_from(c_i).unwrap();
        product_decompose.push(c_i);
    }
    for i in 0..128{
        let c_i = (product.high >> i) & 1;
        let c_i: F3 = F3::try_from(c_i).unwrap();
        product_decompose.push(c_i);
    }

    let mut out = Vec::new();
    for i in 0..82{
        let mut value = F3::ZERO;

        for j in 0..256{
            value = value + b[i][j]*product_decompose[j];
        }
        out.push(value);
    }
    out
}

#[cfg(test)]
mod test{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    
    use rand::SeedableRng;
    use scuttlebutt::{field::F64b, AesRng, Block, Channel};

    use crate::matrix_util::generate_precompute_tables;

    use super::*;

    #[test]
    fn test_w_prf_single(){
        let seed = Block::from([0; 16]);

        let mut b_rng = AesRng::from_seed(seed);
        let mut b: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b[i][j] = F3::random(&mut b_rng);
            }
        }

        let mut bc = generate_precompute_tables(b);
        let mut bs = bc.clone();

        let input = F256b::from(F64b::random(&mut b_rng));

        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let inputs = vec![input];
            let batch_size = inputs.len();
            
            let (mut da_bits, _, mut fcom_p_2, mut fcom_v_2, mut fcom_v_3, _, mut fcom_k, mut fcom_k_delta, mac_delta) = preprocess_client( &mut channel, &mut rng, batch_size);
            let fk_x = w_prf_client(inputs, 1, &mut channel, &mut rng, &mut b, &mut bc, &mut da_bits, &mut fcom_p_2, &mut fcom_v_2, &mut fcom_v_3, &mut fcom_k, &mut fcom_k_delta, mac_delta);
            fk_x
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let batch_size = 1;
        let (mut da_bits, _, mut fcom_p_2, mut fcom_v_2, mut fcom_p_3, _, mut fcom_k, mut fcom_k_delta, key_delta) = preprocess_server(&mut channel, &mut rng, batch_size);
        let key = fcom_k.get_delta();
        w_prf_server(key, batch_size, &mut channel, &mut rng, b, &mut bs, &mut da_bits, &mut fcom_p_2, &mut fcom_v_2, &mut fcom_p_3, &mut fcom_k, &mut fcom_k_delta, key_delta);
        let fk_x = handle.join().unwrap();

        let clear = w_prf_clear(key, input, b);
        for i in 0..82{
            assert_eq!(fk_x[i], clear[i], "Output of wPRF does not match clear output at index {i}");
        }

    }

    #[test]
    fn test_w_prf_batch(){
        let seed = Block::from([0; 16]);

        let mut b_rng = AesRng::from_seed(seed);
        let mut b: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b[i][j] = F3::random(&mut b_rng);
            }
        }

        let mut bc = generate_precompute_tables(b);
        let mut bs = bc.clone();

        let inputs = vec![F256b::random(&mut b_rng), F256b::random(&mut b_rng), F256b::random(&mut b_rng), F256b::random(&mut b_rng)];
        let inputs_tread = inputs.clone();
        let len = inputs.len();
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let batch_size = inputs_tread.len();
            
            let (mut da_bits, _, mut fcom_p_2, mut fcom_v_2, mut fcom_v_3, _, mut fcom_k, mut fcom_k_delta, mac_delta) = preprocess_client( &mut channel, &mut rng, batch_size);
            let fk_x = w_prf_client(inputs_tread, batch_size, &mut channel, &mut rng, &mut b, &mut bc, &mut da_bits, &mut fcom_p_2, &mut fcom_v_2, &mut fcom_v_3, &mut fcom_k, &mut fcom_k_delta, mac_delta);
            fk_x
        });
        
        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        
        let batch_size = 4;
        let (mut da_bits, _, mut fcom_p_2, mut fcom_v_2, mut fcom_p_3, _, mut fcom_k, mut fcom_k_delta, key_delta) = preprocess_server(&mut channel, &mut rng, batch_size);
        let key = fcom_k.get_delta();
        w_prf_server(key, batch_size, &mut channel, &mut rng, b, &mut bs, &mut da_bits, &mut fcom_p_2, &mut fcom_v_2, &mut fcom_p_3, &mut fcom_k, &mut fcom_k_delta, key_delta);
        let fk_x = handle.join().unwrap();

        for j in 0..len{
            let clear = &w_prf_clear(key, inputs[j], b);
            for i in 0..82{
                assert_eq!(fk_x[j*82 + i], clear[i], "Output of wPRF does not match clear output at index {i} for input {j}");
            }
        }

    }
}