use hd_quicksilver::homcom::{FComProver, FComVerifier};
use ocelot::svole::wykw::choose_lpn_parameters;
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{F256b, F82t, F3}, AbstractChannel};

use crate::{daBits_cnc_consistency::{candidate_client, candidate_server, get_bucket_size}, daBits_code_consistency::{code_candidate_client, code_candidate_server, CodeType}, dabits::{dabit_client, dabit_server, OPRFExtensionSharing}, vole_util::{lift_prover_vole, lift_sharing, lift_verifier_vole, weak_equality_first, weak_equality_second}, OPRF::{CDMOPRFReceiver, CDMOPRFSender, OPRFSetting}};


pub fn init_cdm_oprf_receiver<C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    batch_size: usize,
    b: [[F3; 256];82],
    b_tables: Vec<F3>,
    setting: OPRFSetting
) -> CDMOPRFReceiver{
    const N: usize = 256;

    let f3_p_size: usize;
    let f3_v_size: usize;

    if setting == OPRFSetting::RevealOutput {
        let bucketing_cutoff = 1<<8;
        if batch_size < bucketing_cutoff{
            f3_p_size = 16+2;
            f3_v_size = 32+2
        }else{
            f3_p_size = 9+2;
            f3_v_size = 18+2;
        }

    } else {
        let bucketing_cutoff = 1<<8;
        if batch_size < bucketing_cutoff{
            f3_p_size = 32+2;
            f3_v_size = 32+2
        }else{
            f3_p_size = 18+2;
            f3_v_size = 18+2;
        }
    }


    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F82t>(batch_size*N*f3_v_size);
    let mut f3_v = FComVerifier::<F82t>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    let a = f3_v.extract_svole_receiver();

    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F82t>(batch_size*N*f3_p_size + batch_size*N*2);
    let mut f3_p = FComProver::<F82t>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params, lpn_extend_params, a).unwrap();

    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*N*3 + batch_size*N*2);
    let mut f2_p = FComProver::<F256b>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();
    
    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*N*2);
    let mut f2_v = FComVerifier::<F256b>::init_from_previous_setup_receiver(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();

    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<F256b>(batch_size*N*2 + 512);
    let mut fk = FComProver::<F256b>::init_from_previous_setup_receiver(channel, rng, fcom_k_params, fcom_k_params_extend, a).unwrap();

    let (lpn_share_setup_params, lpn_share_extend_params) = choose_lpn_parameters::<F256b>(batch_size*N);
    let fk_delta = FComProver::<F256b>::init_from_previous_setup_receiver(channel, rng, lpn_share_setup_params, lpn_share_extend_params, a).unwrap();

    let mut da_bits = Vec::new();
    if N*batch_size > 1<<21{
        let iterations = (N*batch_size) / (1<<20);
        for i in 0..iterations{
            let mut output_size = 1<<20;
            if i == iterations -1 {
                output_size = N*batch_size - (iterations-1)*(1<<20);
            }
            let da_bits_part = dabit_client(
                1<<20, 
                &mut f2_p,
                &mut f2_v,
                &mut f3_p,
                &mut f3_v,
                channel, 
                rng,
                setting);

            for j in 0..(output_size/N){
                let mut f3_parts = Vec::with_capacity(N);
                let (value, mac, key) = lift_sharing::<N>(j, &da_bits_part);
                for k in 0..N{
                    f3_parts.push( da_bits_part[k + j*N].1);
                }

                let extension_sharing = OPRFExtensionSharing(value, mac, key);
                da_bits.push((extension_sharing, f3_parts));
            }

        }
    }else{
        let da_bits_part = dabit_client(
            batch_size*N, 
            &mut f2_p,
            &mut f2_v,
            &mut f3_p,
            &mut f3_v,
            channel, 
            rng,
            setting);
        for j in 0..(batch_size*N/N){
            let mut f3_parts = Vec::with_capacity(N);
            let (value, mac, key) = lift_sharing::<N>(j, &da_bits_part);
            for k in 0..N{
                f3_parts.push( da_bits_part[k + j*N].1);
            }

            let extension_sharing = OPRFExtensionSharing(value, mac, key);
            da_bits.push((extension_sharing, f3_parts));
        }
    }

    let mut encoding_la_bits = (Vec::new(), Vec::new());
    if N*batch_size > 1<<21{
        let iterations = (N*batch_size) / (1<<20);
        for i in 0..iterations{
            let mut output_size = 1<<20;
            if i == iterations -1 {
                output_size = N*batch_size - (iterations-1)*(1<<20);
            }
            let encoding_part = code_candidate_client(
                output_size, 
                &mut f2_p,
                &mut f3_p,
                channel, 
                rng,
                &CodeType::Large);
            encoding_la_bits.0.extend(encoding_part.0);
            encoding_la_bits.1.extend(encoding_part.1);
        }
    } else if N*batch_size >= 1<<14 {
        let encoding_part = code_candidate_client(
            N*batch_size, 
            &mut f2_p,
            &mut f3_p,
            channel, 
            rng,
            &CodeType::Large);
        encoding_la_bits.0.extend(encoding_part.0);
        encoding_la_bits.1.extend(encoding_part.1);
    } else{
        let bucket_size = get_bucket_size(N*batch_size);
        let encoding_part = candidate_client((N*batch_size, bucket_size, 3), &mut f2_p, &mut f3_p, channel, rng);
        encoding_la_bits.0.extend(encoding_part.0);
        encoding_la_bits.1.extend(encoding_part.1);
    }

    let (value, mac_delta_0) = lift_prover_vole(&mut fk, channel, rng, N);
    let diff = value - f2_v.get_delta();
    channel.write_serializable(&diff).unwrap();
    channel.flush().unwrap();

    let mut k_key = lift_verifier_vole(&mut f2_v, channel, rng, N);
    let d: F256b = channel.read_serializable().unwrap();
    k_key = k_key - f2_v.get_delta() * d;

    weak_equality_first(channel, rng, &mut [mac_delta_0 - k_key].into(), &mut f2_p).unwrap();

    CDMOPRFReceiver{f2_p, f3_p, f2_v, f3_v, fk, fk_delta, da_bits, encoding_la_bits, mac_delta_0, b, b_tables}
}


pub fn init_cdm_oprf_sender<C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    batch_size: usize,
    b: [[F3; 256];82],
    b_tables: Vec<F3>,
    setting: OPRFSetting
) -> CDMOPRFSender{
    const N: usize = 256;
    
    let f3_p_size: usize;
    let f3_v_size: usize;

    if setting == OPRFSetting::RevealOutput {
        let bucketing_cutoff = 1<<8;
        if batch_size < bucketing_cutoff{
            f3_p_size = 32+2;
            f3_v_size = 16+2
        }else{
            f3_p_size = 18+2;
            f3_v_size = 9+2;
        }

    } else {
        let bucketing_cutoff = 1<<8;
        if batch_size < bucketing_cutoff{
            f3_p_size = 32+2;
            f3_v_size = 32+2
        }else{
            f3_p_size = 18+2;
            f3_v_size = 18+2;
        }
    }

    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F82t>(batch_size*N*f3_p_size);
    let mut f3_p = FComProver::<F82t>::init(channel, rng, lpn_setup_params, lpn_extend_params).unwrap();
    let a = f3_p.extract_svole_sender();
    
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F82t>(batch_size*N*f3_v_size + batch_size*N*2);
    let mut f3_v = FComVerifier::<F82t>::init_from_previous_setup_sender(channel, rng, lpn_setup_params, lpn_extend_params, a).unwrap();

    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*N*3 + batch_size*N*2);
    let mut f2_v = FComVerifier::<F256b>::init_from_previous_setup_sender(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a).unwrap();
    
    let (lpn_setup_params_f2, lpn_extend_params_f2) = choose_lpn_parameters::<F256b>(batch_size*N*2);
    let mut f2_p = FComProver::<F256b>::init_from_previous_setup_sender(channel, rng, lpn_setup_params_f2, lpn_extend_params_f2, a ).unwrap();

    let (fcom_k_params, fcom_k_params_extend) = choose_lpn_parameters::<F256b>(batch_size*N*2 + 512);
    let mut fk: FComVerifier<F256b> = FComVerifier::<F256b>::init_from_previous_setup_sender(channel, rng, fcom_k_params, fcom_k_params_extend, a).unwrap();

    let (lpn_share_setup_params, lpn_share_extend_params) = choose_lpn_parameters::<F256b>(batch_size*N);
    let fk_delta = FComVerifier::<F256b>::init_with_picked_delta_and_ot(channel, rng, lpn_share_setup_params, lpn_share_extend_params, fk.get_delta()* f2_v.get_delta(), a).unwrap();


    let mut da_bits = Vec::new();
    if N*batch_size > 1<<21{
        let iterations = (N*batch_size) / (1<<20);
        for i in 0..iterations{
            let mut output_size = 1<<20;
            if i == iterations -1 {
                output_size = N*batch_size - (iterations-1)*(1<<20);
            }
            let da_bits_part = dabit_server(
                1<<20, 
                &mut f2_p,
                &mut f2_v,
                &mut f3_p,
                &mut f3_v,
                channel, 
                rng,
                setting);

            for j in 0..(output_size/N){
                let mut f3_parts = Vec::with_capacity(N);
                let (value, mac, key) = lift_sharing::<N>(j, &da_bits_part);
                for k in 0..N{
                    f3_parts.push( da_bits_part[k + j*N].1);
                }

                let extension_sharing = OPRFExtensionSharing(value, mac, key);
                da_bits.push((extension_sharing, f3_parts));
            }

        }
    }else{
        let da_bits_part = dabit_server(
            batch_size*N, 
            &mut f2_p,
            &mut f2_v,
            &mut f3_p,
            &mut f3_v,
            channel, 
            rng,
            setting);
        for j in 0..(batch_size*N/N){
            let mut f3_parts = Vec::with_capacity(N);
            let (value, mac, key) = lift_sharing::<N>(j, &da_bits_part);
            for k in 0..N{
                f3_parts.push( da_bits_part[k + j*N].1);
            }

            let extension_sharing = OPRFExtensionSharing(value, mac, key);
            da_bits.push((extension_sharing, f3_parts));
        }
    }

    let mut encoding_la_bits = (Vec::new(), Vec::new());
    if N*batch_size > 1<<21{
        let iterations = (N*batch_size) / (1<<20);
        for i in 0..iterations{
            let mut output_size = 1<<20;
            if i == iterations -1 {
                output_size = N*batch_size - (iterations-1)*(1<<20);
            }
            let encoding_part = code_candidate_server(
                output_size, 
                &mut f2_v,
                &mut f3_v,
                channel, 
                rng,
                &CodeType::Large);
            encoding_la_bits.0.extend(encoding_part.0);
            encoding_la_bits.1.extend(encoding_part.1);
        }
    } else if N*batch_size >= 1<<14{
        let encoding_part = code_candidate_server(
            N*batch_size, 
            &mut f2_v,
            &mut f3_v,
            channel, 
            rng,
            &CodeType::Large);
        encoding_la_bits.0.extend(encoding_part.0);
        encoding_la_bits.1.extend(encoding_part.1);
    }else{
        let bucket_size = get_bucket_size(N*batch_size);
        let encoding_part = candidate_server((N*batch_size, bucket_size, 3), &mut f2_v, &mut f3_v, channel, rng);
        encoding_la_bits.0.extend(encoding_part.0);
        encoding_la_bits.1.extend(encoding_part.1);
    }

    let mut key_delta_0 = lift_verifier_vole(&mut fk, channel, rng, N);
    let d: F256b = channel.read_serializable().unwrap();
    key_delta_0 = key_delta_0 - fk.get_delta() * d;

    let (value, mac_k) = lift_prover_vole(&mut f2_p, channel, rng, N);
    let diff = value - fk.get_delta();
    channel.write_serializable(&diff).unwrap();
    channel.flush().unwrap();

    weak_equality_second(channel, rng, &mut [mac_k-key_delta_0].into(), &mut f2_v).unwrap();

    let key = fk.get_delta();
    CDMOPRFSender{f2_p, f3_p, f2_v, f3_v, fk, fk_delta, da_bits, encoding_la_bits, key_delta_0, b, b_tables, key }
}