use std::time::Instant;

use hd_quicksilver::homcom::{FComProver, FComVerifier};
use ocelot::svole::wykw::choose_lpn_parameters;
use oprf::{dabits::{dabit_client, dabit_server}, OPRF::OPRFSetting};
use rand::SeedableRng;
use scuttlebutt::{field::{F64b, F64t, F3}, track_unix_channel_pair, AesRng};

fn main(){
    let (client, server) = track_unix_channel_pair();
    let output_size = 1<<21;
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F3>(output_size*10);
    let handle = std::thread::spawn(move  || {
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = client;
        
        let t_vole = Instant::now();
        let mut fcom_p_3 = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let mut fcom_v_3 = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let mut fcom_p_2 = FComProver::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let mut fcom_v_2 = FComVerifier::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let dur_vole = t_vole.elapsed();

        let t_start = Instant::now();
        let dabits = dabit_client(output_size, &mut fcom_p_2, &mut fcom_v_2, &mut fcom_p_3, &mut fcom_v_3, &mut channel, &mut rng, OPRFSetting::SecretShareOutput);
        
        let time = t_start.elapsed();
        println!("###Online phase###");
        println!("Runtime: {:?}", time);
        println!("VOLE setup time {:?}", dur_vole);
        println!("Runtime per dabit: {:?} us", (time.as_micros()+dur_vole.as_micros())/output_size as u128);
        println!("comm {}kBits", channel.kilobits_written());
        println!("comm per dabit {}kBits", channel.kilobits_written()/output_size as f64);
        println!("VOLES per dabit: {:?} p_3, {:?} p_2, {:?} v_3, {:?} v_2", 
            fcom_p_3.get_stats().num_voles_used/output_size,
            fcom_p_2.get_stats().num_voles_used/output_size,
            fcom_v_3.get_stats().num_voles_used/output_size,
            fcom_v_2.get_stats().num_voles_used/output_size);
        
        return dabits;
    });
    let mut rng = AesRng::from_seed(Default::default());
    let mut channel = server;
    let t_start = Instant::now();
    let mut fcom_v_3 = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
    let mut fcom_p_3 = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
    let mut fcom_v_2 = FComVerifier::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
    let mut fcom_p_2 = FComProver::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
    
    let dur_start = t_start.elapsed();
    
    //channel.clear();
    
    let time1 = Instant::now();
    let _ = dabit_server(output_size, &mut fcom_p_2, &mut fcom_v_2, &mut fcom_p_3, &mut fcom_v_3, &mut channel, &mut rng, OPRFSetting::SecretShareOutput);
    let time = time1.elapsed();

    let _ = handle.join().unwrap();
    
    println!("SERVER");
    println!("VOLE setup time: {:?}", dur_start);
    println!("Runtime: {:?}", time);
    println!("Runtime per dabit: {:?} us", (time.as_micros() + dur_start.as_micros())/output_size as u128);
    println!("comm {}kBits", channel.kilobits_written());
    println!("comm per dabit {}kBits", channel.kilobits_written()/output_size as f64);
    println!("Number of VOLE extensions {:?}", fcom_p_3.get_stats().num_vole_extensions_performed);
}