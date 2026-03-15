use std::time::Instant;

use hd_quicksilver::homcom::{FComProver, FComVerifier};
use ocelot::svole::wykw::choose_lpn_parameters;
use oprf::F3triples::{triple_client, triple_server};
use rand::SeedableRng;
use scuttlebutt::{field::{F64t, F3}, track_unix_channel_pair, AesRng};

fn main(){
    let (client, server) = track_unix_channel_pair();
    let param = (1<<12, 2, 3);
    let m = param.0*param.1*param.1 + param.2;
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F3>(m);
    let handle = std::thread::spawn(move  || {
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = client;
        
        let mut fcom_p = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let mut fcom_v = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        
        let t_start = Instant::now();
        let triples = triple_client(param, &mut fcom_p, &mut fcom_v, &mut channel, &mut rng);
        
        let time = t_start.elapsed();
        println!("CLIENT");
        println!("Runtime: {:?}", time);
        println!("Runtime per triple: {:?} us", time.as_micros()/param.0 as u128);
        println!("comm {}kBits", channel.kilobits_written());
        println!("comm per triple {}kBits", channel.kilobits_written()/param.0 as f64);
        println!("VOLE per triple {} Prover - {} Verifier", fcom_p.get_stats().num_voles_used/param.0, fcom_v.get_stats().num_voles_used/param.0);
        
        return triples;
    });
    let mut rng = AesRng::from_seed(Default::default());
    let mut channel = server;
    let t_start = Instant::now();
    let mut fcom_v = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
    let mut fcom_p = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();

    let _ = triple_server(param, &mut fcom_p, &mut fcom_v, &mut channel, &mut rng);
    let time = t_start.elapsed();

    let _ = handle.join().unwrap();
    
    println!("SERVER");
    println!("Runtime: {:?}", time);
    println!("Runtime per triple: {:?} us", time.as_micros()/param.0 as u128);
    println!("comm {}kBits", channel.kilobits_written());
    println!("comm per triple {}kBits", channel.kilobits_written()/param.0 as f64);
    println!("VOLE per triple {} Prover - {} Verifier", fcom_p.get_stats().num_voles_used/param.0, fcom_v.get_stats().num_voles_used/param.0);
    println!("Number of VOLE extensions {} - {}", fcom_p.get_stats().num_vole_extensions_performed, fcom_v.get_stats().num_vole_extensions_performed);
    println!("done");
}