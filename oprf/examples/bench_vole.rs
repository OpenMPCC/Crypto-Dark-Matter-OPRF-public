use std::{thread::sleep, time::Instant};

use hd_quicksilver::homcom::{FComProver, FComVerifier};
use ocelot::svole::wykw::choose_lpn_parameters;
use rand::SeedableRng;
use scuttlebutt::{field::{F256b, F64t}, track_unix_channel_pair, AesRng};

fn main(){
    for i in 8..26{

        let (client, server) = track_unix_channel_pair();
        let size = 2<<i;
        let handle = std::thread::spawn(move  || {
            let mut rng = AesRng::from_seed(Default::default());
            let mut channel = client;
            let t_start = Instant::now();
            
            let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F256b>(size);
            let mut fcom_p_2 = FComProver::<F256b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let _ = fcom_p_2.voles_reserve(&mut channel, &mut rng, size);
            
            let time = t_start.elapsed();
            print!("{}, {}, ", time.as_nanos()/size as u128, 1000.0*channel.kilobits_written()/size as f64);
            
            channel.clear();
            sleep(std::time::Duration::from_millis(2000));
            
            let t_start = Instant::now();
            let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F64t>(size);
            let mut fcom_p_3 = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let _ = fcom_p_3.voles_reserve(&mut channel, &mut rng, size);
            
            let time = t_start.elapsed();
            print!("{}, {}, ", time.as_nanos()/size as u128, 1000.0*channel.kilobits_written()/size as f64);
            
            return 0;
        });
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = server;
        let t_start = Instant::now();
        let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F256b>(size);
        let mut fcom_v_2 = FComVerifier::<F256b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let _ = fcom_v_2.voles_reserve(&mut channel, &mut rng, size);
        
        let time = t_start.elapsed();
        
        
        sleep(std::time::Duration::from_millis(1000));
        print!("{}, {}, ", time.as_nanos()/size as u128, 1000.0*channel.kilobits_written()/size as f64);
        
        channel.clear();
        
        let t_start = Instant::now();
        let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F64t>(size);
        let mut fcom_v_3 = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let _ = fcom_v_3.voles_reserve(&mut channel, &mut rng, size);
        
        let time = t_start.elapsed();
        let _ = handle.join().unwrap();
        println!("{}, {}, ", time.as_nanos()/size as u128, 1000.0*channel.kilobits_written()/size as f64);
    }
}