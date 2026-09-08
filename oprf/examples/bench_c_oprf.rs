use std::time::Instant;

use oprf::{client_OPRF::{c_oprf_client, c_oprf_server}, client_wPRF::{c_preprocess_client, c_preprocess_server}, matrix_util::generate_fixed_b};
use rand::SeedableRng;
use scuttlebutt::{field::{F128b, F256b}, ring::FiniteRing, track_unix_channel_pair, AesRng};

fn main(){
    for i in 0..18{
        let (client, server) = track_unix_channel_pair();
        let batch_size = 1<<i;
        let (_, bc) = generate_fixed_b();
        let bs = bc.clone();

        let handle = std::thread::spawn(move  || {
            let mut rng = AesRng::from_seed(Default::default());
            let mut channel = client;

            
            let mut inputs = Vec::new();
            for _ in 0..batch_size{
                let rand = F128b::random(&mut rng);
                inputs.push(rand);
            }
            let t_start = Instant::now();

            let (habits, encoding_dabits, mut fcom_p_3, mut fcom_k, mut fcom_k_delta) = c_preprocess_client(&mut channel, &mut rng, batch_size);
            let time_pre = t_start.elapsed();
            let t_start = Instant::now();
            let fk_x = c_oprf_client(inputs, &mut channel, &mut rng, bc, habits, encoding_dabits, &mut fcom_p_3, &mut fcom_k, &mut fcom_k_delta);
            
            let time = t_start.elapsed();
            print!("{}, {}, {},",time_pre.as_micros()/batch_size as u128, time.as_micros()/batch_size as u128, 1000.0*channel.kilobits_written()/batch_size as f64);
            return fk_x;
        });
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = server;
        
        let key = F256b::random(&mut rng);
        let t_start = Instant::now();

        let (habits, encoding_dabits, mut fcom_v_2, mut fcom_v_3, mut fcom_k, mut fcom_k_delta) = c_preprocess_server(&mut channel, &mut rng, batch_size, key);
        let time_pre = t_start.elapsed();
        let t_start = Instant::now();
        c_oprf_server(key, batch_size, &mut channel, &mut rng, bs, habits, encoding_dabits, &mut fcom_v_2, &mut fcom_v_3, &mut fcom_k, &mut fcom_k_delta);
        let time = t_start.elapsed();

        let _ = handle.join().unwrap();
        
        println!("{}, {}, {},",time_pre.as_micros()/batch_size as u128, time.as_micros()/batch_size as u128, 1000.0*channel.kilobits_written()/batch_size as f64);
    }

}