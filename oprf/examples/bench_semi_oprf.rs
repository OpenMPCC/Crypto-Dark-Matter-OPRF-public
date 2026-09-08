use std::time::Instant;


use oprf::{matrix_util::generate_fixed_b, semi_OPRF::{semi_oprf_client, semi_oprf_server, semi_preprocesses_client, semi_preprocesses_server}};
use rand::SeedableRng;
use scuttlebutt::{field::F256b, ring::FiniteRing, track_unix_channel_pair, AesRng};

fn main(){
    for i in 0..20{
        let (client, server) = track_unix_channel_pair();
        let batch_size = 1<<i;
        let (_, b) = generate_fixed_b();
        let bs = b.clone();

        let handle = std::thread::spawn(move  || {
            let mut rng = AesRng::from_seed(Default::default());
            let mut channel = client;

            
            let mut inputs = Vec::new();
            for _ in 0..batch_size{
                let rand = F256b::random(&mut rng);
                inputs.push(rand);
            }
            let t_start = Instant::now();

            let (mut fcom_k, d_bits) = semi_preprocesses_client(&mut channel, &mut rng, batch_size);
            let time_pre = t_start.elapsed();
            let t_start = Instant::now();
            let fk_x = semi_oprf_client(inputs, batch_size, d_bits, &mut channel, &mut rng, b, &mut fcom_k);
            
            let time = t_start.elapsed();
            print!("{}, {}, {},",time_pre.as_micros()/batch_size as u128, time.as_micros()/batch_size as u128, 1000.0*channel.kilobits_written()/batch_size as f64);
            return fk_x;
        });
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = server;
        
        let key = F256b::random(&mut rng);
        let t_start = Instant::now();

        let (mut fcom_k, d_bits) = semi_preprocesses_server(&mut channel, &mut rng, batch_size);
        let time_pre = t_start.elapsed();
        let t_start = Instant::now();
        semi_oprf_server(key, batch_size, d_bits, &mut channel, &mut rng, bs, &mut fcom_k);
        let time = t_start.elapsed();

        let _ = handle.join().unwrap();
        
        println!("{}, {}, {},",time_pre.as_micros()/batch_size as u128, time.as_micros()/batch_size as u128, 1000.0*channel.kilobits_written()/batch_size as f64);
    }

}