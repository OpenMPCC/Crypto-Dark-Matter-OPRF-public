use std::time::Instant;

use oprf::{matrix_util::generate_precompute_tables, preprocessing::{init_cdm_oprf_receiver, init_cdm_oprf_sender}, OPRF::OPRFSetting};
use rand::SeedableRng;
use scuttlebutt::{field::{F128b, F3}, ring::FiniteRing, track_unix_channel_pair, AesRng, Block};

fn main(){
    for i in 0..20{
        let (client, server) = track_unix_channel_pair();
        let batch_size = 1<<i;
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

        let handle = std::thread::spawn(move  || {
            let mut rng = AesRng::from_seed(Default::default());
            let mut channel = client;

            
            let mut inputs = Vec::new();
            for _ in 0..batch_size{
                let rand = F128b::random(&mut rng);
                inputs.push(rand);
            }
            let t_start = Instant::now();

            let mut cdmoprfreceiver = init_cdm_oprf_receiver(&mut channel, &mut rng, inputs.len(), b, bc, OPRFSetting::RevealOutput);
            let time_pre = t_start.elapsed();
            let t_start = Instant::now();
            let fk_x = cdmoprfreceiver.oprf_client(inputs, &mut channel, &mut rng);
            
            let time = t_start.elapsed();
            print!("{}, {}, {},",time_pre.as_micros()/batch_size as u128, time.as_micros()/batch_size as u128, 1000.0*channel.kilobits_written()/batch_size as f64);
            return fk_x;
        });
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = server;
        
        let t_start = Instant::now();

        let mut cdmoprfsender = init_cdm_oprf_sender(&mut channel, &mut rng, batch_size, b, bs, OPRFSetting::RevealOutput);
        let time_pre = t_start.elapsed();
        let t_start = Instant::now();
        cdmoprfsender.oprf_server(batch_size, &mut channel, &mut rng);
        let time = t_start.elapsed();

        let _ = handle.join().unwrap();
        
        println!("{}, {}, {},",time_pre.as_micros()/batch_size as u128, time.as_micros()/batch_size as u128, 1000.0*channel.kilobits_written()/batch_size as f64);
    }

}