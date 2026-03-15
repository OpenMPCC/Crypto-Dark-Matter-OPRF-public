use std::time::Instant;

use hd_quicksilver::homcom::{FComProver, FComVerifier};
use ocelot::svole::wykw::choose_lpn_parameters;
use oprf::daBits_code_consistency::{code_candidate_client, code_candidate_server, large_cpde, medium_code, small_code, CodeType};
use rand::SeedableRng;
use scuttlebutt::{field::{F256b, F64t, F3}, track_unix_channel_pair, AesRng};




fn main(){
    for i in 14..24{
        let (client, server) = track_unix_channel_pair();
        let wanted_size = 1<<(i);
        let code = CodeType::Large;
        let parity_check_matrix = match code {
            CodeType::Small => small_code(),
            CodeType::Medium => medium_code(),
            CodeType::Large => large_cpde(),
        };
        let output_size = {
            if wanted_size % parity_check_matrix.k != 0 {
                //println!("Warning: The wanted size is not a multiple of the code's k. Adjusting to the next multiple of k.");
                wanted_size + (parity_check_matrix.k - (wanted_size % parity_check_matrix.k))
            } else {
                wanted_size
            }
        };

        let m = parity_check_matrix.b * (output_size/parity_check_matrix.k) + parity_check_matrix.zk_d + 1;
        let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F3>(m);
        let handle = std::thread::spawn(move  || {
            let mut rng = AesRng::from_seed(Default::default());
            //let reader = BufReader::new(client.try_clone().unwrap());
            //let writer = BufWriter::new(client);
            //let mut channel = Channel::new(reader, writer);
            let mut channel = client;
            let t_start = Instant::now();
            let mut fcom2 = FComProver::<F256b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let mut fcom3 = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let _ = fcom2.voles_reserve(&mut channel, &mut rng, m);
            let _ = fcom3.voles_reserve(&mut channel, &mut rng, m);
            
            let (v2, v3) = code_candidate_client(output_size, &mut fcom2, &mut fcom3, &mut channel, &mut rng, &code);
            let time = t_start.elapsed();
            print!("{}, {}, ", time.as_nanos()/output_size as u128, 1000.0*channel.kilobits_written()/output_size as f64);
            
            return (v2, v3);
        });
        let mut rng = AesRng::from_seed(Default::default());
        //let reader = BufReader::new(server.try_clone().unwrap());
        //let writer = BufWriter::new(server);
        //let mut channel = Channel::new(reader, writer);
        let mut channel = server;
        let t_start = Instant::now();
        let mut fcom2 = FComVerifier::<F256b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let mut fcom3 = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let _ = fcom2.voles_reserve(&mut channel, &mut rng, m);
        let _ = fcom3.voles_reserve(&mut channel, &mut rng, m);
        let (_, _) = code_candidate_server(output_size, &mut fcom2, &mut fcom3, &mut channel, &mut rng, &code);
        let time = t_start.elapsed();

        let (_, _) = handle.join().unwrap();
        println!("{}, {}", time.as_nanos()/output_size as u128, 1000.0*channel.kilobits_written()/output_size as f64);
    }
}