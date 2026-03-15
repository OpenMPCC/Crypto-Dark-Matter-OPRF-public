use std::time::Instant;

use hd_quicksilver::homcom::{FComProver, FComVerifier};
use ocelot::svole::wykw::choose_lpn_parameters;
use oprf::daBits_cnc_consistency::{candidate_client, candidate_server};
use rand::SeedableRng;
use scuttlebutt::{field::{F64b, F64t, F3}, track_unix_channel_pair, AesRng};




fn main(){
    for i in 14..24{
        let (client, server) = track_unix_channel_pair();
        let param = (1<<i, 4, 3);
        let m = param.0*param.1 + param.2;
        let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F3>(m);
        let handle = std::thread::spawn(move  || {
            let mut rng = AesRng::from_seed(Default::default());
            //let reader = BufReader::new(client.try_clone().unwrap());
            //let writer = BufWriter::new(client);
            //let mut channel = Channel::new(reader, writer);
            let mut channel = client;
            let t_start = Instant::now();
            let mut fcom2 = FComProver::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let mut fcom3 = FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let _ = fcom2.voles_reserve(&mut channel, &mut rng, m);
            let _ = fcom3.voles_reserve(&mut channel, &mut rng, m);
            
            let (v2, v3) = candidate_client(param, &mut fcom2, &mut fcom3, &mut channel, &mut rng);
            let time = t_start.elapsed();
            print!("{}, {}, ", time.as_nanos()/param.0 as u128, 1000.0*channel.kilobits_written()/param.0 as f64);
            return (v2, v3);
        });
        let mut rng = AesRng::from_seed(Default::default());
        //let reader = BufReader::new(server.try_clone().unwrap());
        //let writer = BufWriter::new(server);
        //let mut channel = Channel::new(reader, writer);
        let mut channel = server;
        let t_start = Instant::now();
        let mut fcom2 = FComVerifier::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let mut fcom3 = FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let _ = fcom2.voles_reserve(&mut channel, &mut rng, m);
        let _ = fcom3.voles_reserve(&mut channel, &mut rng, m);
        let (_, _) = candidate_server(param, &mut fcom2, &mut fcom3, &mut channel, &mut rng);
        let time = t_start.elapsed();

        let (_, _) = handle.join().unwrap();

        println!("{}, {}", time.as_nanos()/param.0 as u128, 1000.0*channel.kilobits_written()/param.0 as f64);
    }
}