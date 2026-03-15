use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{F64b, FiniteField, F2, F3}, ring::FiniteRing, serialization::CanonicalSerialize, AbstractChannel, Block};

use hd_quicksilver::homcom::{FComProver, FComVerifier};

pub fn ot_d_bits_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    fcom_p_2: &mut FComProver<F64b>,
) -> Vec<(u8, F3)>{
    let vole_size = (output_size as f64 * 1.5) as usize;
    fcom_p_2.voles_reserve(channel, rng, vole_size).unwrap();

    let string_len = channel.read_u64().unwrap() as usize;
    let discard_ot_string: Vec<F2> = channel.read_serializable_seq(string_len).unwrap();

    let mut d_bits = Vec::new();
    for bit in &discard_ot_string{
        let ole = fcom_p_2.random(channel, rng).unwrap();
        if bit == &F2::ONE{
            continue;
        }
        let mb: F3 = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&ole.mac().to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
            .unwrap()
            .into();
            <F3 as FiniteField>::PrimeField::from_uniform_bytes(&bytes)
        };
        d_bits.push((ole.value().into(), -mb));
    };
    return d_bits;
}

pub fn ot_d_bits_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    channel: &mut C,
    rng: &mut RNG,
    fcom_v_2: &mut FComVerifier<F64b>,
) -> Vec<(u8, F3)>{

    let vole_size = (output_size as f64 * 1.5) as usize;
    fcom_v_2.voles_reserve(channel, rng, vole_size).unwrap();

    let mut discard_ot_string: Vec<F2> = Vec::new();
    let mut d_bits: Vec<(u8, F3)> = Vec::new();
    while d_bits.len() < output_size {
        let ole = fcom_v_2.random(channel, rng).unwrap();
        let m0: F3 = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&ole.mac().to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
            .unwrap()
            .into();
            <F3 as FiniteField>::PrimeField::from_uniform_bytes(&bytes)
        };
        let m1: F3 = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&(ole.mac()+fcom_v_2.get_delta()).to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
            .unwrap()
            .into();
            <F3 as FiniteField>::PrimeField::from_uniform_bytes(&bytes)
        };
        
        if m0 == m1{
            discard_ot_string.push(F2::ONE);
        }else{
            discard_ot_string.push(F2::ZERO);
            if m1 == m0 + F3::ONE {
                d_bits.push((1, m1));
            } else {
                d_bits.push((0, m0));
            }
        }
        
    }
    channel.write_u64(discard_ot_string.len() as u64).unwrap();
    channel.write_serializable_seq(&discard_ot_string).unwrap();
    channel.flush().unwrap();

    return d_bits;
}

#[cfg(test)]
mod test{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};
    use ocelot::svole::wykw::choose_lpn_parameters;
    use rand::SeedableRng;
    use scuttlebutt::{AesRng, Channel};

    use super::*;

    #[test]
    fn d_bits_test(){
        let (client, server) = UnixStream::pair().unwrap();
        let output_size = 100;
        let handle = std::thread::spawn( move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let n = 256;
            let vole_size = ((output_size*n) as f64 * 1.5) as usize;
            let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F64b>(vole_size as usize);
            let mut fcom_p_2 = FComProver::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
            let d_bits = ot_d_bits_client(output_size, &mut channel, &mut rng, &mut fcom_p_2);
            return d_bits;
        });
        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let n = 256;
        let vole_size = ((output_size*n) as f64 * 1.5) as usize;
        let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F64b>(vole_size as usize);
        let mut fcom_v_2 = FComVerifier::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();
        let d_bits_server = ot_d_bits_server(output_size, &mut channel, &mut rng, &mut fcom_v_2);

        let d_bits_client = handle.join().unwrap();

        for i in 0..output_size{
            let value_2 = d_bits_server[i].0 ^ d_bits_client[i].0;
            let value_3 = u8::from(d_bits_server[i].1 + d_bits_client[i].1);

            assert_eq!(value_2, value_3);   
        }
        assert_eq!(d_bits_server.len(), output_size);
        assert_eq!(d_bits_client.len(), output_size);
    }
}