use hd_quicksilver::homcom::{FComProver, FComVerifier};
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::FiniteField, ring::FiniteRing, AbstractChannel, Block};

use crate::dabits::OPRFSharing;



pub fn ha_bit_client<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    fcom_p_2: &mut FComProver<Fb>,
    channel: &mut C,
    rng: &mut RNG,
) ->(Vec<OPRFSharing<Fb>>, Vec<Fp::PrimeField>)
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{
    // Step 1 & 2
    // Sample output_size many candidates, and commit to them 

    let mut c_commitment = Vec::with_capacity(output_size);
    for _ in 0..output_size{
        let com = fcom_p_2.random(channel, rng).unwrap();
        c_commitment.push(com);
    }

    // Step 3
    let mut m_b = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let m_b_i = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&c_commitment[i].mac().to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
                .unwrap()
                .into();
            Fp::PrimeField::from_uniform_bytes(&bytes)
        };
        m_b.push(m_b_i);
    }

    // Step 4
    let t = channel.read_serializable_seq::<Fp::PrimeField>(output_size).unwrap();

    // Step 5
    let mut b_tilde = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let value = u8::from(c_commitment[i].value()).try_into();
        let value = match value {
            Ok(v) => v,
            Err(_) => panic!("Failed to convert commitment value to Fp"),
            
        };
        let b_i = m_b[i] + value * t[i] + value;
        b_tilde.push(b_i);
    }
    drop(m_b);
    drop(t);

    let mut sharings = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let share = OPRFSharing{
            0: c_commitment[i].value(),
            1: c_commitment[i],
            2: Default::default(),
        };
        sharings.push(share);
    }
    (sharings, b_tilde)
}

pub fn ha_bit_server<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    fcom_v_2: &mut FComVerifier<Fb>,
    channel: &mut C,
    rng: &mut RNG,
) ->(Vec<OPRFSharing<Fb>>, Vec<Fp::PrimeField>)
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{
    // step 1
    let mut b: Vec<Fb::PrimeField> = Vec::with_capacity(output_size);
    for _ in 0..output_size{
        let b_i = Fb::PrimeField::random(rng);
        b.push(b_i);
    }
    
    // Step2
    let mut c_commitment = Vec::with_capacity(output_size);
    for _ in 0..output_size{
        let com = fcom_v_2.random(channel, rng).unwrap();
        c_commitment.push(com);
    }

    // Step 3
    let mut m_0 = Vec::with_capacity(output_size);
    let mut m_1 = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let m_0_i = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&c_commitment[i].mac().to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
            .unwrap()
            .into();
            Fp::PrimeField::from_uniform_bytes(&bytes)
        };
        let m_1_i = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&(c_commitment[i].mac() + fcom_v_2.get_delta()).to_bytes());
            let bytes: [u8; 16] = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16])
            .unwrap()
            .into();
            Fp::PrimeField::from_uniform_bytes(&bytes)
        };
        m_0.push(m_0_i);
        m_1.push(m_1_i);
    }

    // Step 4
    let mut t = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let b_value: Fp::PrimeField  =  match u8::from(b[i]).try_into(){
            Ok(v) => v,
            Err(_) => panic!("Failed to convert b[i] to Fp"),
        };
        let t_i = b_value + m_0[i] - m_1[i];
        t.push(t_i);
    }
    drop(m_1);
    channel.write_serializable_seq(&t).unwrap();
    channel.flush().unwrap();
    drop(t);

    // Step 5
    let mut b_tilde = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let b_value: Fp::PrimeField  =  match u8::from(b[i]).try_into(){
            Ok(v) => v,
            Err(_) => panic!("Failed to convert b[i] to Fp"),
        };
        let b_i = b_value - m_0[i];
        b_tilde.push(b_i);
    }
    drop(m_0);

    let mut sharings = Vec::with_capacity(output_size);
    for i in 0..output_size{
        let share = OPRFSharing{
            0: b[i],
            1: Default::default(),
            2: c_commitment[i],
        };
        sharings.push(share);
    }
    (sharings, b_tilde)
}

#[cfg(test)]
mod tests{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    use ocelot::svole::wykw::choose_lpn_parameters;
    use rand::SeedableRng;
    use scuttlebutt::{field::{F256b, F64t}, AesRng, Channel};

    use super::*;

    #[test]
    fn ha_bit_test(){
        let (client, server) = UnixStream::pair().unwrap();
        let ell = 10;
        let output_size = ell;
        let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<F256b>(ell);

        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom_p_2 = FComProver::<F256b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();

            ha_bit_client::<F256b, F64t, _, _>(output_size, &mut fcom_p_2, &mut channel, &mut rng)
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom_v_2 = FComVerifier::<F256b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params).unwrap();

        let (server_sharing, server_bit) = ha_bit_server::<F256b, F64t, _, _>(output_size, &mut fcom_v_2, &mut channel, &mut rng);
            
        let (client_sharing, client_bit) = handle.join().unwrap();

        for i in 0..ell{
            let bit_2 = server_sharing[i].0 + client_sharing[i].0;
            let bit_3 = server_bit[i] + client_bit[i];
            assert_eq!(u8::from(bit_2), u8::from(bit_3));
        }

        for i in 0..ell{
            let key = server_sharing[i].2.mac();
            let mac = client_sharing[i].1.mac();
            let value = client_sharing[i].0 ;
            assert_eq!(key, mac + value*fcom_v_2.get_delta());
        }

    }
}