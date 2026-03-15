use hd_quicksilver::homcom::{FComProver, FComVerifier};
use rand::{CryptoRng, Rng, SeedableRng};
use scuttlebutt::{field::{F128b, F256b, F82t, FiniteField}, ring::FiniteRing, serialization::CanonicalSerialize, AbstractChannel, AesRng, Block};
use std::io::{self, Result};

pub fn lift_prover_vole<C: AbstractChannel, RNG: CryptoRng + Rng>(
    fcom: &mut FComProver<F256b>,
    channel: &mut C,
    rng: &mut RNG,
    size: usize,
)-> (F256b, F256b){
    let mut oles = Vec::with_capacity(size);
    for _ in 0..size {
        let ole = fcom.random(channel, rng).unwrap();
        oles.push(ole);
    }
    let mut out = oles[0].mac();
    let mut value:F256b = (oles[0].value()).into() ;
    let mut pow = F256b::ONE;
    for i in 1..oles.len() {
        pow.shift_left_once();
        out = out + oles[i].mac().pow_mul(i);
        value = value + oles[i].value() * pow;
    }
    (value, out)
}

pub fn lift_prover_vole_to_higher_field<C: AbstractChannel, RNG: CryptoRng + Rng>(
    fcom: &mut FComProver<F128b>,
    channel: &mut C,
    rng: &mut RNG,
    size: usize,
)-> (F256b, F256b){
    let mut oles = Vec::with_capacity(size);
    for _ in 0..size {
        let ole = fcom.random(channel, rng).unwrap();
        oles.push(ole);
    }
    let mut out = oles[0].mac().into();
    let mut value:F256b = (oles[0].value()).into() ;
    let mut pow = F256b::ONE;
    for i in 1..oles.len() {
        pow.shift_left_once();
        let mac: F256b = oles[i].mac().into();
        out = out + mac * pow;
        value = value + oles[i].value() * pow;
    }
    (value, out)
}

pub fn lift_verifier_vole<C: AbstractChannel, RNG: CryptoRng + Rng>(
    fcom: &mut FComVerifier<F256b>,
    channel: &mut C,
    rng: &mut RNG,
    size: usize,
) -> F256b{
    let mut oles = Vec::with_capacity(size);
    for _ in 0..size {
        let ole = fcom.random(channel, rng).unwrap();
        oles.push(ole);
    }
    let mut out = oles[0].mac();
    for i in 1..oles.len() {
        out = out + oles[i].mac().pow_mul(i);
    }
    out
}

pub fn lift_verifier_vole_to_higher_field<C: AbstractChannel, RNG: CryptoRng + Rng>(
    fcom: &mut FComVerifier<F128b>,
    channel: &mut C,
    rng: &mut RNG,
    size: usize,
) -> F256b{
    let mut oles = Vec::with_capacity(size);
    for _ in 0..size {
        let ole = fcom.random(channel, rng).unwrap();
        oles.push(ole);
    }
    let mut out = oles[0].mac().into();
    let mut pow = F256b::ONE;
    for i in 1..oles.len() {
        pow.shift_left_once();
        let mac: F256b = oles[i].mac().into();
        out = out + mac * pow;
    }
    out
}

pub fn open_mac_prover_lazy<'a, C: AbstractChannel, FE: FiniteField, FFE: FiniteField,  I: IntoIterator<Item = FE>, J: IntoIterator<Item = FFE>>(
    channel: &mut C,
    values: J,
    macs: I,
) -> Result<()>{
    let mut hasher = blake3::Hasher::new();
    let values_to_send = values.into_iter().map(|x| {
        hasher.update(&x.to_bytes());
        x
    }).collect::<Vec<_>>();
    channel.write_serializable_seq(&values_to_send)?;

    let seed = Block::try_from_slice(&hasher.finalize().as_bytes()[..16]).unwrap();
    let mut rng = AesRng::from_seed(seed);

    let mut m = FE::ZERO;
    for mac in macs {
        let chi = FE::random(&mut rng);
        m += chi * mac;
    }
    channel.write_serializable::<FE>(&m)?;
    channel.flush()?;
    Ok(())
}

pub fn open_extension_mac_prover<C: AbstractChannel, FE: FiniteField>(
    channel: &mut C,
    values: &[FE],
    macs: &[FE],
) -> Result<()>{
    let mut hasher = blake3::Hasher::new();
    let values_to_send = values.iter().map(|x| *x).collect::<Vec<_>>();
    channel.write_serializable_seq(&values_to_send)?;
    for val in values {
        hasher.update(&val.to_bytes());
    }
    let seed = Block::try_from_slice(&hasher.finalize().as_bytes()[..16]).unwrap();
    let mut rng = AesRng::from_seed(seed);

    let mut m = FE::ZERO;
    for mac in macs{
        let chi = FE::random(&mut rng);
        m += chi * *mac;
    }
    channel.write_serializable::<FE>(&m)?;
    channel.flush()?;

    Ok(())
}

pub fn open_extension_mac_verifier<C: AbstractChannel, FE: FiniteField>(
    channel: &mut C,
    keys: &[FE],
    delta: FE,
    out: &mut Vec<FE>,
) -> Result<()>{
    let mut hasher = blake3::Hasher::new();
    out.clear();
    let x_values = channel.read_serializable_seq::<FE>(keys.len())?;
    for i in 0..keys.len() {
        let x = x_values[i];
        out.push(x);
        hasher.update(&x.to_bytes());
    }
    let seed = Block::try_from_slice(&hasher.finalize().as_bytes()[0..16]).unwrap();
    let mut rng = AesRng::from_seed(seed);

    let mut key_chi = FE::ZERO;
    let mut x_chi = FE::ZERO;
    for i in 0..keys.len() {
        let chi = FE::random(&mut rng);
        let key = keys[i];
        let x = out[i];

        key_chi += chi * key;
        x_chi += x * chi;
    }
    let m = channel.read_serializable::<FE>()?;

    assert_eq!(out.len(), keys.len());
    if key_chi + delta * x_chi == m {
        Ok(())
    } else {
        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "Opening of extension mac is not valid",
        ))
    }
}

pub fn lift_sharing<const N: usize>(index: usize, sharing: &Vec<(crate::dabits::OPRFSharing<F256b>, crate::dabits::OPRFSharing<F82t>)>)
-> (F256b, F256b, F256b){
    let values: Vec<F256b> = sharing[N*index..N*index + N].iter().map(|x| x.0.0.into()).collect();
    let macs: Vec<F256b> = sharing[N*index..N*index + N].iter().map(|x| x.0.1.mac().into()).collect();
    let keys: Vec<F256b> = sharing[N*index..N*index + N].iter().map(|x| x.0.2.mac().into()).collect();
    lift_array::<{N}>(values, macs, keys)
}

pub fn lift_array<const N: usize>(values: Vec<F256b>, mut macs: Vec<F256b>, mut keys: Vec<F256b>)
-> (F256b, F256b, F256b){
    let mut value = values[0];
    let mut mac = macs[0];
    let mut key = keys[0];
    let mut pow = F256b::ONE;
    for i in 1..N{
        pow.shift_left_once();
        value += values[i] * pow;
        mac += macs[i].pow_mul(i);
        key += keys[i].pow_mul(i);
    }
    (value, mac, key)
}



// Implementation of F_{EQ} from https://eprint.iacr.org/2020/925.pdf
pub fn weak_equality_second<C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    _rng: &mut RNG,
    values: &mut Vec<F256b>,
    _fcom: &mut FComVerifier<F256b>,
) -> Result<()>{
    let batch_size = values.len();

    // Get commitment of V_B from b
    let mut com: [u8; 32] = [0u8; 32];
    channel.read_bytes(&mut com)?;

    // Send V_A to to b
    channel.write_serializable_seq(&values)?;
    channel.flush()?;

    // Get opening of commitment from b
    let v_b: Vec<F256b> = channel.read_serializable_seq(batch_size)?;

    let mut hasher = blake3::Hasher::new();
    for val in v_b.iter(){
        hasher.update(&val.to_bytes());
    }
    let binding = hasher.finalize();
    if com != *binding.as_bytes(){
        return Err(io::Error::new(io::ErrorKind::Other, "Commitment does not open"));
    }

    for i in 0..batch_size{
        if values[i] != v_b[i] {
            return Err(io::Error::new(io::ErrorKind::Other, "V_A != V_B"));
        }
    }

    // Output V_A = V_B
    Ok(())
}

pub fn weak_equality_first<C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    _rng: &mut RNG,
    values: &mut Vec<F256b>,
    _fcom: &mut FComProver<F256b>,
) -> Result<()>{
    let batch_size = values.len();

    // Commit to V_B
    let mut hasher = blake3::Hasher::new();
    for val in values.iter(){
        hasher.update(&val.to_bytes());
    }
    let binding = hasher.finalize();
    let com = binding.as_bytes();
    channel.write_bytes(com)?;
    channel.flush()?;

    // get V_A from A
    let v_a: Vec<F256b> = channel.read_serializable_seq(batch_size)?;

    // Check V_A = V_B
    for i in 0..batch_size{
        if v_a[i] != values[i]{
            let zeros = vec![F256b::ZERO; batch_size];
            channel.write_serializable_seq(&zeros)?;
            channel.flush()?;
            return Err(io::Error::new(io::ErrorKind::Other, "V_A != V_B"));
        }
    }

    // Open commitment of V_B
    channel.write_serializable_seq(&values)?;
    channel.flush()?;

    Ok(())
}


#[cfg(test)]
mod test{
    use std::{io::{BufReader, BufWriter}, os::unix::net::UnixStream};

    use ocelot::svole::wykw::{LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
    use rand::SeedableRng;
    use scuttlebutt::{field::F128b, AesRng, Block, Channel};
    use super::*;

    #[test]
    fn test_lift(){
        let seed = Block::from([0; 16]);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom2 = FComProver::<F256b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
            let out = lift_prover_vole(&mut fcom2, &mut channel, &mut rng, 64);
            return out;
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom2 = FComVerifier::<F256b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
        let out = lift_verifier_vole(&mut fcom2, &mut channel, &mut rng, 64);

        let client = handle.join().unwrap();

        assert_eq!(client.0 * fcom2.get_delta() + client.1, out);
    }

    #[test]
    fn test_lift_higher_field(){
        let seed = Block::from([0; 16]);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom2 = FComProver::<F128b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
            let out = lift_prover_vole_to_higher_field(&mut fcom2, &mut channel, &mut rng, 64);
            return out;
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom2 = FComVerifier::<F128b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
        let out = lift_verifier_vole_to_higher_field(&mut fcom2, &mut channel, &mut rng, 64);

        let client = handle.join().unwrap();

        let delta: F256b = fcom2.get_delta().into();
        assert_eq!(client.0 * delta + client.1, out);
    }


    #[test]
    fn test_f_eq(){
        let seed = Block::from([0; 16]);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let v_a = F256b::random(&mut rng);
            let v_a_1 = F256b::random(&mut rng);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom = FComVerifier::<F256b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
            
            let out = weak_equality_second(&mut channel, &mut rng, &mut [v_a, v_a_1].into(), &mut fcom);
            return out;
        });

        let mut rng = AesRng::from_seed(seed);
        let v_b = F256b::random(&mut rng);
        let v_b_1 = F256b::random(&mut rng);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom = FComProver::<F256b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
        
        let out = weak_equality_first(&mut channel, &mut rng, &mut [v_b, v_b_1].into(), &mut fcom);

        let client = handle.join().unwrap();

        out.unwrap();
        client.unwrap();
    }

    #[test]
    fn test_f_eq_false(){
        let seed = Block::from([0; 16]);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let _ = F256b::random(&mut rng);
            let v_a = F256b::random(&mut rng);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom = FComVerifier::<F256b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
            
            let out = weak_equality_second(&mut channel, &mut rng, &mut [v_a].into(), &mut fcom);
            return out;
        });

        let mut rng = AesRng::from_seed(seed);
        let v_b = F256b::random(&mut rng);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom = FComProver::<F256b>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
        
        let out = weak_equality_first(&mut channel, &mut rng, &mut [v_b].into(), &mut fcom);

        let client = handle.join().unwrap();

        let a = match out {
            Ok(_) => 0,
            _ => 1,
        };
        let b = match client {
            Ok(_) => 0,
            _ => 1,
        };

        assert_eq!(a,b);
        assert_eq!(a, 1);
    }
}