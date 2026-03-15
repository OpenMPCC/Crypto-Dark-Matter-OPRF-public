//! Implemenatation of endemic OT using Kyber

use kyber_ot::{self, gen_matrix, indcpa_dec, indcpa_enc, indcpa_keypair, pack_pk, polyvec_add, polyvec_reduce, polyvec_sub, randombytes, sha3_256, unpack_pk, Polyvec, KYBER_INDCPA_PUBLICKEYBYTES, KYBER_INDCPA_SECRETKEYBYTES, KYBER_K, KYBER_POLYBYTES, KYBER_POLYVECBYTES, KYBER_SYMBYTES};
use rand::SeedableRng;
use scuttlebutt::{AesRng, Block, Malicious, SemiHonest};

use crate::ot::{Receiver as OtReceiver, Sender as OtSender};
/// OT Sender
#[derive(Clone)]
pub struct Sender{
}

/// OT Receiver
#[derive(Clone)]
pub struct Receiver{
}

impl SemiHonest for Sender {}
impl Malicious for Sender {}
impl SemiHonest for Receiver {}
impl Malicious for Receiver {}

impl OtSender for Sender{
    type Msg = Block;

    fn init<C: scuttlebutt::AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        _channel: &mut C,
        _rng: &mut RNG,
    ) -> Result<Self, crate::Error> {
        Ok(Self{})
    }

    fn send<C: scuttlebutt::AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        inputs: &[(Self::Msg, Self::Msg)],
        _rng: &mut RNG,
    ) -> Result<(), crate::Error> {
        let mut ctxt: Vec<KyberOTCtxt> = vec![KyberOTCtxt { sm: [vec![0u8; KYBER_POLYVECBYTES + KYBER_POLYBYTES], vec![0u8; KYBER_POLYVECBYTES + KYBER_POLYBYTES]] }; inputs.len()];
        let mut ptxt: Vec<KyberOTPtxt> = vec![KyberOTPtxt { sot: [vec![0u8; KYBER_SYMBYTES], vec![0u8; KYBER_SYMBYTES]] }; inputs.len()];
        
        // Generate random messages
        for i in 0..inputs.len(){ 
            let arr0: [u8; 16] = inputs[i].0.into();
            let arr1: [u8; 16] = inputs[i].1.into();
            
            let mut in0 = [0u8; KYBER_SYMBYTES];
            in0[16..].copy_from_slice(&arr0);
            let mut in1 = [0u8; KYBER_SYMBYTES];
            in1[16..].copy_from_slice(&arr1);

            ptxt[i].sot[0].copy_from_slice(&in0);
            ptxt[i].sot[1].copy_from_slice(&in1);
        }

        let mut pks = Vec::new();
        for _ in 0..inputs.len(){
            let mut bytes1 = [0u8; KYBER_INDCPA_PUBLICKEYBYTES];
            channel.read_bytes(&mut bytes1)?;
            let mut bytes2 = [0u8; KYBER_INDCPA_PUBLICKEYBYTES];
            channel.read_bytes(&mut bytes2)?;
            let pk = KyberOtRecvPKs { keys: [bytes1.to_vec(), bytes2.to_vec()] };
            pks.push(pk);
        }

        for i in 0..inputs.len(){
            kyber_sender_message(&mut ctxt[i], &ptxt[i], &pks[i]);
            channel.write_bytes(&ctxt[i].sm[0])?;
            channel.write_bytes(&ctxt[i].sm[1])?;
        }
        channel.flush()?;
        Ok(())
    }
}


impl OtReceiver for Receiver{
    type Msg = Block;

    fn init<C: scuttlebutt::AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        _channel: &mut C,
        _rng: &mut RNG,
    ) -> Result<Self, crate::Error> {
        Ok(Self{})
    }

    fn receive<C: scuttlebutt::AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        inputs: &[bool],
        _rng: &mut RNG,
    ) -> Result<Vec<Self::Msg>, crate::Error> {
        let mut recver= vec![KyberOTRecver { secret_key: vec![0u8; KYBER_INDCPA_SECRETKEYBYTES], b: 0, rot: vec![0u8; KYBER_SYMBYTES] }; inputs.len()];

        let mut pks = Vec::new();
        for i in 0..inputs.len(){
            let mut pk = KyberOtRecvPKs { keys: [vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES], vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES]] }; 
            recver[i].b = if inputs[i] {1} else {0};
            kyber_receiver_message(&mut recver[i], &mut pk);
            pks.push(pk);
        }
        for pk in pks{
            channel.write_bytes(&pk.keys[0])?;
            channel.write_bytes(&pk.keys[1])?;
        }
        channel.flush()?;

        for i in 0..inputs.len(){
            let mut bytes1 = [0u8; KYBER_POLYVECBYTES + KYBER_POLYBYTES];
            channel.read_bytes(&mut bytes1)?;
            let mut bytes2 = [0u8; KYBER_POLYVECBYTES + KYBER_POLYBYTES];
            channel.read_bytes(&mut bytes2)?;
            let c = KyberOTCtxt { sm: [bytes1.to_vec(), bytes2.to_vec()] };
            kyber_receiver_strings(&mut recver[i], &c);
        }

        let mut outputs = Vec::new();
        for i in 0..inputs.len(){
            outputs.push(Block::try_from_slice(&recver[i].rot[16..]).unwrap());
        }
        Ok(outputs)
    }
}

impl std::fmt::Display for Receiver {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Endemic OT Receiver")
    }
}



/// PK hash
pub fn pk_hash(h: &mut [u8], pk: &[u8], publicseed: &[u8]) {
    const SEED_LEN: usize = 32;

    // Compute SHA3-256(pk[0..PKlengthsmall])
    let mut seed = [0u8; SEED_LEN];
    sha3_256(&mut seed, pk, KYBER_POLYVECBYTES);

    // Call randomPK(h, seed, publicseed)
    random_pk(h, &seed, publicseed);
}

fn random_pk(pk: &mut [u8], seed: &[u8], publicseed: &[u8]) {
    // Allocate an array of polyvecs
    let mut a: Vec<Polyvec> = vec![Polyvec::new(); KYBER_K];

    // Generate matrix from seed1
    gen_matrix(&mut a, seed, false);

    // Pack into pk using seed2
    pack_pk(pk, &mut a[0], publicseed);
}

fn pk_plus(pk: &mut [u8], pk1: &[u8], pk2: &[u8]) {
    let mut pkpv1 = Polyvec::new();
    let mut pkpv2 = Polyvec::new();
    let mut seed = [0u8; KYBER_SYMBYTES];
    let mut _seed = [0u8; KYBER_SYMBYTES];

    // Deserialize pk1 and pk2 into polyvec form
    unpack_pk(&mut pkpv1, &mut seed, pk1);
    unpack_pk(&mut pkpv2, &mut _seed, pk2);

    // Add polyvecs
    polyvec_add(&mut pkpv1, &pkpv2);
    polyvec_reduce(&mut pkpv1);

    // Repack into pk
    pack_pk(pk, &mut pkpv1, &seed);
}

fn pk_minus(pk: &mut [u8], pk1: &[u8], pk2: &[u8]) {
    let mut pkpv1 = Polyvec::new();
    let mut pkpv2 = Polyvec::new();
    let mut seed = [0u8; KYBER_SYMBYTES];
    let mut _seed = [0u8; KYBER_SYMBYTES];

    // Deserialize pk1 and pk2
    unpack_pk(&mut pkpv1, &mut seed, pk1);
    unpack_pk(&mut pkpv2, &mut _seed, pk2);

    // Subtract polyvecs
    polyvec_sub(&mut pkpv2, &pkpv1);
    polyvec_reduce(&mut pkpv2);

    // Repack
    pack_pk(pk, &mut pkpv2, &seed);
}

const COINSLENGTH: usize = 32;

/// Receiver state
#[derive(Clone)]
pub struct KyberOTRecver {
    /// Receiver's secret key
    pub secret_key: Vec<u8>,  // size = secret key length
    /// Receiver's choice bit
    pub b: usize,             // choice bit (0 or 1)
    /// Receiver's output string
    pub rot: Vec<u8>,         // receiver’s output string
}

/// Receiver’s public keys container
pub struct KyberOtRecvPKs {
    /// Two public keys
    pub keys: [Vec<u8>; 2],   // two public keys of length PKLENGTH
}

/// Sender’s ciphertext container
#[derive(Clone)]
pub struct KyberOTCtxt {
    /// Two ciphertexts
    pub sm: [Vec<u8>; 2],     // two ciphertexts
}

/// Sender’s plaintexts
#[derive(Clone)]
pub struct KyberOTPtxt {
    /// Two strings to send
    pub sot: [Vec<u8>; 2],    // two strings to send
}

/// Receiver message generation (C: KyberReceiverMessage)
pub fn kyber_receiver_message(recver: &mut KyberOTRecver, pks: &mut KyberOtRecvPKs) {
    let mut pk = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
    let mut h  = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
    let mut seed = [0u8; 32];

    // AES rng
    let mut rng = AesRng::from_entropy();

    // get pk, sk
    indcpa_keypair(&mut pk, &mut recver.secret_key, None, &mut rng).unwrap();

    // sample random public key for the one we don’t want
    randombytes(&mut seed, 32, &mut rng).unwrap();
    let not_b = 1 ^ recver.b;
    random_pk(&mut pks.keys[not_b], &seed, &pk[KYBER_POLYVECBYTES..]);

    // compute H(r_{not b})
    pk_hash(&mut h, &pks.keys[not_b], &pk[KYBER_POLYVECBYTES..]);

    // set r_b = pk - H(r_{not b})
    pk_minus(&mut pks.keys[recver.b], &pk, &h);
}

/// Sender message generation (C: KyberSenderMessage)
pub fn kyber_sender_message(ctxt: &mut KyberOTCtxt, ptxt: &KyberOTPtxt, recv_pks: &KyberOtRecvPKs) {
    let mut h  = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
    let mut pk = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
    let mut coins = vec![0u8; COINSLENGTH];

    let mut rng = AesRng::from_entropy();
    // --- First ciphertext (index 0) ---
    randombytes(&mut coins, COINSLENGTH, &mut rng).unwrap();

    // compute pk0
    pk_hash(&mut h, &recv_pks.keys[1], &recv_pks.keys[0][KYBER_POLYVECBYTES..]);
    pk_plus(&mut pk, &recv_pks.keys[0], &h);

    // enc
    indcpa_enc(&mut ctxt.sm[0], &ptxt.sot[0], &pk, &coins);

    // --- Second ciphertext (index 1) ---
    randombytes(&mut coins, COINSLENGTH, &mut rng).unwrap();

    // compute pk1
    pk_hash(&mut h, &recv_pks.keys[0], &recv_pks.keys[0][KYBER_POLYVECBYTES..]);
    pk_plus(&mut pk, &recv_pks.keys[1], &h);

    // enc
    indcpa_enc(&mut ctxt.sm[1], &ptxt.sot[1], &pk, &coins);
}

/// Receiver output strings (C: KyberReceiverStrings)
pub fn kyber_receiver_strings(recver: &mut KyberOTRecver, ctxt: &KyberOTCtxt) {
    indcpa_dec(&mut recver.rot, &ctxt.sm[recver.b], &recver.secret_key);
}


#[cfg(test)]
mod test{
    use kyber_ot::{indcpa_keypair, randombytes, KYBER_INDCPA_PUBLICKEYBYTES, KYBER_INDCPA_SECRETKEYBYTES, KYBER_K, KYBER_POLYBYTES, KYBER_POLYVECBYTES, KYBER_SYMBYTES};
    use rand::SeedableRng;
    use scuttlebutt::{AesRng, Block};

    use super::{KyberOTCtxt, KyberOTPtxt, KyberOTRecver, KyberOtRecvPKs}; // Added missing import

    #[test]
    pub fn endemic_ot(){
        let mut ctxt = KyberOTCtxt { sm: [vec![0u8; KYBER_POLYVECBYTES + KYBER_POLYBYTES], vec![0u8; KYBER_POLYVECBYTES + KYBER_POLYBYTES]] };
        let mut ptxt = KyberOTPtxt { sot: [vec![0u8; KYBER_SYMBYTES], vec![0u8; KYBER_SYMBYTES]] }; 
        let mut recver = KyberOTRecver { secret_key: vec![0u8; KYBER_INDCPA_SECRETKEYBYTES], b: 0, rot: vec![0u8; KYBER_SYMBYTES] };
        let mut pks = KyberOtRecvPKs { keys: [vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES], vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES]] }; 

        println!("kyber_k {:?}", KYBER_K);

        let mut rng = AesRng::from_entropy();
        randombytes(&mut [recver.b as u8], 1, &mut rng).unwrap();
        recver.b &= 1;

        randombytes(&mut ptxt.sot[0], KYBER_SYMBYTES, &mut rng).unwrap();
        randombytes(&mut ptxt.sot[1], KYBER_SYMBYTES, &mut rng).unwrap();

        super::kyber_receiver_message(&mut recver, &mut pks);
        super::kyber_sender_message(&mut ctxt, &ptxt, &pks);
        super::kyber_receiver_strings(&mut recver, &ctxt);

        assert_eq!(&recver.rot[..], &ptxt.sot[recver.b][..]);
    }

    #[test]
    pub fn test_plus_minus(){
        let mut pk1 = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
        let mut pk2 = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
        let mut pk_plus = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
        let mut pk_minus = vec![0u8; KYBER_INDCPA_PUBLICKEYBYTES];
        let mut sk = vec![0u8; KYBER_INDCPA_SECRETKEYBYTES];

        let block: Block = [0u8; 16].into();
        let mut rng = AesRng::from_seed(block);
        indcpa_keypair(&mut pk1, &mut sk, None, &mut rng).unwrap();
        indcpa_keypair(&mut pk2, &mut sk, None, &mut rng).unwrap();

        super::pk_plus(&mut pk_plus, &pk1, &pk2);
        super::pk_minus(&mut pk_minus, &pk_plus, &pk2);

        assert_eq!(&pk1[..KYBER_POLYVECBYTES], &pk_minus[..KYBER_POLYVECBYTES]);
    }
}