use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::{F128b, F256b, F82t, F3}, ring::FiniteRing, AbstractChannel, Block};
use ocelot::Error;

use crate::{dabits::{OPRFExtensionSharing, OPRFSharing}, full_wPRF::{secret_shared_w_prf_client_with_commitment, secret_shared_w_prf_server_with_commitment, w_prf_client_commit_to_input, w_prf_client_with_commitment, w_prf_server_commit_to_input, w_prf_server_with_commitment}, input_encoding::{apply_gadget, apply_parity_check_matrix_f82t, generate_linear_code, encode_input}, vole_util::*};
use crate::{matrix_util::generate_precompute_tables, preprocessing::{init_cdm_oprf_receiver, init_cdm_oprf_sender}};

/// Trait containing the associated types used by an oblivious PRF.
pub trait ObliviousPrf
where
    Self: Sized,
{
    /// PRF seed.
    type Seed: Sized;
    /// PRF input.
    type Input: Sized;
    /// PRF output.
    type Output: Sized;
}

/// Trait for an oblivious PRF sender.
pub trait Sender: ObliviousPrf
where
    Self: Sized,
{
    /// Runs any one-time initialization.
    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<Self, Error>;
    /// Runs `m` OPRF instances as the sender, returning the OPRF seeds.
    fn send<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        m: usize,
        rng: &mut RNG,
    ) -> Result<Vec<Self::Seed>, Error>;
    /// Computes the oblivious PRF on seed `seed` and input `input`.
    fn compute(&self, seed: Self::Seed, input: Self::Input) -> Self::Output;
}

/// Trait for an oblivious PRF receiver.
pub trait Receiver: ObliviousPrf
where
    Self: Sized,
{
    /// Runs any one-time initialization.
    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<Self, Error>;
    /// Runs the oblivious PRF on inputs `inputs`, returning the OPRF outputs.
    fn receive<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        inputs: &[Self::Input],
        rng: &mut RNG,
    ) -> Result<Vec<Self::Output>, Error>;
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum OPRFSetting{
    RevealOutput,
    SecretShareOutput,
}
pub struct CDMOPRFReceiver {
    // VOLE correlations
    pub f2_p: FComProver<F256b>,
    pub f3_p: FComProver<F82t>,
    pub f2_v: FComVerifier<F256b>,
    pub f3_v: FComVerifier<F82t>,
    pub fk: FComProver<F256b>,
    pub fk_delta: FComProver<F256b>,

    // Preprocessing
    pub da_bits: Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    pub encoding_la_bits: (Vec<MacProver<F256b>>, Vec<MacProver<F82t>>),
    pub mac_delta_0: F256b,

    // CDM settings
    pub b: [[F3; 256];82],
    pub b_tables: Vec<F3>,
}

pub struct CDMOPRFSender {
    // VOLE correlations
    pub f2_p: FComProver<F256b>,
    pub f3_p: FComProver<F82t>,
    pub f2_v: FComVerifier<F256b>,
    pub f3_v: FComVerifier<F82t>,
    pub fk: FComVerifier<F256b>,
    pub fk_delta: FComVerifier<F256b>,

    // Preprocessing
    pub da_bits: Vec<(OPRFExtensionSharing<F256b>, Vec<OPRFSharing<F82t>>)>,
    pub encoding_la_bits: (Vec<MacVerifier<F256b>>, Vec<MacVerifier<F82t>>),
    pub key_delta_0: F256b,

    // CDM settings
    pub key: F256b,
    pub b: [[F3; 256];82],
    pub b_tables: Vec<F3>,
}

impl ObliviousPrf for CDMOPRFSender {
    type Seed = F256b;
    type Input = F128b;
    type Output = ();
}

impl Sender for CDMOPRFSender {
    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        _channel: &mut C,
        _rng: &mut RNG,
    ) -> Result<Self, Error> {
        // For CDMOPRFSender, the fields should already be initialized.
        // Usually, init is used for any one-time setup. Here we return an uninitialized dummy.
        let batch_size = 256;
        let mut b: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b[i][j] = F3::random(_rng);
            }
        }
        let bs = generate_precompute_tables(b);
        Ok(init_cdm_oprf_sender(_channel, _rng, batch_size, b, bs, OPRFSetting::RevealOutput))
    }

    fn send<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        m: usize,
        rng: &mut RNG,
    ) -> Result<Vec<Self::Seed>, Error> {
        // Run the OPRF as server
        self.oprf_server(m, channel, rng);
        Ok(vec![self.key; m])
    }

	fn compute(&self, seed: Self::Seed, input: Self::Input) -> Self::Output {
    }
}

impl ObliviousPrf for CDMOPRFReceiver {
    type Seed = F256b;
    type Input = F128b;
    type Output = F3;
}

impl Receiver for CDMOPRFReceiver {
    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        _channel: &mut C,
        _rng: &mut RNG,
    ) -> Result<Self, Error> {
        // Usually, init is used for any one-time setup. Here we return an uninitialized dummy.
        let batch_size = 256;
        let mut b: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b[i][j] = F3::random(_rng);
            }
        }
        let bc = generate_precompute_tables(b);
        Ok(init_cdm_oprf_receiver(_channel, _rng, batch_size, b, bc, OPRFSetting::RevealOutput))
    }

    fn receive<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        inputs: &[Self::Input],
        rng: &mut RNG,
    ) -> Result<Vec<Self::Output>, Error> {
        let outputs = inputs
            .iter()
            .cloned()
            .collect::<Vec<F128b>>(); // clone inputs for method
        let res = self.oprf_client(outputs, channel, rng);
        Ok(res)
    }
}

impl CDMOPRFReceiver{
    pub fn oprf_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        input: Vec<F128b>, 
        channel: &mut C, 
        rng: &mut RNG,
    )-> Vec<F3> {
        let (encoded_inputs, batch_size, coms) = self.check_encoded_input(input, channel, rng);

        let out = w_prf_client_with_commitment(encoded_inputs, batch_size, channel, rng, &mut self.b, &mut self.b_tables, &mut self.da_bits, &mut self.f2_p, &mut self.f2_v, &mut self.f3_v, &mut self.fk, &mut self.fk_delta, coms, self.mac_delta_0);
        return out;
    }

    pub fn secret_shared_oprf_client<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        input: Vec<F128b>, 
        channel: &mut C, 
        rng: &mut RNG,
    )-> Vec<OPRFSharing<F82t>> {
        let (encoded_inputs, batch_size, coms) = self.check_encoded_input(input, channel, rng);

        let out = secret_shared_w_prf_client_with_commitment(encoded_inputs, batch_size, channel, rng, &mut self.b, &mut self.b_tables, &mut self.da_bits, &mut self.f2_p, &mut self.f2_v, &mut self.f3_v, &mut self.fk, &mut self.fk_delta, coms, self.mac_delta_0);
        return out;
    }

    fn check_encoded_input<C: AbstractChannel, RNG: CryptoRng + Rng>(&mut self, input: Vec<F128b>, channel: &mut C, rng: &mut RNG) -> (Vec<F256b>, usize, Vec<F256b>) {
        let(g, gadget, h) = generate_linear_code();
        let mut encoded_inputs = Vec::with_capacity(input.len());
        for i in input{
            let encoded = encode_input(i, g);
            encoded_inputs.push(encoded);
        }
        let batch_size = encoded_inputs.len();
            
        let n = 256;
        
        let (dabits_2, dabits_3) = &self.encoding_la_bits;
        
        let coms = w_prf_client_commit_to_input(&encoded_inputs, batch_size, channel, rng, &mut self.fk);
        
        let diff = channel.read_serializable::<F256b>().unwrap();
        
        // Lift dabits
        let mut dabit_2_values = Vec::with_capacity(batch_size);
        let mut dabit_2_mac = Vec::with_capacity(batch_size);
        
        for j in 0..batch_size{
            let mut bit_2_value: F256b = dabits_2[0 + j*n].value().into();
            let mut bit_2_mac   = dabits_2[0 + j*n].mac() + bit_2_value * diff;
            
            let mut pow = F256b::ONE;
            for i in 1..n{
                pow.shift_left_once();
                bit_2_value = bit_2_value + dabits_2[i + j*n].value() * pow;
                bit_2_mac = bit_2_mac + (dabits_2[i + j*n].mac() + dabits_2[i + j*n].value() * diff).pow_mul(i);
            }
            dabit_2_values.push(bit_2_value);
            dabit_2_mac.push(bit_2_mac);
        }
        
        let mut c_to_open = Vec::with_capacity(batch_size);
        let mut c_macs = Vec::with_capacity(batch_size);
        for j in 0..batch_size{
            let c_c = dabit_2_values[j] + encoded_inputs[j];
            let c_mac = dabit_2_mac[j] + coms[j];
            c_to_open.push(c_c);
            c_macs.push(c_mac);
        };
        open_extension_mac_prover(channel, &c_to_open, &c_macs).unwrap();
        
        // Convert mac to F3 and apply gadget & H
        let mut check_macs = Vec::with_capacity(batch_size);
        let mut c_bit_string = [F3::ZERO; 256];
        for j in 0..batch_size{
            let mut mac_f3 = Vec::with_capacity(254);
        
            for i in 0..128{
                let value = (c_to_open[j].low >> i) & 1;
                c_bit_string[i] = F3{msb: 0, lsb: value as u8};
                let value = (c_to_open[j].high >> i) & 1;
                c_bit_string[i+128] = F3{msb: 0, lsb: value as u8};
            }
        
            // Convert to F3
            for i in 0..2{
                let dabit3_i = dabits_3[i+j*n];
                let c_i = c_bit_string[i];
                let mac = dabit3_i.mac() + c_i * dabit3_i.mac();
                let mac = MacProver::new(F3::ONE, mac);
                let mac = self.f3_p.affine_add_cst(F3::ONE + F3::ONE, mac);
                check_macs.push(mac);
            }
        
            for i in 2..256{
                let dabit3_i = dabits_3[i+j*n];
                let c_i = c_bit_string[i];
        
        
                let mac = dabit3_i.mac() + c_i * dabit3_i.mac();
                mac_f3.push(mac);
            }
        
            mac_f3.reverse();
        
            // apply gadget
            let gadget_out = apply_gadget(mac_f3.try_into().unwrap(), gadget);
        
            // apply H
            let check_matrix: [F82t; 63] = apply_parity_check_matrix_f82t(gadget_out, h);
            for i in 0..63{
                check_macs.push(MacProver::new(F3::ZERO,check_matrix[i]));
            }
        
        
        }
        
        self.f3_p.check_zero(channel, &check_macs).unwrap();
        (encoded_inputs, batch_size, coms)
            }
}


impl CDMOPRFSender{
    pub fn oprf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        batch_size: usize,
        channel: &mut C, 
        rng: &mut RNG,
    )-> () {
        let coms = self.check_encoded_input(batch_size, channel, rng);

        w_prf_server_with_commitment(self.key, batch_size, channel, rng, self.b, &mut self.b_tables, &mut self.da_bits, &mut self.f2_p, &mut self.f2_v, &mut self.f3_p, &mut self.fk, &mut self.fk_delta, coms, self.key_delta_0);
    }

    pub fn secret_shared_oprf_server<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        batch_size: usize,
        channel: &mut C, 
        rng: &mut RNG,
    )-> Vec<OPRFSharing<F82t>> {
        let coms = self.check_encoded_input(batch_size, channel, rng);

        secret_shared_w_prf_server_with_commitment(self.key, batch_size, channel, rng, self.b, &mut self.b_tables, &mut self.da_bits, &mut self.f2_p, &mut self.f2_v, &mut self.fk, &mut self.fk_delta, coms, self.key_delta_0)
    }

    fn check_encoded_input<C: AbstractChannel, RNG: CryptoRng + Rng>(&mut self, batch_size: usize, channel: &mut C, rng: &mut RNG) -> Vec<F256b> {
        let n = 256;
        let(_, gadget, h) = generate_linear_code();
        
        let (dabits_2, dabits_3) = &self.encoding_la_bits;
        
        let coms = w_prf_server_commit_to_input( batch_size, channel, rng, &mut self.fk);
        
        // Change Delta of commitment
        let diff = self.f2_v.get_delta() - self.fk.get_delta();
        channel.write_serializable(&diff).unwrap();
        channel.flush().unwrap();
        
        // Lift dabits
        let mut dabit_2_mac = Vec::with_capacity(batch_size);
        
        for j in 0..batch_size{
            let mut bit_2_mac   = dabits_2[0 + j*n].mac();
            for i in 1..n{
                bit_2_mac = bit_2_mac + dabits_2[i + j*n].mac().pow_mul(i);
            }
            dabit_2_mac.push(bit_2_mac);
        }
        
        let mut c_keys = Vec::with_capacity(batch_size);
        for j in 0..batch_size{
            let c_mac = dabit_2_mac[j] + coms[j];
            c_keys.push(c_mac);
        };
        let mut c_values = Vec::with_capacity(batch_size);
        open_extension_mac_verifier(channel, &c_keys, self.fk.get_delta(), &mut c_values).unwrap();
        
        // Convert mac to F3 and apply gadget & H
        let mut check_macs = Vec::with_capacity(batch_size);
        let mut c_bit_string = [F3::ZERO; 256];
        for j in 0..batch_size{
            let mut mac_f3 = Vec::with_capacity(254);
            
            for i in 0..128{
                let value = (c_values[j].low >> i) & 1;
                c_bit_string[i] = F3{msb: 0, lsb: value as u8};
                let value = (c_values[j].high >> i) & 1;
                c_bit_string[i+128] = F3{msb: 0, lsb: value as u8};
            }
            // Convert to F3
            for i in 0..2{
                let dabit3_i = dabits_3[i+j*n];
                let c_i = c_bit_string[i];
        
                let mac = -(c_i*self.f3_v.get_delta()) + dabit3_i.mac() + c_i * dabit3_i.mac();
                let mac = MacVerifier::new(mac);
                let mac = self.f3_v.affine_add_cst(F3::ONE + F3::ONE, mac);
                check_macs.push(mac);
            }
        
            for i in 2..256{
                let dabit3_i = dabits_3[i+j*n];
                let c_i = c_bit_string[i];
        
                let mac = -(c_i*self.f3_v.get_delta()) + dabit3_i.mac() + c_i * dabit3_i.mac();
                mac_f3.push(mac);
            }
        
            mac_f3.reverse();
        
            // apply gadget
            let gadget_out = apply_gadget(mac_f3.try_into().unwrap(), gadget);
        
            // apply H
            let check_matrix: [F82t; 63] = apply_parity_check_matrix_f82t(gadget_out, h);
            for i in 0..63{
                check_macs.push(MacVerifier::new(check_matrix[i]));
            }
        }
        
        self.f3_v.check_zero(channel, rng, &check_macs).unwrap();
        coms
            }
}


#[cfg(test)]
mod test{
    use std::io::{BufReader, BufWriter};
    use std::os::unix::net::UnixStream;

    use rand::SeedableRng;
    
    use scuttlebutt::{AesRng, Block, Channel};

    use super::*;
    
    use crate::full_wPRF::w_prf_clear;
    use crate::matrix_util::generate_precompute_tables;
    use crate::preprocessing::{init_cdm_oprf_receiver, init_cdm_oprf_sender};

    #[test]
    fn test_oprf() {
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


        let input = F128b::random(&mut b_rng);
        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let inputs = vec![input];

            let mut cdmoprfreceiver = init_cdm_oprf_receiver(&mut channel, &mut rng, inputs.len(), b, bc, OPRFSetting::RevealOutput);
            let out = cdmoprfreceiver.oprf_client(inputs, &mut channel, &mut rng);
            out
        });

        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);

        let batch_size = 1;
        let mut cdmoprfsender = init_cdm_oprf_sender(&mut channel, &mut rng, batch_size, b, bs, OPRFSetting::RevealOutput);
        let key = cdmoprfsender.fk.get_delta();
        cdmoprfsender.oprf_server(batch_size, &mut channel, &mut rng);

        let fk_x = handle.join().unwrap();

        // Verify the output
        let encoded_input = encode_input(input, generate_linear_code().0);
        let expected_out = w_prf_clear(key, encoded_input, b);
        for i in 0..82{
            assert_eq!(fk_x[i], expected_out[i], "Mismatch at index {}", i);
        }

    }

    #[test]
    fn test_oprf_batch() {
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

        let mut inputs = Vec::new();
        for _ in 0..10{
            let input = F128b::random(&mut b_rng);
            inputs.push(input);
        }
        let input_thread = inputs.clone();
        let mut rng = AesRng::from_seed(seed);
        let batch_size = inputs.len();

        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);

            let mut cdmoprfreceiver = init_cdm_oprf_receiver(&mut channel, &mut rng, input_thread.len(), b, bc, OPRFSetting::RevealOutput);
            let out = cdmoprfreceiver.oprf_client(input_thread, &mut channel, &mut rng);
            out
        });

        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        
        let mut cdmoprfsender = init_cdm_oprf_sender(&mut channel, &mut rng, batch_size, b, bs, OPRFSetting::RevealOutput);
        let key = cdmoprfsender.fk.get_delta();
        cdmoprfsender.oprf_server(batch_size, &mut channel, &mut rng);    
        
        let fk_x = handle.join().unwrap();
            
            // Verify the output
        for j in 0..batch_size{
            let encoded_input = encode_input(inputs[j].clone(), generate_linear_code().0);
            let expected_output = w_prf_clear(key, encoded_input, b);
            for i in 0..82{
                assert_eq!(fk_x[i + 82*j], expected_output[i], "Mismatch at index {}, {}", i, j);
            }
        }

    }

    #[test]
    fn test_secret_shared_oprf(){
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

        let mut inputs = Vec::new();
        for _ in 0..2{
            let input = F128b::random(&mut b_rng);
            inputs.push(input);
        }
        let input_thread = inputs.clone();
        let mut rng = AesRng::from_seed(seed);
        let batch_size = inputs.len();

        let (client, server) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);

            let mut cdmoprfreceiver = init_cdm_oprf_receiver(&mut channel, &mut rng, input_thread.len(), b, bc, OPRFSetting::SecretShareOutput);
            let out = cdmoprfreceiver.secret_shared_oprf_client(input_thread, &mut channel, &mut rng);
            (out, cdmoprfreceiver.f3_v.get_delta())
        });

        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        
        let mut cdmoprfsender = init_cdm_oprf_sender(&mut channel, &mut rng, batch_size, b, bs, OPRFSetting::SecretShareOutput);
        let key = cdmoprfsender.fk.get_delta();
        let fk_x_server = cdmoprfsender.secret_shared_oprf_server(batch_size, &mut channel, &mut rng);    
        
        let (fk_x_client, c_delta) = handle.join().unwrap();
            
        // Verify the output
        for j in 0..batch_size{
            let encoded_input = encode_input(inputs[j].clone(), generate_linear_code().0);
            let expected_output = w_prf_clear(key, encoded_input, b);
            for i in 0..82{
                assert_eq!(fk_x_server[j*82 + i].0 + fk_x_client[j*82 + i].0, expected_output[i], "Mismatch at index {}, {}", i, j);
                assert_eq!(fk_x_client[j*82 + i].2.mac(), -fk_x_server[j*82 + i].0*c_delta + fk_x_server[j*82 + i].1.mac(), "Mac mismatch at index {}, {}", i, j);
                assert_eq!(fk_x_server[j*82 + i].2.mac(), -fk_x_client[j*82 + i].0*cdmoprfsender.f3_v.get_delta() + fk_x_client[j*82 + i].1.mac(), "Mac mismatch at index {}, {}", i, j);
            }
        }

    }

	#[test]
	fn test_trait_api() {
		use std::io::{BufReader, BufWriter};
		use std::os::unix::net::UnixStream;

		use rand::SeedableRng;
		use scuttlebutt::{AesRng, Block, Channel};

		use crate::preprocessing::{init_cdm_oprf_receiver, init_cdm_oprf_sender};
		use crate::matrix_util::generate_precompute_tables;
		use crate::full_wPRF::w_prf_clear;

		let seed = Block::from([0u8; 16]);
		let mut rng = AesRng::from_seed(seed);

		// Generate B matrix
		let mut b: [[F3; 256]; 82] = [[F3::ZERO; 256]; 82];
		for i in 0..82 {
			for j in 0..256 {
				b[i][j] = F3::random(&mut rng);
			}
		}

		let bc = generate_precompute_tables(b);
		let bs = bc.clone();

		// Single input
		let input = F128b::random(&mut rng);
		let inputs = vec![input];
		let len = inputs.len();

		let (client, server) = UnixStream::pair().unwrap();

		// === Receiver thread ===
		let handle = std::thread::spawn(move || {
			let mut rng = AesRng::from_seed(seed);
			let reader = BufReader::new(client.try_clone().unwrap());
			let writer = BufWriter::new(client);
			let mut channel = Channel::new(reader, writer);

			let mut receiver = init_cdm_oprf_receiver(
				&mut channel,
				&mut rng,
				len,
				b,
				bc,
				OPRFSetting::RevealOutput,
			);

			// Call via the *trait*
			<CDMOPRFReceiver as Receiver>::receive(
				&mut receiver,
				&mut channel,
				&inputs,
				&mut rng,
			)
			.unwrap()
		});

		// === Sender side ===
		let reader = BufReader::new(server.try_clone().unwrap());
		let writer = BufWriter::new(server);
		let mut channel = Channel::new(reader, writer);

		let mut sender = init_cdm_oprf_sender(
			&mut channel,
			&mut rng,
			len,
			b,
			bs,
			OPRFSetting::RevealOutput,
		);

		let key = sender.fk.get_delta();
		<CDMOPRFSender as Sender>::send(
			&mut sender,
			&mut channel,
			len,
			&mut rng,
		)
		.unwrap();

		let outputs = handle.join().unwrap();

		// === Verify correctness ===
		let encoded = encode_input(input, generate_linear_code().0);
		let expected = w_prf_clear(key, encoded, b);

		for i in 0..82 {
			assert_eq!(
				outputs[i],
				expected[i],
				"Mismatch at output index {}",
				i
			);
		}
	}
}