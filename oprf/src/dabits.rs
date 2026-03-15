use hd_quicksilver::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::FiniteField,
    AbstractChannel,
};

use crate::{daBits_cnc_consistency::{candidate_client, candidate_server, get_bucket_size}, daBits_code_consistency::{code_candidate_client, code_candidate_server, CodeType}, F3triples::{triple_client, triple_server}, F3triples_half_auth::{triple_client_half_auth, triple_server_half_auth}, OPRF::OPRFSetting};

/// Triple over a finite field
#[derive(Default, Clone, Copy, Debug, PartialEq)]
pub struct OPRFSharing<F: FiniteField>(
    /// share value
    pub F::PrimeField,
    /// share tag
    pub MacProver<F>,
    /// share key
    pub MacVerifier<F>,
);

pub struct OPRFExtensionSharing<F: FiniteField>(
    /// Share value
    pub F,
    /// Share mac
    pub F,
    /// Share key
    pub F
);



pub fn dabit_client<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    fcom_p_2: &mut FComProver<Fb>,
    fcom_v_2: &mut FComVerifier<Fb>,
    fcom_p_3: &mut FComProver<Fp>,
    fcom_v_3: &mut FComVerifier<Fp>,
    channel: &mut C,
    rng: &mut RNG,
    setting: OPRFSetting,
) -> Vec<(OPRFSharing<Fb>, OPRFSharing<Fp>)> 
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{
    let bucket_size;
    if output_size < 1<< 14 {
        bucket_size = get_bucket_size(output_size);
    }else if output_size < 1<<16{
        bucket_size = 4;
    }else {
        bucket_size = 3;
    }

    let candidate_tags;
    let candidate_values;
    if output_size < 1<<14{
        candidate_values = candidate_client((output_size, bucket_size, 3), fcom_p_2, fcom_p_3, channel, rng);
        candidate_tags = candidate_server((output_size, bucket_size, 3), fcom_v_2, fcom_v_3, channel, rng);
    }else{
        candidate_values = code_candidate_client(output_size, fcom_p_2, fcom_p_3, channel, rng, &CodeType::Large);
        candidate_tags = code_candidate_server(output_size, fcom_v_2, fcom_v_3, channel, rng, &CodeType::Large);
    }
    
    let triples;
    if setting == OPRFSetting::RevealOutput{
        triples = triple_client_half_auth((output_size, bucket_size, 3), fcom_p_3, fcom_v_3, channel, rng);
    }else {
        triples = triple_client((output_size, bucket_size, 3), fcom_p_3, fcom_v_3, channel, rng);
    }
    let ell = output_size;

    let mut f2_sharings = Vec::with_capacity(ell);
    for i in 0..ell {
        let value = candidate_values.0[i].value();
        let mac = candidate_values.0[i];
        let tag = candidate_tags.0[i];

        let share = OPRFSharing {
            0: value,
            1: mac,
            2: tag,
        };
        f2_sharings.push(share);
    }

    let mut sharings = Vec::with_capacity(ell);

    let mut d_to_open = Vec::with_capacity(ell);
    let mut e_to_open_tag = Vec::with_capacity(ell);

    for i in 0..ell {
        let mac = candidate_values.1[i];
        let tag = candidate_tags.1[i];

        let (a, b, _) = triples[i].clone();
        let d = fcom_p_3.sub(mac, a.1);
        d_to_open.push(d);

        let e_tag = fcom_v_3.sub(tag, b.2);
        e_to_open_tag.push(e_tag);
    }
    fcom_p_3.open(channel, &d_to_open).unwrap();
    channel.flush().unwrap();
    let mut e = Vec::new();
    fcom_v_3.open(channel, &e_to_open_tag, &mut e).unwrap();

    for i in 0..ell {
        let value: Fp::PrimeField = candidate_values.1[i].value();
        let mac = candidate_values.1[i];
        let tag = candidate_tags.1[i];

        let (a, b, c) = triples[i].clone();
        // d*b + e*a + c + d*e
        let mut product_value = fcom_p_3.affine_mult_cst(e[i], a.1);
        product_value = fcom_p_3.add(
            product_value,
            fcom_p_3.affine_mult_cst(d_to_open[i].value(), b.1),
        );
        product_value = fcom_p_3.add(product_value, c.1);
        product_value = fcom_p_3.affine_add_cst(d_to_open[i].value() * e[i], product_value);

        let mut product_tag = fcom_v_3.affine_mult_cst(e[i], a.2);
        product_tag = fcom_v_3.add(
            product_tag,
            fcom_v_3.affine_mult_cst(d_to_open[i].value(), b.2),
        );
        product_tag = fcom_v_3.add(product_tag, c.2);
        //product_tag = fcom_v_3.affine_add_cst(d.value()*e[0], product_tag);

        let share = OPRFSharing {
            0: value - product_value.value() - product_value.value(),
            1: fcom_p_3.sub(fcom_p_3.sub(mac, product_value), product_value),
            2: fcom_v_3.sub(fcom_v_3.sub(tag, product_tag), product_tag),
        };
        sharings.push(share);
    }

    let mut out = Vec::with_capacity(ell);

    for i in 0..ell {
        let a = f2_sharings[i].clone();
        let b = sharings[i].clone();
        out.push((a, b));
    }

    return out;
}

pub fn dabit_server<Fb: FiniteField, Fp: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    output_size: usize,
    fcom_p_2: &mut FComProver<Fb>,
    fcom_v_2: &mut FComVerifier<Fb>,
    fcom_p_3: &mut FComProver<Fp>,
    fcom_v_3: &mut FComVerifier<Fp>,
    channel: &mut C,
    rng: &mut RNG,
    setting: OPRFSetting,
) -> Vec<(OPRFSharing<Fb>, OPRFSharing<Fp>)>
where u8: From<<Fb as FiniteField>::PrimeField>,
Fp::PrimeField: TryFrom<u8>
{
    let bucket_size;
    if output_size < 1<< 14 {
        bucket_size = get_bucket_size(output_size);
    }else if output_size < 1<<16{
        bucket_size = 4;
    }else {
        bucket_size = 3;
    }

    let candidate_tags;
    let candidate_values;
    if output_size < 1<<14{
        candidate_tags = candidate_server((output_size, bucket_size, 3), fcom_v_2, fcom_v_3, channel, rng);
        candidate_values = candidate_client((output_size, bucket_size, 3), fcom_p_2, fcom_p_3, channel, rng);
    }else{
        candidate_tags = code_candidate_server(output_size, fcom_v_2, fcom_v_3, channel, rng, &CodeType::Large);
        candidate_values = code_candidate_client(output_size, fcom_p_2, fcom_p_3, channel, rng, &CodeType::Large);
    }

    let triples; 
    if setting == OPRFSetting::RevealOutput{
        triples = triple_server_half_auth((output_size, bucket_size, 3), fcom_p_3, fcom_v_3, channel, rng);
    }else {
        triples = triple_server((output_size, bucket_size, 3), fcom_p_3, fcom_v_3, channel, rng);
    }
    let ell = output_size;
    let mut f2_sharings = Vec::with_capacity(ell);
    for i in 0..ell {
        let value = candidate_values.0[i].value();
        let mac = candidate_values.0[i];
        let tag = candidate_tags.0[i];

        let share = OPRFSharing {
            0: value,
            1: mac,
            2: tag,
        };
        f2_sharings.push(share);
    }

    let mut sharings = Vec::with_capacity(ell);

    let mut e_to_open = Vec::with_capacity(ell);
    let mut d_to_open_tag = Vec::with_capacity(ell);

    for i in 0..ell {
        let mac = candidate_values.1[i];
        let tag = candidate_tags.1[i];

        let (a, b, _) = triples[i].clone();
        let d_tag = fcom_v_3.sub(tag, a.2);
        d_to_open_tag.push(d_tag);

        let e = fcom_p_3.sub(mac, b.1);
        e_to_open.push(e);
    }

    let mut d = Vec::new();
    fcom_v_3.open(channel, &d_to_open_tag, &mut d).unwrap();
    fcom_p_3.open(channel, &e_to_open).unwrap();
    channel.flush().unwrap();

    for i in 0..ell {
        let value = candidate_values.1[i].value();
        let mac = candidate_values.1[i];
        let tag = candidate_tags.1[i];

        let (a, b, c) = triples[i].clone();
        // d*b + e*a + c + d*e
        let mut product_value = fcom_p_3.affine_mult_cst(e_to_open[i].value(), a.1);
        product_value = fcom_p_3.add(product_value, fcom_p_3.affine_mult_cst(d[i], b.1));
        product_value = fcom_p_3.add(product_value, c.1);
        //product_value = fcom_p_3.affine_add_cst(d[0]*e.value(), product_value);

        let mut product_tag = fcom_v_3.affine_mult_cst(e_to_open[i].value(), a.2);
        product_tag = fcom_v_3.add(product_tag, fcom_v_3.affine_mult_cst(d[i], b.2));
        product_tag = fcom_v_3.add(product_tag, c.2);
        product_tag = fcom_v_3.affine_add_cst(d[i] * e_to_open[i].value(), product_tag);

        let share = OPRFSharing {
            0: value - product_value.value() - product_value.value(),
            1: fcom_p_3.sub(fcom_p_3.sub(mac, product_value), product_value),
            2: fcom_v_3.sub(fcom_v_3.sub(tag, product_tag), product_tag),
        };
        sharings.push(share);
    }

    let mut out = Vec::with_capacity(ell);

    for i in 0..ell {
        let a = f2_sharings[i].clone();
        let b = sharings[i].clone();
        out.push((a, b));
    }

    return out;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        io::{BufReader, BufWriter},
        os::unix::net::UnixStream,
    };

    use ocelot::svole::wykw::{choose_lpn_parameters, LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
    use rand::SeedableRng;
    use scuttlebutt::{
        field::{F64b, F64t, F3}, AesRng, Block, Channel
    };

    use hd_quicksilver::homcom::FComProver;

    #[test]
    fn test_fcom3() {
        let (client, server) = UnixStream::pair().unwrap();
        let seed = Block::from([0; 16]);
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(seed);
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom3 =
                FComProver::<F64t>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL)
                    .unwrap();
            let mut coms = Vec::new();
            for _ in 0..10{
                let com = fcom3.random(&mut channel, &mut rng).unwrap();
                coms.push(com);
            }
            return coms;
        });
        let mut rng = AesRng::from_seed(seed);
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom3 =
            FComVerifier::<F64t>::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL)
                .unwrap();
        let mut coms_s = Vec::new();
        for _ in 0..10{
            let com_s = fcom3.random(&mut channel, &mut rng).unwrap();
            coms_s.push(com_s);
        }

        let com_c = handle.join().unwrap();

        for i in 0..10{
            assert_eq!(coms_s[i].mac(), -(com_c[i].value() * fcom3.get_delta() - com_c[i].mac()));
        }
    }

    #[test]
    fn da_bits_test() {
        let (client, server) = UnixStream::pair().unwrap();
        let ell = 10;
        let output_size = ell;
        let (lpn_setup_params, lpn_extend_params) =
            choose_lpn_parameters::<F3>(ell * 2*2 + 3);
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(client.try_clone().unwrap());
            let writer = BufWriter::new(client);
            let mut channel = Channel::new(reader, writer);
            let mut fcom_p_3 = FComProver::<F64t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let mut fcom_v_3 = FComVerifier::<F64t>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let mut fcom_p_2 = FComProver::<F64b>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();
            let mut fcom_v_2 = FComVerifier::<F64b>::init(
                &mut channel,
                &mut rng,
                lpn_setup_params,
                lpn_extend_params,
            )
            .unwrap();

            let dabits = dabit_client(
                output_size,
                &mut fcom_p_2,
                &mut fcom_v_2,
                &mut fcom_p_3,
                &mut fcom_v_3,
                &mut channel,
                &mut rng,
                OPRFSetting::SecretShareOutput
            );

            return (dabits, fcom_v_2.get_delta(), fcom_v_3.get_delta());
        });
        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(server.try_clone().unwrap());
        let writer = BufWriter::new(server);
        let mut channel = Channel::new(reader, writer);
        let mut fcom_v_3 =
            FComVerifier::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let mut fcom_p_3 =
            FComProver::<F64t>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let mut fcom_v_2 =
            FComVerifier::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();
        let mut fcom_p_2 =
            FComProver::<F64b>::init(&mut channel, &mut rng, lpn_setup_params, lpn_extend_params)
                .unwrap();

        let dabits = dabit_server(
            output_size,
            &mut fcom_p_2,
            &mut fcom_v_2,
            &mut fcom_p_3,
            &mut fcom_v_3,
            &mut channel,
            &mut rng,
            OPRFSetting::SecretShareOutput
        );

        let (dabits_c, delta_2, delta_3) = handle.join().unwrap();

        for i in 0..ell {
            let (a, b) = &dabits[i];
            let (a_c, b_c) = &dabits_c[i];
            let a_real = a.0 + a_c.0;
            let b_real = b.0 + b_c.0;
            let a_int: u8 = a_real.into();
            let b_int: u8 = b_real.into();
            assert_eq!(a_int, b_int);
            assert!(a_int == 0 || a_int == 1);
            assert!(b_int == 0 || b_int == 1);
        }

        for i in 0..ell{
            let (a_s, b_s) = &dabits[i];
            let (a_c, b_c) = &dabits_c[i];
            assert_eq!(a_s.2.mac(), -a_c.0*fcom_v_2.get_delta() + a_c.1.mac());
            assert_eq!(b_s.2.mac(), -b_c.0*fcom_v_3.get_delta() + b_c.1.mac());
            assert_eq!(a_c.2.mac(), -a_s.0*delta_2 + a_s.1.mac());
            assert_eq!(b_c.2.mac(), -b_s.0*delta_3 + b_s.1.mac());
        }
    }
}
