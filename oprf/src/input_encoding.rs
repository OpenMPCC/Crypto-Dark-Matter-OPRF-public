use std::u8;

use rand::SeedableRng;
use scuttlebutt::{field::{F128b, F256b, F64t, F82t, FiniteField, F2, F3}, ring::FiniteRing, AesRng};

pub const D: usize = 128;
pub const N_PRIME: usize = 128 + 63;

pub fn decompose(input: [F3; N_PRIME]) -> [F2; D + 2*(N_PRIME-D)]{
    let mut decompose = [F2::ZERO; D + 2*(N_PRIME-D)];
    for i in 0..D {
        let u8_value: u8 = input[i].into();
        decompose[(N_PRIME - D) + i] = F2::try_from(u8_value).unwrap();
    }
    for i in 0..(N_PRIME - D) {
        let u8_value: u8 = input[D + i].into();
        decompose[i] = F2::try_from((u8_value >> 1) & 1).unwrap();
        decompose[N_PRIME - D + i + D] = F2::try_from(u8_value & 1).unwrap();
    }
    decompose
}

pub fn apply_gadget_convert<Fb: FiniteRing, Fp: FiniteRing>(input: [Fb; D + 2*(N_PRIME-D)], gadget: [[Fp; 2*(N_PRIME)]; N_PRIME])
-> [Fp; N_PRIME]
where 
    Fb: Into<u8>,
    Fp: TryFrom<u8>,
{
    let mut output = [Fp::ZERO; N_PRIME];
    let mut extended_input = [Fb::ZERO; 2*(128+63)];
    for i in 0..D{
        extended_input[i] = Fb::ZERO;
    }
    for i in D..2*N_PRIME{
        extended_input[i] = input[i - D];
    }

    for i in 0..N_PRIME{
        let mut value_i = Fp::ZERO;
        let g_2 = gadget[i][i];
        let g_1 = gadget[i][i+N_PRIME];
        let input_2: u8 = extended_input[i].into();
        let input_1: u8 = extended_input[i+N_PRIME].into();
        let conversion_2 = Fp::try_from(input_2);
        match conversion_2 {
            Ok(value) => value_i += g_2 * value,
            Err(_) => panic!("Failed to convert input_j to Fp"),
        }
        let conversion_1 = Fp::try_from(input_1);
        match conversion_1 {
            Ok(value) => value_i += g_1 * value,
            Err(_) => panic!("Failed to convert input_j to Fp"),
        }
        output[i] = value_i;
    }

    output
}

pub fn apply_gadget<F: FiniteField>(input: [F; D + 2*(N_PRIME-D)], gadget: [[F3; 2*(N_PRIME)]; N_PRIME])
-> [F; N_PRIME]
where scuttlebutt::field::F3: std::ops::Mul<F, Output = F>
{
    let mut output = [F::ZERO; N_PRIME];
    let mut extended_input = [F::ZERO; 2*(128+63)];
    for i in D..2*N_PRIME{
        extended_input[i] = input[i - D];
    }

    for i in 0..N_PRIME{
        let g_2 = gadget[i][i];
        let g_1 = gadget[i][i+N_PRIME];
        let mut value_i = g_2 * extended_input[i];
        value_i += g_1 * extended_input[i+N_PRIME];
        output[i] = value_i;
    }
    output
}

pub fn apply_parity_check_matrix_f64t(input: [F64t; N_PRIME], h:[[F3; N_PRIME]; N_PRIME-D]) 
-> [F64t; N_PRIME-D] 
{
    let mut output = [F64t::ZERO; N_PRIME - D];
    for i in 0..(N_PRIME - D){
        let h_arr: [F3; D] = h[i][0..D].try_into().unwrap();
        let mut value_i = F64t::compute_vector(h_arr, &input.to_vec());
        value_i += input[i+D];
        output[i] = value_i;
    }
    output
}

pub fn apply_parity_check_matrix_f82t(input: [F82t; N_PRIME], h:[[F3; N_PRIME]; N_PRIME-D]) 
-> [F82t; N_PRIME-D] 
{
    let mut output = [F82t::ZERO; N_PRIME - D];
    for i in 0..(N_PRIME - D){
        let h_arr: [F3; D] = h[i][0..D].try_into().unwrap();
        let mut value_i = F82t::compute_vector(h_arr, &input.to_vec());
        value_i += input[i+D];
        output[i] = value_i;
    }
    output
}

pub fn apply_parity_check_matrix<F: FiniteField>(input: [F; N_PRIME], h:[[F3; N_PRIME]; N_PRIME-D]) 
-> [F; N_PRIME-D] 
where scuttlebutt::field::F3: std::ops::Mul<F, Output = F>
{
    let mut output = [F::ZERO; N_PRIME - D];
    for i in 0..(N_PRIME - D){
        let mut value_i = F::ZERO;
        for j in 0..D{
            let h_ij = h[i][j];
            value_i += h_ij * input[j];
        }
        value_i += input[i+D];
        output[i] = value_i;
    }
    output
}

pub fn encode_input(input: F128b, g: [[F3; D]; N_PRIME]) -> F256b{
    //apply G
    let mut gx = Vec::with_capacity(N_PRIME);
    let input:u128 = input.into();
    for i in 0..D{
        let input_i = ((input >> i) & 1) as u8;
        let value = F3{msb: 0, lsb: input_i};
        gx.push(value);
    }
    for i in D..N_PRIME{
        let mut value_i = F3::ZERO;
        for j in 0..D{
            let g_ij = g[i][j];
            let input_j = ((input >> j) & 1) as u8;
            value_i += g_ij * F3{msb: 0, lsb: input_j};
        }
        gx.push(value_i);
    }

    // Decompose last n'-d coordinate of Gx
    let decompose = decompose(gx.try_into().unwrap());
    let mut decompose_vec = decompose.to_vec();
    decompose_vec.push(F2::ONE); // Append 1 for security
    decompose_vec.push(F2::ONE); // Append 1 to match d+2*(n' - d) + 2 = power of 2
    assert_eq!(decompose_vec.len(), 256);

    // Convert into F256b
    let mut low = 0u128;
    let mut high = 0u128;
    for i in 0..128{
        low |= (u8::from(decompose_vec[i+128]) as u128) << (127-i);
        high |= (u8::from(decompose_vec[i]) as u128) << (127-i);
    }

    F256b{high, low}
}

pub fn generate_linear_code() -> 
([[F3; 128]; 128+63], [[F3; 2*(128+63)]; 128 + 63], [[F3; 128+63]; 63]) {
    let mut g = [[F3::ZERO; 128]; 128 + 63];
    let mut h = [[F3::ZERO; 128 + 63]; 63];
    let mut g_gadget = [[F3::ZERO; 2*(128+63)]; 128 + 63];
    let mut rng = AesRng::from_seed(Default::default());
    for i in 0..128{
        g[i][i] = F3::ONE;
    }
    for i in 128..(128+63){
        for j in 0..128{
            let value = F3::random(&mut rng);
            g[i][j] = value;
            h[i-128][j] = -value;
        }
    }
    for i in 0..63 {
        h[i][i+128] = F3::ONE;
    }
    
    for i in 0..(128+63){
        g_gadget[i][i] = F3::ONE+F3::ONE;
        g_gadget[i][i+128+63] = F3::ONE;
    }
    
    (g, g_gadget, h)
}

#[cfg(test)]
mod test{
    use rand::SeedableRng;
    use scuttlebutt::{field::{F128b, F3}, AesRng, Block};
    use super::*;

    #[test]
    fn test_generator(){
        let (g, gadget, h) = generate_linear_code();
        for i in 0..128{
            let mut sum = 0;
            for j in 0..128{
                sum += u8::from(g[i][j]);
            }
            assert_eq!(sum, 1, "Row {} of G should sum to 1", i);
        }
        for i in 128..(128+63){
            let mut sum = 0;
            for j in 0..128{
                sum += u8::from(g[i][j]);
            }
            assert!(sum > 0, "Row {} of G should sum to more than 0 with 2^{{-128}} probability", i);
        }

        for i in 0..63{
            let mut sum = 0;
            for j in 0..63{
                sum  += u8::from(h[i][j+128]);
            }
            assert_eq!(sum, 1, "Row {} the last (N' - D) of H should sum to 1", i);
        }

        for i in 0..(128+63){
            let mut sum = 0;
            for j in 0..2*(128+63){
                sum += u8::from(gadget[i][j]);
            }
            assert_eq!(sum, 3, "Row {} of gadget should sum to 3", i);
        }
    }

    #[test]
    fn test_decompose_gadget(){
        let seed = Block::from([0; 16]);
        let mut rng = AesRng::from_seed(seed);
        let mut input = [F3::ZERO; N_PRIME];
        for i in 0..D/2 {
            input[i] = F3::ONE;
            input[i+1] = F3::ZERO;
        }
        for i in D..N_PRIME{
            input[i] = F3::random(&mut rng);
        }

        let decompose = decompose(input);
        assert_eq!(decompose.len(), D + 2*(N_PRIME - D));

        let (_, g_gadget, _) = generate_linear_code();

        let output = apply_gadget_convert(decompose, g_gadget);
        assert_eq!(output.len(), N_PRIME);
        for i in 0..D {
            assert_eq!(output[i], input[i], "Output at index {} should match input", i);
        }

    }

    #[test]
    fn test_parity_check(){
        let seed = Block::from([0; 16]);
        let mut rng = AesRng::from_seed(seed);
        let (g, g_gadget, h) = generate_linear_code();

        for _ in 0..25{
            let input = F128b::random(&mut rng);
            let encoded = encode_input(input, g);
            let mut decomp_encoded = [F2::ZERO; D + 2*(N_PRIME - D)];
            for i in 0..D {
                decomp_encoded[i] = F2::try_from((encoded.high >> (127-i)) & 1).unwrap();
            }
            for i in D..(D + 2*(N_PRIME - D)) {
                decomp_encoded[i] = F2::try_from((encoded.low >> (127-(i - D))) & 1).unwrap();
            }

            let gadget = apply_gadget_convert(decomp_encoded, g_gadget);
            let parity_check = apply_parity_check_matrix(gadget, h);

            for i in 0..(N_PRIME - D) {
                assert_eq!(parity_check[i], F3::ZERO, "Parity check failed at index {}", i);
            }
    }
        
    }
}
