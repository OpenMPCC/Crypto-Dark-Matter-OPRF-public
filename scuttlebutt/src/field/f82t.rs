use std::arch::x86_64::{ __m256i, _mm256_andnot_si256, _mm256_extract_epi64, _mm256_extractf128_si256, _mm256_extracti128_si256, _mm256_insertf128_si256, _mm256_mullo_epi32, _mm256_or_si256, _mm256_set_epi32, _mm256_set_epi64x, _mm256_setzero_si256, _mm256_sll_epi64, _mm256_slli_si256, _mm256_srl_epi64, _mm256_srli_si256, _mm256_xor_si256, _mm_cvtsi32_si128, _mm_extract_epi64};
use std::ops::{AddAssign, Mul, MulAssign, SubAssign};
use bytemuck::Zeroable;
use generic_array::GenericArray;
use rand::SeedableRng;
use smallvec::smallvec;

use subtle::{ConditionallySelectable, ConstantTimeEq};

use crate::ring::{FiniteRing, IsSubRingOf};
use crate::serialization::{BytesDeserializationCannotFail, CanonicalSerialize};
use crate::{AesRng, Block};

use super::convolve::Convolve;
use super::{FiniteField, F3};

use super::IsSubFieldOf;

/// A 64-bit mod 3 field element
#[derive(Debug, Clone, Copy, Hash, Eq)]
pub struct F82t{
    /// Most significat bit
    pub msb: u128,
    /// Least significant bit
    pub lsb: u128,
}

// x^82 + 2x^2 + 1
const BASE: F82t = F82t{msb: 0b0100, lsb: 0b0001};

impl<'a> AddAssign<&'a F82t> for F82t{
    fn add_assign(&mut self, rhs: &'a F82t) {
        let t = (self.lsb | rhs.msb) ^ (self.msb | rhs.lsb);
        let msb = (self.lsb | rhs.lsb) ^ t;
        let lsb = (self.msb | rhs.msb) ^ t;
        self.msb = msb;
        self.lsb = lsb;
    }
}

impl<'a> SubAssign<&'a F82t> for F82t{
    fn sub_assign(&mut self, rhs: &'a F82t) {
        let neg = F82t{msb: rhs.lsb, lsb: rhs.msb};
        *self += &neg;
    }
}

fn reduce(msb_long: (u64, u128), lsb_long: (u64,u128)) -> F82t{
    fn trunc_to_82(x: u128) -> u128 {
        return x & 0x3ffffffffffffffffffff;
    }


    let msb = trunc_to_82(msb_long.1);
    let lsb = trunc_to_82(lsb_long.1);
    let mut reduced: F82t = F82t{msb, lsb};

    // terms reduced once
    // u128 terms
    let msb_low = (msb_long.1 >> 82) as u128;
    let lsb_low = (lsb_long.1 >> 82) as u128;
    reduced += &F82t{msb: lsb_low, lsb: msb_low};
    reduced += &F82t{msb: msb_low << 2, lsb: lsb_low << 2};

    //u64 terms
    let msb_high = (msb_long.0 >> 0) as u128;
    let lsb_high = (lsb_long.0 >> 0) as u128;
    let offset = 128-82;
    reduced += &F82t{msb: lsb_high << offset, lsb: msb_high << offset};
    reduced += &F82t{msb: msb_high << (2+offset), lsb: lsb_high << (2+offset)};

    
    // term that reduces twice
    let i = 34;
    let index_val = ((lsb_long.0 >> (i)) & 1) + ((msb_long.0 >> (i)) & 1)*2;
    let additiona_base = F82t{msb: BASE.msb, lsb: BASE.lsb};
    if index_val == 1{
        reduced += &additiona_base;
    }
    if index_val == 2{
        reduced -= &additiona_base;
    }

    reduced
}

impl<'a> MulAssign<&'a F82t> for F82t{

    fn mul_assign(&mut self, rhs: &'a F82t) {
        unsafe fn add_u256_simd(lhs: (__m256i, __m256i), rhs: (__m256i, __m256i)) -> (__m256i, __m256i) {
            let t2 = _mm256_xor_si256(lhs.0, rhs.0);
            let t3 = _mm256_xor_si256(lhs.1, rhs.1);
            let t1 = _mm256_xor_si256(lhs.1, t2);
            let t0 = _mm256_xor_si256(lhs.0, t3);
            let msb = _mm256_andnot_si256(t3, t1);
            let lsb = _mm256_andnot_si256(t2, t0);
            (msb, lsb)
        }

        unsafe fn shift_u256_simd(v: __m256i, n: i32) -> __m256i{
            if n < 64 {
                let shift = _mm_cvtsi32_si128(n); // load n into low 64 bits
                let shift_inverse = _mm_cvtsi32_si128(64 - n);
                let carry_carry = _mm256_slli_si256(_mm256_srl_epi64(v, shift_inverse), 8);
                let lo = _mm256_extractf128_si256(carry_carry, 1);
                let carry_carry = _mm256_insertf128_si256(_mm256_setzero_si256(), lo, 0);
                //let carry_carry = _mm256_permute2x128_si256::<0x01>(carry_carry, carry_carry);
                let carry = _mm256_srli_si256(_mm256_srl_epi64(v, shift_inverse), 8);
                let carry = _mm256_or_si256(carry, carry_carry);
                
                let shifted = _mm256_sll_epi64(v, shift);
                _mm256_or_si256(shifted, carry)
            } else {
                // Shift by at least 64 bits, move lanes up by one
                let n2 = n - 64;
                let shift2 = _mm_cvtsi32_si128(n2);
                let v_hi = _mm256_srli_si256(v, 8);
                let v_carry = _mm256_slli_si256(v, 8);
                let carry = _mm256_srl_epi64(v, _mm_cvtsi32_si128(64 - n2));

                let lo = _mm256_extractf128_si256(v_carry, 1);
                let lo1 = _mm256_extractf128_si256(carry, 1);
                let v_carry = _mm256_insertf128_si256(_mm256_setzero_si256(), lo, 0);
                let carry = _mm256_insertf128_si256(_mm256_setzero_si256(), lo1, 0);
                //let v_carry = _mm256_permute2x128_si256::<0x01>(v_carry, v_carry);
                let v_hi = _mm256_or_si256(v_hi, v_carry);
                let shifted = _mm256_sll_epi64(v_hi, shift2);
                //let carry = _mm256_permute2x128_si256::<0x01>(carry, carry);
                _mm256_or_si256(shifted, carry)
            }
        }
        
        fn shift_left_reduce(x: F82t) -> F82t{
            let msb = x.msb << 1;
            let lsb = x.lsb << 1;
            let mut reduced = F82t{msb: msb & 0x3ffffffffffffffffffff, lsb: lsb & 0x3ffffffffffffffffffff};
            if x.msb >> 81 == 1{
                reduced += &BASE;
            }
            if x.lsb >> 81 == 1{
                reduced -= &BASE;
            }
            reduced
        }

        #[inline(always)]
        fn two_u128_to_m256i(y: u128, x: u128) -> __m256i {
            unsafe { _mm256_set_epi64x(x as i64, (x >> 64) as i64, y as i64, (y >> 64) as i64) }
        }

        #[inline(always)]
        fn m256i_to_u128_and_u64(v: __m256i) -> (u64, u128) {
            unsafe {
                let high = _mm256_extracti128_si256(v, 0);
                let low = _mm256_extracti128_si256(v, 1);
                let high_u64 = _mm_extract_epi64(high, 1) as u64;
                let high_u128 = (_mm_extract_epi64(low, 0) as u64) as u128;
                let low_u128 = (_mm_extract_epi64(low, 1) as u64) as u128;
                (high_u64, (high_u128 << 64) | low_u128)
            }
        }
        
        
        // Count leading zeros and trailing zeros in both inputs
        // This is non constant time, so it might not be a good idea to use this
        let self_leading = self.msb.leading_zeros().min(self.lsb.leading_zeros());
        let self_trailing = self.msb.trailing_zeros().min(self.lsb.trailing_zeros());
        let rhs_leading = rhs.msb.leading_zeros().min(rhs.lsb.leading_zeros());
        let rhs_trailing = rhs.msb.trailing_zeros().min(rhs.lsb.trailing_zeros());

        let a: F82t;
        let b: F82t;
        let start_index: i32;
        let end_index: i32;

        if (self_leading+self_trailing)>= (rhs_leading+rhs_trailing){
            b = self.clone();
            a = *rhs;
            start_index = (self_trailing/2) as i32;
            end_index = (82 - (self_leading/2)) as i32;
        }else{
            a = self.clone();
            b = *rhs;
            start_index = (rhs_trailing/2) as i32;
            end_index = (82 - (rhs_leading/2)) as i32;
        }

        
        let mut precompute_table = [F82t::ZERO; 13];
        
        precompute_table[0] = F82t::ZERO;
        precompute_table[1] = a;
        precompute_table[4] = -a;
        precompute_table[2] = shift_left_reduce(a);
        precompute_table[3] = precompute_table[2] + a;
        precompute_table[6] = precompute_table[2] - a;
        precompute_table[8] = -precompute_table[2];
        precompute_table[9] = -precompute_table[6];
        precompute_table[12] = -precompute_table[3];
        
        
        let lsb = b.lsb;
        let msb = b.msb;
        
        // make sure rhs_zero is a multiple of 2, by increasing the value
        let loop_iterations = end_index;
        
        let mut msb_long: __m256i = __m256i::zeroed();
        let mut lsb_long: __m256i = __m256i::zeroed();

        let mut avx_table = [(__m256i::zeroed(), __m256i::zeroed()); 13];
        for i in 0..13{
            let pre = precompute_table[i];
            avx_table[i] = (
                two_u128_to_m256i(0u128, pre.msb),
                two_u128_to_m256i(0u128, pre.lsb),
            );
        }

        for i in start_index..loop_iterations{
            let offset = i << 1;
            let lsbs = (lsb >> offset) & 0b11;
            let msbs = (msb >> offset) & 0b11;
            let index_val = (msbs << 2) | lsbs;
            let precompute = avx_table[index_val as usize];
            unsafe {
                let rhs = (shift_u256_simd(precompute.0, i<<1), shift_u256_simd(precompute.1, i<<1));
                
                let lhs = ((msb_long), (lsb_long));
                
                (msb_long, lsb_long) = add_u256_simd(lhs, rhs);
            }
        }
        let msb_long = m256i_to_u128_and_u64(msb_long);
        let lsb_long = m256i_to_u128_and_u64(lsb_long);
        *self = reduce(msb_long, lsb_long);
    }
}

impl ConstantTimeEq for F82t{
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        self.msb.ct_eq(&other.msb) & self.lsb.ct_eq(&other.lsb)
    }
}

impl ConditionallySelectable for F82t{
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        let msb = u128::conditional_select(&a.msb, &b.msb, choice);
        let lsb = u128::conditional_select(&a.lsb, &b.lsb, choice);
        Self{msb, lsb}
    }
}

impl FiniteRing for F82t{
    // TODO these needs to be updated.
    fn from_uniform_bytes(x: &[u8; 16]) -> Self {
        /*
        let buf = <[u8; 16]>::from(*x);
        let mut msb = 0;
        let mut lsb = 0;
        for j in 0..16{
            for i in 0..4{
                let bits = (buf[j] >> (2*i)) & 0b11;
                let value = bits % 3;
                msb = (msb << 1) + ((value >> 1) as u128);
                lsb = (lsb << 1) + ((value & 1) as u128);
            }
        }
        F82t{msb, lsb}
        */
        let buf = <[u8; 16]>::from(*x);
        let seed = Block::from(buf);
        let mut rng = AesRng::from_seed(seed);
        F82t::random(&mut rng)
    }

    fn random<R: rand::Rng + ?Sized>(rng: &mut R) -> Self {
        let a = rng.next_u64();
        let b = rng.next_u64();
        let c = rng.next_u32();
        let d = rng.next_u32();

        let mut lsb: u128 = a as u128;
        let mut msb: u128 = (b  ^ (a & b)) as u128;
        let lsb_extra = c as u128;
        let msb_extra = (d  ^ (c & d)) as u128;
        lsb = ((lsb_extra << 64) | lsb) & 0x3ffffffffffffffffffff;
        msb = ((msb_extra << 64) | msb) & 0x3ffffffffffffffffffff; 
        F82t{msb, lsb}
    }

    const ZERO: Self = Self{msb: 0, lsb: 0};

    const ONE: Self = Self{msb: 0, lsb: 1};

}

impl FiniteField for F82t {
    type PrimeField = F3;

    fn polynomial_modulus() -> super::polynomial::Polynomial<Self::PrimeField> {
        let mut coefficients = smallvec![F3::ZERO; 82];
        let two = F3{msb: 1, lsb: 0};
        coefficients[82 - 1] = F3::ONE;
        coefficients[2 - 1] = two;
        super::polynomial::Polynomial {
            constant: F3::ONE,
            coefficients,
        }
    }

    const GENERATOR: Self = Self{msb: 0, lsb: 0b10};

    type NumberOfBitsInBitDecomposition = generic_array::typenum::U164;

    fn bit_decomposition(&self) -> generic_array::GenericArray<bool, Self::NumberOfBitsInBitDecomposition> {
        let mut bits = generic_array::GenericArray::default();
        for (i, dst) in bits.iter_mut().enumerate() {
            let index = i / 2;
            let bit = (self.lsb & (1 << (index))) != 0;
            let bit_msb = (self.msb & (1 << (index))) != 0;
            *dst = if i % 2 == 0 {
                bit
            } else {
                bit_msb
            };
        }
        bits
    }

    fn inverse(&self) -> Self {
        if *self == Self::ZERO {
            panic!("Zero cannot be inverted");
        }

        fn frob3(x: F82t) -> F82t {
            x*x*x
        }

        let mut t: Vec<F82t> = vec![F82t::ZERO; 82+1];
        t[0] = *self;
        for i in 1..=81{
            let next = frob3(t[i-1]);
            t[i] = next;
        }

        let mut acc = t[81];
        for i in 0..=80{
            let sq = t[i]*t[i]*t[i]*t[i];
            acc = acc * sq;
        }

        acc

    }
}

impl Convolve for F82t {}

impl IsSubRingOf<F82t> for F3 {}
impl IsSubFieldOf<F82t> for F3 {    
    type DegreeModulo = generic_array::typenum::U82;
    
    fn decompose_superfield(fe: &F82t) -> generic_array::GenericArray<Self, Self::DegreeModulo> {
        GenericArray::from_iter(
            (0..82).map(|i| {
                let msb = (fe.msb >> i) & 1;
                let lsb = (fe.lsb >> i) & 1;
                F3::try_from((msb*2 + lsb) as u8).unwrap()
            })
        )
    }
    
    fn form_superfield(components: &generic_array::GenericArray<Self, Self::DegreeModulo>) -> F82t {
        let mut msb = 0;
        let mut lsb = 0;
        for x in components.iter().rev(){
            msb = (msb << 1) + (x.msb as u128);
            lsb = (lsb << 1) + (x.lsb as u128);
        }
        F82t{msb, lsb}
    }
}

impl CanonicalSerialize for F82t{
    type Serializer = crate::serialization::ByteElementSerializer<Self>;

    type Deserializer  = crate::serialization::ByteElementDeserializer<Self>;

    type ByteReprLen = generic_array::typenum::U32;

    type FromBytesError = BytesDeserializationCannotFail;

    fn from_bytes(
        bytes: &generic_array::GenericArray<u8, Self::ByteReprLen>,
    ) -> Result<Self, Self::FromBytesError> {
        let buf = <[u8; 32]>::from(*bytes);
        let msb = u128::from_le_bytes(buf[0..16].try_into().unwrap());
        let lsb = u128::from_le_bytes(buf[16..32].try_into().unwrap());
        Ok(F82t{msb, lsb})
    }

    fn to_bytes(&self) -> generic_array::GenericArray<u8, Self::ByteReprLen> {
        let mut bytes = [0u8; 32];
        let out = self.msb.to_le_bytes();
        bytes[0..16].copy_from_slice(&out);
        let out = self.lsb.to_le_bytes();
        bytes[16..32].copy_from_slice(&out);
        bytes.into()
    }
}

impl Mul<F82t> for F3{
    type Output = F82t;

    fn mul(self, rhs: F82t) -> Self::Output {
        /*
        let msb_mask = 0u128.wrapping_sub(self.msb as u128);
        let lsb_mask = 0u128.wrapping_sub(self.lsb as u128);
        let a = F82t{
            msb: rhs.msb & lsb_mask,
            lsb: rhs.msb & msb_mask,
        };
        let b = F82t{
            msb: rhs.lsb & msb_mask,
            lsb: rhs.lsb & lsb_mask,
        };
        
        b+a
        */
        let msb = rhs.msb * (self.lsb as u128) | rhs.lsb * (self.msb as u128);
        let lsb = rhs.lsb * (self.lsb as u128) | rhs.msb * (self.msb as u128);
        F82t{msb, lsb}
    }
}

impl From<F3> for F82t{
    fn from(pf: F3) -> Self {
        return F82t{msb: pf.msb as u128, lsb: pf.lsb as u128};
    }
}

impl F82t{
    /// Compute two multiplications in parallel using AVX2 instructions
    #[inline(always)]
    fn compute_avx_mul((a,b): (F3,F3), (ax, bx): (F82t, F82t)) -> (__m256i, __m256i){
        let out_a: __m256i;
        let out_b: __m256i;
        unsafe{
            let msb = _mm256_set_epi64x((ax.msb>>64) as i64, ax.msb as i64, (bx.msb>>64) as i64, bx.msb as i64);
            let lsb = _mm256_set_epi64x((ax.lsb>>64) as i64, ax.lsb as i64, (bx.lsb>>64) as i64, bx.lsb as i64);
            let f3_lsb = _mm256_set_epi32(a.lsb as i32, a.lsb as i32, a.lsb as i32, a.lsb as i32, b.lsb as i32, b.lsb as i32, b.lsb as i32, b.lsb as i32);
            let f3_msb = _mm256_set_epi32(a.msb as i32, a.msb as i32, a.msb as i32, a.msb as i32, b.msb as i32, b.msb as i32, b.msb as i32, b.msb as i32);

            out_a = _mm256_or_si256(_mm256_mullo_epi32(msb, f3_lsb),_mm256_mullo_epi32(lsb, f3_msb));
            out_b = _mm256_or_si256(_mm256_mullo_epi32(lsb, f3_lsb),_mm256_mullo_epi32(msb, f3_msb));
        }
        (out_a, out_b)
    }

    /// Compute a vector of multiplications and sum the results using AVX2 instructions
    pub fn compute_vector<const C: usize>(arr: [F3; C], vec: &Vec<F82t>) -> F82t{
        let mut out_msb: __m256i = __m256i::zeroed();
        let mut out_lsb: __m256i = __m256i::zeroed();
        for i in 0..C/2{
            let a = arr[2*i];
            let b = arr[2*i+1];
            let ax = vec[2*i];
            let bx = vec[2*i+1];
            let (res_a, res_b) = F82t::compute_avx_mul((a,b), (ax,bx));

            unsafe{
                let t2 = _mm256_xor_si256(out_msb, res_a);
                let t3 = _mm256_xor_si256(out_lsb, res_b);
                let t1 = _mm256_xor_si256(out_lsb, t2);
                let t0 = _mm256_xor_si256(out_msb, t3);
                out_msb = _mm256_andnot_si256(t3, t1);
                out_lsb = _mm256_andnot_si256(t2, t0);
            }
        }
        let out: F82t;
        unsafe{
            let a: F82t = F82t{
                msb: ((_mm256_extract_epi64(out_msb, 1)as u64) as u128) << 64 | ((_mm256_extract_epi64(out_msb, 0) as u64) as u128),
                lsb: ((_mm256_extract_epi64(out_lsb, 1)as u64) as u128) << 64 | ((_mm256_extract_epi64(out_lsb, 0) as u64) as u128),
            };
            let b = F82t{
                msb: ((_mm256_extract_epi64(out_msb, 3) as u64) as u128) << 64 | ((_mm256_extract_epi64(out_msb, 2) as u64) as u128),
                lsb: ((_mm256_extract_epi64(out_lsb, 3) as u64) as u128) << 64 | ((_mm256_extract_epi64(out_lsb, 2) as u64) as u128),
            };
            out = a + b;
        }

        out
    }
}

field_ops!(F82t);

#[cfg(test)]
mod tests{
    use super::*;

    test_field!(test_field, crate::field::F82t);

    const BASE: F82t = F82t{msb: 0b0100, lsb: 0b0001};
    #[test]
    fn test_mul_identity(){
        let a = F82t{msb: 0, lsb: (1 << 81) + (1 << 30)};
        let b = F82t{msb: 0, lsb: 0b1};
        assert_eq!(a*b, F82t{msb: 0, lsb: (1 << 81) + (1 << 30)});
    }

    #[test]
    fn test_mul_two(){
        let a = F82t{msb: 0, lsb: (1 << 80) + (1 << 30)};
        let b = F82t{msb: 0, lsb: 0b10};
        assert_eq!(b*a, F82t{msb: 0, lsb: (1 << 81) + (1 << 31)});
    }

    #[test]
    fn test_mul_three(){
        let a = F82t{msb: 0, lsb: (1 << 79) + (1 << 30)};
        let b = F82t{msb: 0, lsb: 0b100};
        assert_eq!(a*b, F82t{msb: 0, lsb: (1 << 81) + (1 << 32)});
    }

    #[test]
    fn test_mul_sixty(){
        let a = F82t{msb: 0, lsb: (1 << 79)};
        let b = F82t{msb: 0, lsb: (1 << 60)};
        // x^79 \cdot x^60 = x^139 = x^82 \cdot x^57
        // x^57 \cdot (x^2 + 2) = x^59 + 2x^57
        assert_eq!(b*a, F82t{msb: (1 << 57), lsb: (1 << 59)});
    }
    
    #[test]
    fn test_mul_reduce_1(){
        let a = F82t{msb: 0, lsb: 1 << 81};
        let b = F82t{msb: 0, lsb: 0b10};
        assert_eq!(a*b, -BASE);
    }

    #[test]
    fn test_mul_reduce_multiple(){
        let a = F82t{msb: 0, lsb: 1 << 81};
        let b = F82t{msb: 0, lsb: 0b110};
        assert_eq!(a*b, F82t{msb: 0b011, lsb: 0b1100});
    }

    #[test]
    fn test_mul_reduce_1_msb(){
        let a = F82t{msb: 1 << 81, lsb: 0};
        let b = F82t{msb: 0, lsb: 0b10};
        assert_eq!(a*b, BASE);
    }

    #[test]
    fn test_mul_reduce_1_double_msb(){
        let a = F82t{msb: 1 << 81, lsb: 0};
        let b = F82t{msb: 0b10, lsb: 0};
        assert_eq!(a*b, -BASE);
    }

    #[test]
    fn test_mul_reduce_max(){
        let a = F82t{msb: 0, lsb: 1 << 81};
        let b = F82t{msb: 0, lsb: 1 << 81};
        //x^81 \cdot x^81 = x^162 = x^82 \cdot x^80
        // x^80 \cdot (x^2 + 2) = x^82+ 2x^80 =
        // (x^2 + 2) + 2x^80 = 2x^80 + x^2 + 2
        assert_eq!(a*b, F82t{msb: (1<<80) + 1, lsb: 0b0100});
    }

    #[test]
    fn test_mul_reduce_max_msb(){
        let a = F82t{msb: 1 << 81, lsb: 0};
        let b = F82t{msb: 1 << 81, lsb: 0};
        //2x^81 \cdot 2x^81 = x^162 = x^82 \cdot x^80
        // x^80 \cdot (x^2 + 2) = x^82+ 2x^80 =
        // (x^2 + 2) + 2x^80 = 2x^80 + x^2 + 2
        assert_eq!(a*b, F82t{msb: (1<<80) + 1, lsb: 0b0100});
    }

    #[test]
    fn test_mul_reduce_max_diff(){
        let a = F82t{msb: 1 << 81, lsb: 0};
        let b = F82t{msb: 0, lsb: 1 << 81};
        //2x^81 \cdot 2x^81 = x^162 = x^82 \cdot x^80
        // x^80 \cdot (x^2 + 2) = x^82+ 2x^80 =
        // (x^2 + 2) + 2x^80 = 2x^80 + x^2 + 2
        assert_eq!(a*b, F82t{msb: 0b100, lsb: (1<<80) + 1});
    }

    #[test]
    fn test_mul_reduce_deg_minus_1(){
        let a = F82t{msb: 0, lsb: 1 << 81};
        let b = F82t{msb: 0, lsb: 1 << 80};
        //x^81 \cdot x^80 = x^161 = x^82 \cdot x^79
        // x^79 \cdot (x^2 + 2) = x^81 + 2x^79
        assert_eq!(a*b, F82t{msb: (1<<79) , lsb: (1<<81)});
    }

    #[test]
    fn test_mul_reduce_max_once(){
        let a = F82t{msb: 0, lsb: 1 << 80};
        let b = F82t{msb: 0, lsb: 1 << 80};
        //x^80 \cdot x^80 = x^160 = x^82 \cdot x^78
        // x^78 \cdot (2x^2 + 1) = 2x^80+ x^78
        assert_eq!(a*b, F82t{msb: (1<<78), lsb:  (1<<80)});
    }

    #[test]
    fn test_mul_reduce_max_multiple(){
        let a = F82t{msb: 0, lsb: (1 << 81) + (1<<80) };
        let b = F82t{msb: 0, lsb: (1 << 81)};
        // (x^81 + x^80) * x^81 = x^162 + x^161 = x^82*x^80 + x^82*x^79
        // x^80*(x^2 + 2) + x^79*(x^2 + 2) = x^82 + 2x^80 + x^81 + 2x^79 = 
        // (x^2 + 2) + x^81 + 2x^80 + 2x^79
        assert_eq!(a*b, F82t{msb: (1<<80) + (1<<79) + 1, lsb:  (1<<81) + (1<<2)});
    }

    #[test]
    fn test_mul_assoc(){
        let a = F82t{msb: 1<< 73, lsb: 1 << 81};
        let b = F82t{msb: 1<< 2, lsb: 1 << 80};
        let c = F82t{msb: 1<< 30, lsb: 1 << 79};
        //x^80 \cdot x^80 = x^160 = x^82 \cdot x^78
        // x^78 \cdot (2x^2 + 1) = 2x^80+ x^78
        assert_eq!(a*b*c, a*(b*c));
    }

    #[test]
    fn test_mul_inverse(){
        let a = F82t{msb: 0, lsb: 0b10};
        let b = a.inverse();
        assert_eq!(a*b, F82t::ONE);
    }
}
