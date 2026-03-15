use std::arch::x86_64::{__m128i, __m256i, _mm256_and_si256, _mm256_andnot_si256, _mm256_extracti128_si256, _mm256_set_epi64x, _mm256_xor_si256, _mm_andnot_si128, _mm_extract_epi64, _mm_set_epi64x, _mm_xor_si128};
use std::cmp::min;
use std::ops::{AddAssign, Mul, MulAssign, SubAssign};
use bytemuck::Zeroable;
use generic_array::GenericArray;
use smallvec::smallvec;

use subtle::{ConditionallySelectable, ConstantTimeEq};

use crate::ring::{FiniteRing, IsSubRingOf};
use crate::serialization::{BytesDeserializationCannotFail, CanonicalSerialize};

use super::convolve::Convolve;
use super::{FiniteField, F3};

use super::IsSubFieldOf;

/// A 64-bit mod 3 field element
#[derive(Debug, Clone, Copy, Hash, Eq)]
pub struct F64t{
    /// Most significat bit
    pub msb: u64,
    /// Least significant bit
    pub lsb: u64,
}

// x^64 + x^3 + 2
const BASE: F64t = F64t{msb: 0b0001, lsb: 0b1000};

impl<'a> AddAssign<&'a F64t> for F64t{
    fn add_assign(&mut self, rhs: &'a F64t) {
        let t = (self.lsb | rhs.msb) ^ (self.msb | rhs.lsb);
        let msb = (self.lsb | rhs.lsb) ^ t;
        let lsb = (self.msb | rhs.msb) ^ t;
        self.msb = msb;
        self.lsb = lsb;
    }
}

impl<'a> SubAssign<&'a F64t> for F64t{
    fn sub_assign(&mut self, rhs: &'a F64t) {
        let neg = F64t{msb: rhs.lsb, lsb: rhs.msb};
        *self += neg;
    }
}

fn reduce(msb_long: u128, lsb_long: u128) -> F64t{
    let msb = (msb_long) as u64;
    let lsb = (lsb_long) as u64;
    let mut reduced: F64t = F64t{msb, lsb};

    // terms reduced once
    let msb_h = (msb_long >> 64) as u64;
    let lsb_h = (lsb_long >> 64) as u64;
    reduced += F64t{msb: msb_h, lsb: lsb_h};
    reduced += F64t{msb: lsb_h << 3, lsb: msb_h << 3};

    // term that reduces twice

    let i = 61;
    let index_val = ((lsb_long >> (i+64)) & 1) + ((msb_long >> (i+64)) & 1)*2;
    if index_val == 1{
        reduced += &BASE;
    }
    if index_val == 2{
        reduced -= &BASE;
    }
    
    let i = 62;
    let index_val = ((lsb_long >> (i+64)) & 1) + ((msb_long >> (i+64)) & 1)*2;
    let additiona_base = F64t{msb: BASE.msb << 1, lsb: BASE.lsb << 1};
    if index_val == 1{
        reduced += additiona_base;
    }
    if index_val == 2{
        reduced -= additiona_base;
    }

    reduced
}

impl<'a> MulAssign<&'a F64t> for F64t{

    fn mul_assign(&mut self, rhs: &'a F64t) {
        unsafe fn add_u128_simd(lhs: (__m128i, __m128i), rhs: (__m128i, __m128i)) -> (__m128i, __m128i) {
            let t2 = _mm_xor_si128(lhs.0, rhs.0);
            let t3 = _mm_xor_si128(lhs.1, rhs.1);
            let t1 = _mm_xor_si128(lhs.1, t2);
            let t0 = _mm_xor_si128(lhs.0, t3);
            let msb = _mm_andnot_si128(t3, t1);
            let lsb = _mm_andnot_si128(t2, t0);
            (msb, lsb)
        }
        
        fn shift_left_reduce(x: F64t) -> F64t{
            let msb = x.msb << 1;
            let lsb = x.lsb << 1;
            let mut reduced = F64t{msb, lsb};
            if x.msb >> 63 == 1{
                reduced += BASE;
            }
            if x.lsb >> 63 == 1{
                reduced -= BASE;
            }
            reduced
        }

        #[inline(always)]
        fn u128_to_m128i(x: u128) -> __m128i {
            unsafe { _mm_set_epi64x((x >> 64) as i64, x as i64) }
        }

        #[inline(always)]
        fn m128i_to_u128(v: __m128i) -> u128 {
            unsafe {
                let arr: [u64; 2] = core::mem::transmute(v);
                ((arr[1] as u128) << 64) | (arr[0] as u128)
            }
        }
        
        // Count leading zero of self.lsb
        let self_zero = min(self.msb.leading_zeros(), self.lsb.leading_zeros());
        let rhs_zero = min(rhs.msb.leading_zeros(), rhs.lsb.leading_zeros());
        
        let mut set = 64 - rhs_zero;
        let mut a = self.clone();
        let mut b = *rhs;
        if self_zero > rhs_zero{
            set = 64 - self_zero;
            a = *rhs;
            b = self.clone();
        } 
        
        let mut precompute_table = [F64t::ZERO; 13];
        
        precompute_table[0] = F64t::ZERO;
        precompute_table[1] = a;
        precompute_table[4] = -a;
        precompute_table[2] = shift_left_reduce(a);
        precompute_table[3] = precompute_table[2] + a;
        precompute_table[6] = precompute_table[2] - a;
        precompute_table[8] = -precompute_table[2];
        precompute_table[9] = -precompute_table[6];
        precompute_table[12] = -precompute_table[3];
        
        
        let mut msb_long: __m128i = __m128i::zeroed();
        let mut lsb_long: __m128i = __m128i::zeroed();
        let lsb = b.lsb;
        let msb = b.msb;

        // make sure rhs_zero is a multiple of 2, by increasing the value
        let loop_iterations = set/2 + (set&1);

        for i in 0..loop_iterations{
            let offset = i << 1;
            let lsbs = (lsb >> offset) & 0b11;
            let msbs = (msb >> offset) & 0b11;
            let index_val = (msbs << 2) | lsbs;
            let precompute = precompute_table[index_val as usize];
            unsafe {
                let rhs = (
                    u128_to_m128i((precompute.msb as u128) << (i << 1)),
                    u128_to_m128i((precompute.lsb as u128) << (i << 1)),
                );
                
                let lhs = ((msb_long), (lsb_long));
                
                (msb_long, lsb_long) = add_u128_simd(lhs, rhs);
            }
        }
        let msb_long = m128i_to_u128(msb_long);
        let lsb_long = m128i_to_u128(lsb_long);
        *self = reduce(msb_long, lsb_long);
    }
}

impl ConstantTimeEq for F64t{
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        self.msb.ct_eq(&other.msb) & self.lsb.ct_eq(&other.lsb)
    }
}

impl ConditionallySelectable for F64t{
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        let msb = u64::conditional_select(&a.msb, &b.msb, choice);
        let lsb = u64::conditional_select(&a.lsb, &b.lsb, choice);
        Self{msb, lsb}
    }
}

impl FiniteRing for F64t{
    fn from_uniform_bytes(x: &[u8; 16]) -> Self {
        let buf = <[u8; 16]>::from(*x);
        let mut msb = 0;
        let mut lsb = 0;
        for j in 0..16{
            for i in 0..4{
                let bits = (buf[j] >> (2*i)) & 0b11;
                let value = bits % 3;
                msb = (msb << 1) + ((value >> 1) as u64);
                lsb = (lsb << 1) + ((value & 1) as u64);
            }
        }
        F64t{msb, lsb}
    }

    fn random<R: rand::Rng + ?Sized>(rng: &mut R) -> Self {
        let a = rng.next_u64();
        let b = rng.next_u64();
        let c: u128 = ((a as u128) << 64) + (b as u128);
        let buf = c.to_le_bytes();
        let mut msb = 0;
        let mut lsb = 0;
        for j in 0..16{
            for i in 0..4{
                let bits = (buf[j] >> (2*i)) & 0b11;
                let value = bits % 3;
                msb = (msb << 1) + ((value >> 1) as u64);
                lsb = (lsb << 1) + ((value & 1) as u64);
            }
        }
        F64t{msb, lsb}
    }

    const ZERO: Self = Self{msb: 0, lsb: 0};

    const ONE: Self = Self{msb: 0, lsb: 1};

}

impl FiniteField for F64t {
    type PrimeField = F3;

    fn polynomial_modulus() -> super::polynomial::Polynomial<Self::PrimeField> {
        let mut coefficients = smallvec![F3::ZERO; 64];
        let two = F3{msb: 1, lsb: 0};
        coefficients[64 - 1] = F3::ONE;
        coefficients[3 - 1] = F3::ONE;
        super::polynomial::Polynomial {
            constant: two,
            coefficients,
        }
    }

    const GENERATOR: Self = Self{msb: 0, lsb: 0b10};

    type NumberOfBitsInBitDecomposition = generic_array::typenum::U128;

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
        
        /*
        for i in 0..64{
            bits[2*i] = ((self.lsb >> i) & 1) != 0;
            bits[2*i+1] = ((self.msb >> i) & 1) != 0;
        }
        */
        bits
    }

    fn inverse(&self) -> Self {
        if *self == Self::ZERO {
            panic!("Zero cannot be inverted");
        }
        let base: u128 = 3;
        self.pow_var_time(base.pow(64) - 2)
    }
}

impl Convolve for F64t {}

impl IsSubRingOf<F64t> for F3 {}
impl IsSubFieldOf<F64t> for F3 {    
    type DegreeModulo = generic_array::typenum::U64;
    
    fn decompose_superfield(fe: &F64t) -> generic_array::GenericArray<Self, Self::DegreeModulo> {
        GenericArray::from_iter(
            (0..64).map(|i| {
                let msb = (fe.msb >> i) & 1;
                let lsb = (fe.lsb >> i) & 1;
                F3::try_from((msb*2 + lsb) as u8).unwrap()
            })
        )
    }
    
    fn form_superfield(components: &generic_array::GenericArray<Self, Self::DegreeModulo>) -> F64t {
        let mut msb = 0;
        let mut lsb = 0;
        for x in components.iter().rev(){
            msb = (msb << 1) + (x.msb as u64);
            lsb = (lsb << 1) + (x.lsb as u64);
        }
        F64t{msb, lsb}
    }
}

impl CanonicalSerialize for F64t{
    type Serializer = crate::serialization::ByteElementSerializer<Self>;

    type Deserializer  = crate::serialization::ByteElementDeserializer<Self>;

    type ByteReprLen = generic_array::typenum::U16;

    type FromBytesError = BytesDeserializationCannotFail;

    fn from_bytes(
        bytes: &generic_array::GenericArray<u8, Self::ByteReprLen>,
    ) -> Result<Self, Self::FromBytesError> {
        let buf = <[u8; 16]>::from(*bytes);
        let msb = u64::from_le_bytes(buf[0..8].try_into().unwrap());
        let lsb = u64::from_le_bytes(buf[8..16].try_into().unwrap());
        Ok(F64t{msb, lsb})
    }

    fn to_bytes(&self) -> generic_array::GenericArray<u8, Self::ByteReprLen> {
        let mut bytes = [0u8; 16];
        let out = self.msb.to_le_bytes();
        bytes[0..8].copy_from_slice(&out);
        let out = self.lsb.to_le_bytes();
        bytes[8..16].copy_from_slice(&out);
        bytes.into()
    }
}

impl Mul<F64t> for F3{
    type Output = F64t;

    fn mul(self, rhs: F64t) -> Self::Output {
        let msb_mask = 0u64.wrapping_sub(self.msb as u64);
        let lsb_mask = 0u64.wrapping_sub(self.lsb as u64);
        let a = F64t{
            msb: rhs.msb & lsb_mask,
            lsb: rhs.msb & msb_mask,
        };
        let b = F64t{
            msb: rhs.lsb & msb_mask,
            lsb: rhs.lsb & lsb_mask,
        };
        
        b+a
    }
}

impl F64t{
    /// Compute two multiplications in parallel using AVX2 instructions
    #[inline(always)]
    fn compute_avx_mul((a,b,c,d): (F3,F3,F3,F3), (ax, bx,cx,dx): (F64t, F64t, F64t, F64t)) -> (__m256i, __m256i){
        let a_msb_mask = 0u64.wrapping_sub(a.msb as u64);
        let a_lsb_mask = 0u64.wrapping_sub(a.lsb as u64);
        let b_msb_mask = 0u64.wrapping_sub(b.msb as u64);
        let b_lsb_mask = 0u64.wrapping_sub(b.lsb as u64);
        let c_msb_mask = 0u64.wrapping_sub(c.msb as u64);
        let c_lsb_mask = 0u64.wrapping_sub(c.lsb as u64);
        let d_msb_mask = 0u64.wrapping_sub(d.msb as u64);
        let d_lsb_mask = 0u64.wrapping_sub(d.lsb as u64);

        let out_a: __m256i;
        let out_b: __m256i;
        unsafe{

            // Setup terms
            let a_double_lsb = _mm256_set_epi64x(ax.msb as i64, bx.msb as i64, cx.msb as i64, dx.msb as i64);
            let lsb_mask = _mm256_set_epi64x(a_lsb_mask as i64, b_lsb_mask as i64, c_lsb_mask as i64, d_lsb_mask as i64);
            let msb_mask = _mm256_set_epi64x(a_msb_mask as i64, b_msb_mask as i64, c_msb_mask as i64, d_msb_mask as i64);
            let a_double_msb = _mm256_and_si256(a_double_lsb, lsb_mask);
            let a_double_lsb = _mm256_and_si256(a_double_lsb, msb_mask);
            
            let b_double_lsb = _mm256_set_epi64x(ax.lsb as i64, bx.lsb as i64, cx.lsb as i64, dx.lsb as i64);
            let b_double_msb = _mm256_and_si256(b_double_lsb, msb_mask);
            let b_double_lsb = _mm256_and_si256(b_double_lsb, lsb_mask);

            // Add terms together
            let t2 = _mm256_xor_si256(a_double_msb, b_double_msb);
            let t3 = _mm256_xor_si256(a_double_lsb, b_double_lsb);
            let t1 = _mm256_xor_si256(a_double_lsb, t2);
            let t0 = _mm256_xor_si256(a_double_msb, t3);
            out_a = _mm256_andnot_si256(t3, t1);
            out_b = _mm256_andnot_si256(t2, t0);

        }
        (out_a, out_b)
    }

    /// Compute a vector of multiplications and sum the results using AVX2 instructions
    pub fn compute_vector<const C: usize>(arr: [F3; C], vec: &Vec<F64t>) -> F64t{
        let mut out_msb: __m256i = __m256i::zeroed();
        let mut out_lsb: __m256i = __m256i::zeroed();
        for i in 0..C/4{
            let a = arr[4*i];
            let b = arr[4*i+1];
            let c = arr[4*i+2];
            let d = arr[4*i+3];
            let ax = vec[4*i];
            let bx = vec[4*i+1];
            let cx = vec[4*i+2];
            let dx = vec[4*i+3];
            let (res_a, res_b) = F64t::compute_avx_mul((a,b,c,d), (ax,bx,cx,dx));

            unsafe{
                let t2 = _mm256_xor_si256(out_msb, res_a);
                let t3 = _mm256_xor_si256(out_lsb, res_b);
                let t1 = _mm256_xor_si256(out_lsb, t2);
                let t0 = _mm256_xor_si256(out_msb, t3);
                out_msb = _mm256_andnot_si256(t3, t1);
                out_lsb = _mm256_andnot_si256(t2, t0);
            }
        }
        let out: F64t;
        unsafe{
            let a_msb = _mm256_extracti128_si256(out_msb, 1);
            let a_lsb = _mm256_extracti128_si256(out_lsb, 1);
            let b_msb = _mm256_extracti128_si256(out_msb, 0);
            let b_lsb = _mm256_extracti128_si256(out_lsb, 0);

            // Add sub results together
            let t2 = _mm_xor_si128(a_msb, b_msb);
            let t3 = _mm_xor_si128(a_lsb, b_lsb);
            let t1 = _mm_xor_si128(a_lsb, t2);
            let t0 = _mm_xor_si128(a_msb, t3);
            let out_a = _mm_andnot_si128(t3, t1);
            let out_b = _mm_andnot_si128(t2, t0);

            let a: F64t = F64t{
                msb: _mm_extract_epi64(out_a, 1) as u64,
                lsb: _mm_extract_epi64(out_b, 1) as u64,
            };
            let b = F64t{
                msb: _mm_extract_epi64(out_a, 0) as u64,
                lsb: _mm_extract_epi64(out_b, 0) as u64,
            };
            out = a + b;
        }

        out
    }
}


impl From<F3> for F64t{
    fn from(pf: F3) -> Self {
        return F64t{msb: pf.msb as u64, lsb: pf.lsb as u64};
        /*
        if pf == F3::ZERO {return F64t::ZERO;}
        if pf == F3::ONE {return F64t::ONE;}
        return F64t{msb: 1, lsb: 0};
        */
    }
}

field_ops!(F64t);

#[cfg(test)]
mod tests{
    use super::*;

    test_field!(test_field, crate::field::F64t);

    #[test]
    fn test_mul_small(){
        let a = F64t{msb: 0b0, lsb: 0b10};
        let b = F64t{msb: 0b0, lsb: 0b10};
        let c = a * b;
        assert_eq!(c, F64t{msb: 0b0, lsb: 0b100})
    }

    #[test]
    fn test_mul(){
        // 2x^3+ 2x^2 +x
        let a = F64t{msb: 0b0010, lsb: 0b1100};
        // 2x^3 + x^2 + 2x
        let b = F64t{msb: 0b100, lsb: 0b10000};
        // x^6 + 2*x^4 + 2*x^3 + 2*x^2
        let c = a * b;
        assert_eq!(c, F64t{msb: 0b10000, lsb: 0b11101000})
    }

    #[test]
    fn test_mul_reduce_1(){
        let a = F64t{msb: 0, lsb: 1 << 63};
        let b = F64t{msb: 0, lsb: 0b10};
        assert_eq!(a*b, F64t{msb: 0b1000, lsb: 1});
    }

    #[test]
    fn test_mul_reduce_multiple(){
        let a = F64t{msb: 0, lsb: 1 << 63};
        let b = F64t{msb: 0, lsb: 0b110};
        assert_eq!(a*b, F64t{msb: 0b11000, lsb: 0b11});
    }

    #[test]
    fn test_mul_reduce_1_msb(){
        let a = F64t{msb: 1 << 63, lsb: 0};
        let b = F64t{msb: 0b10, lsb: 0};
        assert_eq!(a*b, F64t{msb: 0b1000, lsb: 1});
    }

    #[test]
    fn test_mul_reduce_1_mix(){
        let a = F64t{msb: 1 << 63, lsb: 0};
        let b = F64t{msb: 0, lsb: 0b10};
        assert_eq!(a*b, F64t{msb: 1, lsb: 0b1000});
    }

    #[test]
    fn test_mul_reduce_degree_124(){
        let a = F64t{msb: 1 << 63, lsb: 0};
        let b = F64t{msb: 0, lsb: 1 << 61};
        assert_eq!(a*b, F64t{msb: 1<<60, lsb: 1<<63});
    }

    #[test]
    fn test_mul_reduce_degree_125_2(){
        let a = F64t{msb: 1 << 63, lsb: 0};
        let b = F64t{msb: 0, lsb: 1 << 62};
        assert_eq!(a*b, F64t{msb: (1<<61) + 0b1000, lsb: 1});
    }

    #[test]
    fn test_mul_reduce_degree_125_1(){
        let a = F64t{msb: 0, lsb: 1 << 63};
        let b = F64t{msb: 0, lsb: 1 << 62};
        assert_eq!(a*b, F64t{msb: 1, lsb: (1<<61) + 0b1000});
    }

    #[test]
    fn test_mul_reduce_degree_126_1(){
        let a = F64t{msb: 0, lsb: 1 << 63};
        let b = F64t{msb: 0, lsb: 1 << 63};
        assert_eq!(a*b, F64t{msb: 0b10, lsb: (1<<62) + 0b10000});
    }

    #[test]
    fn test_mul_reduce_degree_126_2(){
        let a = F64t{msb: 0, lsb: 1 << 63};
        let b = F64t{msb: 1 << 63, lsb: 0};
        assert_eq!(a*b, F64t{msb: (1<<62) + 0b10000, lsb: 0b10});
    }

    #[test]
    fn test_mul_inverse(){
        let a = F64t{msb: 0, lsb: 0b10};
        let b = a.inverse();
        assert_eq!(a*b, F64t::ONE);
    }


    #[test]
    fn test_decompose_compose(){
        let a = F64t{msb: 0, lsb: 0b10};
        let b = F3::decompose_superfield(&a);
        let c = F3::form_superfield(&b);
        assert_eq!(a, c);
    }

    #[test]
    fn test_generator(){
        let a = F64t::GENERATOR;
        let prime_factors: Vec<u128> = vec![274177, 6700417, 641, 65537, 257, 17, 5, 3];
        for p in prime_factors.iter() {
            let p = *p;
            assert_ne!(F64t::ONE, a.pow(p));
        }
        let base: u128 = 3;
        let order = base.pow(64) - 1;
        assert_eq!(F64t::ONE, a.pow(order));
    }

    #[test]
    fn test_generator_unique(){
        for _ in 0..100{
            let x = F64t::random(&mut rand::thread_rng());
            let subfield = F3::decompose_superfield(&x);
            let mut y = F64t::ZERO;
            for i in 0..64{
                let term = subfield[i] * F64t::GENERATOR.pow(i as u128);
                y += &term;
            }
            assert_eq!(x, y);
        }
    }
}
