use std::ops::{AddAssign, Mul, MulAssign, SubAssign};

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use smallvec::smallvec;
use vectoreyes::U64x2;
use crate::{ring::{FiniteRing, IsSubRingOf}, serialization::CanonicalSerialize};

use super::{convolve::Convolve, polynomial::Polynomial, F128b, F64b, FiniteField, IsSubFieldOf, F2};


#[derive(Debug, Clone, Copy, Hash, Eq)]
/// Binary field element of size 256 bits.
pub struct F256b {
    /// High part of the field element, represented as a 128-bit integer.
    pub high: u128,
    /// Low part of the field element, represented as a 128-bit integer.
    pub low: u128,
}

impl ConstantTimeEq for F256b {
    fn ct_eq(&self, other: &Self) -> Choice {
        let high_eq = self.high.ct_eq(&other.high);
        let low_eq = self.low.ct_eq(&other.low);
        high_eq & low_eq
    }
}

impl ConditionallySelectable for F256b {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            high: u128::conditional_select(&a.high, &b.high, choice),
            low: u128::conditional_select(&a.low, &b.low, choice),
        }
    }
}

impl<'a> AddAssign<&'a F256b> for F256b {
    fn add_assign(&mut self, other: &'a F256b) {
        self.high ^= other.high;
        self.low ^= other.low;
    }
}

impl<'a> SubAssign<&'a F256b> for F256b {
    fn sub_assign(&mut self, other: &'a F256b) {
        // In GF(2^256), subtraction is the same as addition
        *self += other;
    }
}

fn reduce(c0: u128, c1: u128, c2: u128, c3: u128) -> F256b{
    let (mut r1, mut r2, mut r3) = (0u128 ,0u128, 0u128);
    
    //reduce c1
    r3 ^= c1;
    r3 ^= c1 << 2;
    r3 ^= c1 << 5;
    r3 ^= c1 << 10;

    r2 ^= c1 >> (128-2);
    r2 ^= c1 >> (128-5);
    r2 ^= c1 >> (128-10);

    // reduce c0 once
    r2 ^= c0;
    r2 ^= c0 << 2;
    r2 ^= c0 << 5;
    r2 ^= c0 << 10;

    r1 ^= c0 >> (128-2);
    r1 ^= c0 >> (128-5);
    r1 ^= c0 >> (128-10);
    // twice
    r3 ^= r1;
    r3 ^= r1 << 2;
    r3 ^= r1 << 5;
    r3 ^= r1 << 10;

    r3 ^= c3;
    r2 ^= c2;
    F256b {
        high: r2, low: r3
    }
}

/// A mask selecting groups of `shift` set bits alternating with `shift`
/// clear bits, repeated to fill 128 bits (e.g. shift=4 gives 0x0F0F...0F).
/// Used to build the "spread bits apart" masks below without hand-transcribing
/// 32-hex-digit literals.
const fn spread_mask(shift: u32) -> u128 {
    let unit_ones: u128 = (1u128 << shift) - 1;
    let mut mask = unit_ones;
    let mut width = 2 * shift;
    while width < 128 {
        mask |= mask << width;
        width *= 2;
    }
    mask
}

const SPREAD_MASK_32: u128 = spread_mask(32);
const SPREAD_MASK_16: u128 = spread_mask(16);
const SPREAD_MASK_8: u128 = spread_mask(8);
const SPREAD_MASK_4: u128 = spread_mask(4);
const SPREAD_MASK_2: u128 = spread_mask(2);
const SPREAD_MASK_1: u128 = spread_mask(1);

/// Move bit `i` of `x` (for i in 0..64) to bit `2*i` of the result, with
/// every odd-indexed bit of the result zero. Standard SWAR "bit spread" /
/// Morton-code technique: at each step, bits are shifted right by half the
/// remaining gap and OR'd back in, then masked to keep only the bits now in
/// their final half; six halvings (64 -> 32 -> 16 -> 8 -> 4 -> 2 -> 1) place
/// every bit in its own 2-bit slot.
const fn spread64_to_128(x: u64) -> u128 {
    let mut v = x as u128;
    v = (v | (v << 32)) & SPREAD_MASK_32;
    v = (v | (v << 16)) & SPREAD_MASK_16;
    v = (v | (v << 8)) & SPREAD_MASK_8;
    v = (v | (v << 4)) & SPREAD_MASK_4;
    v = (v | (v << 2)) & SPREAD_MASK_2;
    v = (v | (v << 1)) & SPREAD_MASK_1;
    v
}

impl F256b {
    /// Shifts the field element left by one bit, reducing it modulo the irreducible polynomial.
    /// This is equavialent as multiplying by x in the field.
    pub fn shift_left_once(&mut self){
        let c2 = self.high << 1 | self.low >> 127;
        let c3 = self.low << 1;

        self.high = c2;
        self.low = c3;
    }

    /// Squares the field element. In characteristic 2, (sum a_i x^i)^2 =
    /// sum a_i x^(2i): squaring a polynomial just moves each coefficient to
    /// double its position, with every odd-degree coefficient of the result
    /// zero. So the (unreduced) square is obtained by spreading the bits of
    /// `low` and `high` apart rather than by a full carryless multiplication,
    /// then reducing with the same `reduce()` used for general multiplication.
    pub fn square(&self) -> F256b {
        let c3 = spread64_to_128(self.low as u64);
        let c2 = spread64_to_128((self.low >> 64) as u64);
        let c1 = spread64_to_128(self.high as u64);
        let c0 = spread64_to_128((self.high >> 64) as u64);
        reduce(c0, c1, c2, c3)
    }

    /// Multiply with a power
    pub fn pow_mul(&mut self, pow: usize) -> F256b{
        let mut extended = [0u128; 4];
        if pow < 128 {
            extended[0] = self.low << pow;
            extended[1] = self.high << pow | self.low >> (128-pow);
            extended[2] = self.high >> (128-pow);
        } else if pow == 128{
            extended[1] = self.low;
            extended[2] = self.high;
        } else {
            let shift = pow-128;
            extended[1] = self.low << (shift);
            extended[2] = self.high << (shift) | self.low >> (128-shift);
            extended[3] = self.high >> (128-shift);
        }


        reduce(extended[3], extended[2], extended[1], extended[0])
    }
}

impl<'a> MulAssign<&'a F256b> for F256b {
    fn mul_assign(&mut self, rhs: &'a F256b) {
        let a_low: U64x2 = bytemuck::cast(self.low);
        let a_high: U64x2 = bytemuck::cast(self.high);
        let b_low: U64x2 = bytemuck::cast(rhs.low);
        let b_high: U64x2 = bytemuck::cast(rhs.high);

        // Using U64x2 for efficient multiplication
        let g3: [u64; 2] = a_low.carryless_mul::<false, false>(b_low).into();
        let d3: [u64; 2] = a_low.carryless_mul::<true, false>(b_low).into();
        let e3: [u64; 2] = a_low.carryless_mul::<false, false>(b_high).into();
        let f3: [u64; 2] = a_low.carryless_mul::<true, false>(b_high).into();
        
        let g2: [u64; 2] = a_low.carryless_mul::<false, true>(b_low).into();
        let d2: [u64; 2] = a_low.carryless_mul::<true, true>(b_low).into();
        let e2: [u64; 2] = a_low.carryless_mul::<false, true>(b_high).into();
        let f2: [u64; 2] = a_low.carryless_mul::<true, true>(b_high).into();

        let g1: [u64; 2] = a_high.carryless_mul::<false, false>(b_low).into();
        let d1: [u64; 2] = a_high.carryless_mul::<true, false>(b_low).into();
        let e1: [u64; 2] = a_high.carryless_mul::<false, false>(b_high).into();
        let f1: [u64; 2] = a_high.carryless_mul::<true, false>(b_high).into();

        let g0: [u64; 2] = a_high.carryless_mul::<false, true>(b_low).into();
        let d0: [u64; 2] = a_high.carryless_mul::<true, true>(b_low).into();
        let e0: [u64; 2] = a_high.carryless_mul::<false, true>(b_high).into();
        let f0: [u64; 2] = a_high.carryless_mul::<true, true>(b_high).into();

        // Combine the results
        let c3 = g3[0] as u128 ^ ((g3[1] ^d3[0]^g2[0])as u128) << 64;
        let c2 = (e3[0] ^ d3[1] ^ g2[1] ^ d2[0] ^ g1[0]) as u128 ^ ((e3[1] ^ f3[0] ^ d2[1] ^ e2[0] ^ g1[1] ^ g0[0] ^ d1[0]) as u128) << 64;
        let c1 = (f3[1] ^ e2[1] ^ f2[0] ^ d1[1] ^ e1[0] ^ g0[1] ^ d0[0]) as u128 ^ ((f2[1] ^ e1[1] ^ f1[0] ^ d0[1] ^ e0[0])as u128) << 64;
        let c0 = (f1[1] ^ e0[1] ^ f0[0])as u128 ^ ((f0[1])as u128) << 64;

        *self = reduce(c0, c1, c2, c3);

    }
}

impl FiniteRing for F256b{
    fn from_uniform_bytes(x: &[u8; 16]) -> Self {
        let low = u128::from_le_bytes(x[0..16].try_into().unwrap());
        F256b{high: low, low}
    }

    fn random<R: rand::Rng + ?Sized>(rng: &mut R) -> Self {
        let mut bytes = [0; 32];
        rng.fill_bytes(&mut bytes);
        let high = u128::from_le_bytes(bytes[0..16].try_into().unwrap());
        let low = u128::from_le_bytes(bytes[16..32].try_into().unwrap());
        F256b { high, low }
    }

    const ZERO: Self = Self {
        high: 0,
        low: 0,
    };

    const ONE: Self = Self {
        high: 0,
        low: 1,
    };
}

impl Convolve for F256b {}

impl CanonicalSerialize for F256b{
    type Serializer = crate::serialization::ByteElementSerializer<Self>;
    type Deserializer = crate::serialization::ByteElementDeserializer<Self>;
    type ByteReprLen = generic_array::typenum::U32;
    type FromBytesError = crate::serialization::BytesDeserializationCannotFail;

    fn from_bytes(
        bytes: &generic_array::GenericArray<u8, Self::ByteReprLen>,
    ) -> Result<Self, Self::FromBytesError> {
        let high = u128::from_le_bytes(bytes[0..16].try_into().unwrap());
        let low = u128::from_le_bytes(bytes[16..32].try_into().unwrap());
        Ok(F256b { high, low })
    }

    fn to_bytes(&self) -> generic_array::GenericArray<u8, Self::ByteReprLen> {
        let mut bytes = generic_array::GenericArray::<u8, Self::ByteReprLen>::default();
        bytes[0..16].copy_from_slice(&self.high.to_le_bytes());
        bytes[16..32].copy_from_slice(&self.low.to_le_bytes());
        bytes
    }
}

impl FiniteField for F256b{
    type PrimeField = F2;

    fn polynomial_modulus() -> Polynomial<Self::PrimeField>  {
        let mut coefficients = smallvec![F2::ZERO; 256];
        coefficients[256-1] = F2::ONE; // x^256
        coefficients[10-1] = F2::ONE; // x^10
        coefficients[5-1] = F2::ONE; // x^5
        coefficients[2-1] = F2::ONE; // x^2
        Polynomial{
            constant: F2::ONE,
            coefficients,
        }
    }

    const GENERATOR: Self = F256b{ high: 0, low: 2 };

    type NumberOfBitsInBitDecomposition = generic_array::typenum::U256;

    fn bit_decomposition(&self) -> generic_array::GenericArray<bool, Self::NumberOfBitsInBitDecomposition> {
        let low: generic_array::GenericArray<bool, generic_array::typenum::U128> = super::standard_bit_decomposition(self.low);
        let high: generic_array::GenericArray<bool, generic_array::typenum::U128> = super::standard_bit_decomposition(self.high);
        let mut out = generic_array::GenericArray::default();
        for i in 0..128 {
            out[i] = low[i];
            out[128 + i] = high[i];
        }
        out
    }

    fn inverse(&self) -> Self {
        // a^(-1) = a^(2^256 - 2) = (a^(2^255 - 1))^2 by Fermat's little
        // theorem. Reaching the exponent 2^255 - 1 by 254 sequential
        // multiplications (one per squaring) works but is far more
        // multiplication-heavy than necessary. Instead use the standard
        // addition chain for "repunit" exponents: maintaining x_k = a^(2^k-1),
        //   double:   x_{2k}   = x_k^(2^k) * x_k      (k squarings, 1 mult)
        //   add one:  x_{k+1}  = x_k^2 * a             (1 squaring, 1 mult)
        // reaches k = 255 = 0b1111_1111 via 8 doublings and 7 add-ones (an
        // addition chain in the exponent that mirrors 255's all-ones binary
        // form), then one final squaring gives a^(2^256-2): 255 squarings
        // (unavoidable -- the exponent's bit length doesn't shrink) but only
        // 14 multiplications, versus 254 in the direct approach. And since
        // every squaring here is F256b::square() -- bit-spread + reduce,
        // not a full carryless multiplication -- those 255 squarings are
        // themselves far cheaper than 255 multiplications would be.
        let a = *self;

        fn pow2k(x: F256b, k: u32) -> F256b {
            let mut y = x;
            for _ in 0..k {
                y = y.square();
            }
            y
        }
        // x_k -> x_{2k}
        let double = |x_k: F256b, k: u32| pow2k(x_k, k) * x_k;
        // x_k -> x_{k+1}
        let add_one = |x_k: F256b| x_k.square() * a;

        let x1 = a;
        let x2 = double(x1, 1);
        let x3 = add_one(x2);
        let x6 = double(x3, 3);
        let x7 = add_one(x6);
        let x14 = double(x7, 7);
        let x15 = add_one(x14);
        let x30 = double(x15, 15);
        let x31 = add_one(x30);
        let x62 = double(x31, 31);
        let x63 = add_one(x62);
        let x126 = double(x63, 63);
        let x127 = add_one(x126);
        let x254 = double(x127, 127);
        let x255 = add_one(x254);
        x255.square()
    }
}

impl Mul<F256b> for F2{
    type Output = F256b;

    fn mul(self, rhs: F256b) -> Self::Output {
        F256b{high: rhs.high*(self.0 as u128), low: rhs.low*(self.0 as u128)}
    }
}

impl From<F2> for F256b{
    fn from(value: F2) -> Self {
        F256b::conditional_select(&F256b::ZERO, &F256b::ONE, value.ct_eq(&F2::ONE))
    }
}

impl From<F128b> for F256b {
    fn from(value: F128b) -> Self {
        F256b {
            high: 0,
            low: value.0,
        }
    }
}

impl From<F64b> for F256b{
    fn from(value: F64b) -> Self {
        F256b {
            high: 0,
            low: value.0 as u128,
        }
    }
}

impl IsSubRingOf<F256b> for F2 {}
impl IsSubFieldOf<F256b> for F2 {
    type DegreeModulo = generic_array::typenum::U256;

    fn decompose_superfield(fe: &F256b) -> generic_array::GenericArray<Self, Self::DegreeModulo> {
        let mut components = generic_array::GenericArray::<Self, Self::DegreeModulo>::default();
        for i in 0..128 {
            components[i] = if (fe.low & (1 << i)) != 0 {
                F2::ONE
            } else {
                F2::ZERO
            };
        }
        for i in 0..128 {
            components[128 + i] = if (fe.high & (1 << i)) != 0 {
                F2::ONE
            } else {
                F2::ZERO
            };
        }
        components
    }

    fn form_superfield(components: &generic_array::GenericArray<Self, Self::DegreeModulo>) -> F256b {
        let mut high = 0u128;
        let mut low = 0u128;
        for i in 0..128 {
            if components[i] == F2::ONE {
                low |= 1 << i;
            }
            if components[128 + i] == F2::ONE {
                high |= 1 << i;
            }
        }
        F256b { high, low }
    }
}
field_ops!(F256b);

#[cfg(test)]
mod tests {
    use crate::ring::FiniteRing;

    use super::F256b;

    test_field!(test_field, crate::field::F128b);

    #[test]
    fn test_pow_mul(){
        let mut a = F256b{high: 1, low: 1};
        let b = F256b{high:0, low:2};
        assert_eq!(a*b, a.pow_mul(1));
    }

    #[test]
    fn test_pow_mul2(){
        let mut a = F256b{high: 1, low: 1};
        let b = F256b{high:0, low:4};
        assert_eq!(a*b, a.pow_mul(2));
    }

    #[test]
    fn test_pow_mul3(){
        let mut a = F256b{high: 1, low: 1};
        let b = F256b{high:1, low:0};
        assert_eq!(a*b, a.pow_mul(128));
    }
    #[test]
    fn test_pow_mul4(){
        let mut a = F256b{high: 1, low: 1};
        let b = F256b{high:2, low:0};
        assert_eq!(a*b, a.pow_mul(129));
    }
}