use std::{io::Read, ops::{AddAssign, MulAssign, SubAssign}};

use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use crate::{ring::FiniteRing, serialization::{BiggerThanModulus, CanonicalSerialize, SequenceDeserializer, SequenceSerializer}};

use super::{convolve::Convolve, polynomial::Polynomial, FiniteField, PrimeFiniteField};


/// A field element in the prime-order finite field $\textsf{GF}(3).$
#[derive(Debug, Eq, Clone, Copy, Hash, bytemuck::Zeroable)]
pub struct F3{
    /// Most significant bit.
    pub msb: u8,
    /// Least significant bit.
    pub lsb: u8,
}

const MODULUS: u8 = 3;

impl From<F3> for u8 {
    #[inline(always)]
    fn from(x: F3) -> Self {
        x.msb*2 + x.lsb
    }
}

impl TryFrom<u8> for F3{
    type Error = BiggerThanModulus;

    #[inline(always)]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < MODULUS {
            let msb = (value >> 1) & 1;
            let lsb = value & 1;
            Ok(F3{msb, lsb})
        } else {
            Err(BiggerThanModulus)
        }
    }
}

impl ConstantTimeEq for F3 {
    #[inline(always)]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.msb.ct_eq(&other.msb) & self.lsb.ct_eq(&other.lsb)
    }
}

impl ConditionallySelectable for F3 {
    #[inline(always)]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let msb = u8::conditional_select(&a.msb, &b.msb, choice);
        let lsb = u8::conditional_select(&a.lsb, &b.lsb, choice);
        F3{msb, lsb}
    }
}

impl AddAssign<&F3> for F3 {
    #[inline(always)]
    fn add_assign(&mut self, &rhs: &Self) {
        let t = (self.lsb | rhs.msb) ^ (self.msb | rhs.lsb);
        let msb = (self.lsb | rhs.lsb) ^ t;
        let lsb = (self.msb | rhs.msb) ^ t;
        self.msb = msb;
        self.lsb = lsb;
    }
}

impl SubAssign<&F3> for F3 {
    #[inline(always)]
    fn sub_assign(&mut self, &rhs: &Self) {
        let a = u8::try_from(*self).unwrap();
        let b = u8::try_from(rhs).unwrap();
        let diff = (a + MODULUS - b) % MODULUS;
        let value = F3::try_from(diff).unwrap();
        self.msb = value.msb;
        self.lsb = value.lsb;
    }
}

const LOOKUP: [F3; 11] = [F3::ZERO,          F3::ZERO, F3::ZERO, 
                          F3::ZERO,          F3::ZERO, F3::ONE,
                          F3{msb: 1, lsb:0}, F3::ZERO, F3::ZERO,
                          F3{msb: 1, lsb:0}, F3::ONE];

impl MulAssign<&F3> for F3 {
    
    #[inline(always)]
    fn mul_assign(&mut self, &rhs: &Self) {
        let x = self.msb * 8 + self.lsb*4 + rhs.msb*2 + rhs.lsb;
        let value = LOOKUP[x as usize];
        self.msb = value.msb;
        self.lsb = value.lsb;
        
        /*
        (self.msb, self.lsb) = match self {
            F3{msb: 0, lsb: 0} => (0,0),
            F3{msb: 0, lsb: 1} => (rhs.msb, rhs.lsb),
            _ => (rhs.lsb, rhs.msb),
        };
        */

        /*
        let a = u8::try_from(*self).unwrap();
        let b = u8::try_from(rhs).unwrap();
        let prod = (a * b) % MODULUS;
        let value = F3::try_from(prod).unwrap();
        self.msb = value.msb;
        self.lsb = value.lsb;
        */
    }
}

impl FiniteRing for F3{
    fn from_uniform_bytes(x: &[u8; 16]) -> Self {
        let mut value = u128::from_le_bytes(*x);
        value = value % MODULUS as u128;
        F3::try_from(value as u8).unwrap()
    }

    fn random<R: rand::Rng + ?Sized>(rng: &mut R) -> Self {
        let value = rng.next_u32() % MODULUS as u32;
        F3::try_from(value as u8).unwrap()
    }

    fn random_nonzero<R: RngCore + ?Sized>(_rng: &mut R) -> Self {
        let value = _rng.next_u32();
        if (value & 1) == 0{
            F3{msb: 1, lsb: 0} // 2
        } else {
            F3{msb: 0, lsb: 1} // 1
        }
    }

    const ZERO: Self = F3{msb: 0, lsb: 0};

    const ONE: Self = F3{msb: 0, lsb: 1};
}

impl Convolve for F3 {}

impl CanonicalSerialize for F3{
    type Serializer = F3BitSerializer;
    type Deserializer = F3BitDeserializer;
    type ByteReprLen = generic_array::typenum::U1;
    type FromBytesError = BiggerThanModulus;

    fn from_bytes(
        bytes: &generic_array::GenericArray<u8, Self::ByteReprLen>,
    ) -> Result<Self, Self::FromBytesError> {
        let buf = <[u8; 1]>::from(*bytes);
        F3::try_from(u8::from_le_bytes(buf))
    }

    fn to_bytes(&self) -> generic_array::GenericArray<u8, Self::ByteReprLen> {
        u8::from(*self).to_le_bytes().into()
    }
}

pub struct F3BitSerializer{
    accumulator: u8,
    multiplier: u8
}

impl SequenceSerializer<F3> for F3BitSerializer {
    fn serialized_size(n: usize) -> usize {
        n/5 + if n % 5 == 0 {0} else {1}
        /*
        let mut num_bit = n * 2;
        num_bit/8 + if num_bit % 8 == 0 {0} else {1}
        */
    }

    fn new<W: std::io::Write>(_dst: &mut W) -> std::io::Result<Self> {
        Ok(F3BitSerializer{
            accumulator: 0,
            multiplier: 1
        })
    }

    fn write<W: std::io::Write>(&mut self, dst: &mut W, e: F3) -> std::io::Result<()> {
        let value = u8::try_from(e).unwrap();
        self.accumulator += value * self.multiplier;
        self.multiplier *= 3;
        if self.multiplier >= 243{
            dst.write_all(&[self.accumulator])?;
            self.accumulator = 0;
            self.multiplier = 1;
        }

        /*
        let value = u8::try_from(e).unwrap();
        self.word |= value << self.num_bits;
        self.num_bits += 2;
        if self.num_bits == 8 {
            dst.write_all(&[self.word])?;
            self.word = 0;
            self.num_bits = 0;
        }
        */
        Ok(())
    }

    fn finish<W: std::io::Write>(mut self, dst: &mut W) -> std::io::Result<()> {
        if self.multiplier > 1{
            dst.write_all(&[self.accumulator])?;
            self.accumulator = 0;
            self.multiplier = 1;
        }
        /*
        if self.num_bits > 0 {
            dst.write_all(&[self.word])?;
            self.word = 0;
            self.num_bits = 0;
        }
        */
        Ok(())
    }
}

pub struct F3BitDeserializer{
    accumulator: u8,
    counter: u8,
}

impl SequenceDeserializer<F3> for F3BitDeserializer{
    fn new<R: Read>(_: &mut R) -> std::io::Result<Self> {
        Ok(F3BitDeserializer{
            accumulator: 0,
            counter: 0,
        })
    }

    fn read<R: Read>(&mut self, src: &mut R) -> std::io::Result<F3> {
        if self.counter == 0{
            let mut buf = [0; 1];
            src.read_exact(&mut buf)?;
            self.accumulator = buf[0];
            self.counter = 5; // 3^5 = 243, so we can read 5 values at once
        }
        let value = self.accumulator % 3;
        self.accumulator /= 3;
        self.counter -= 1;
        let out = F3::try_from(value).unwrap();
        /*
        if self.num_bits == 0 {
            let mut buf = [0; 1];
            src.read_exact(&mut buf)?;
            self.word = buf[0];
            self.num_bits = 8;
        }
        let value = (self.word >> (8-self.num_bits)) & 0b11;
        self.num_bits -= 2;
        let out = F3::try_from(value).unwrap();
        */
        Ok(out)
    }
}

impl FiniteField for F3{
    type PrimeField = Self;

    fn polynomial_modulus() -> super::polynomial::Polynomial<Self::PrimeField> {
        Polynomial::x()
    }

    const GENERATOR: Self = F3{msb: 1, lsb: 0};

    type NumberOfBitsInBitDecomposition = generic_array::typenum::U2;

    fn bit_decomposition(&self) -> generic_array::GenericArray<bool, Self::NumberOfBitsInBitDecomposition> {
        let mut bits = generic_array::GenericArray::default();
        bits[1] = self.msb != 0;
        bits[0] = self.lsb != 0;
        bits
    }

    fn inverse(&self) -> Self {
        assert_ne!(self.lsb + self.msb, 0);
        *self
    }
}

impl TryFrom<u128> for F3{
    type Error = BiggerThanModulus;

    fn try_from(value: u128) -> Result<Self, Self::Error> {
        if value < MODULUS.into() {
            let value = value as u8;
            Ok(F3::try_from(value).unwrap())
        } else {
            Err(BiggerThanModulus)
        }
    }
}

impl TryFrom<u64> for F3{
    type Error = BiggerThanModulus;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        if value < MODULUS.into(){
            let value = value as u8;
            Ok(F3::try_from(value).unwrap())
        } else {
            Err(BiggerThanModulus)
        }
    }
}

impl PrimeFiniteField for F3{}

field_ops!(F3);


#[cfg(test)]
mod tests{
    use crate::serialization;

    use super::*;

    #[test]
    fn test_from_u8(){
        let a = F3::try_from(0u8).unwrap();
        assert_eq!(a, F3{msb: 0, lsb: 0});
        let b = F3::try_from(1u8).unwrap();
        assert_eq!(b, F3{msb: 0, lsb: 1});
        let c = F3::try_from(2u8).unwrap();
        assert_eq!(c, F3{msb: 1, lsb: 0});
    }

    #[test]
    fn test_add(){
        let a = F3{msb: 0, lsb: 1};
        let b = F3{msb: 0, lsb: 1};
        let mut c = a;
        c += &b;
        assert_eq!(c, F3{msb: 1, lsb: 0});
    }

    #[test]
    fn test_sub(){
        let a = F3{msb: 0, lsb: 1};
        let b = F3{msb: 1, lsb: 0};
        let mut c = a;
        c -= &b;
        assert_eq!(c, F3{msb: 1, lsb: 0});
    }

    #[test]
    fn test_mul(){
        let a = F3{msb: 1, lsb: 0};
        let b = F3{msb: 1, lsb: 0};
        let mut c = a;
        c *= &b;
        assert_eq!(c, F3{msb: 0, lsb: 1});
    }

    #[test]
    fn test_serialize_deserialize(){
        let a = F3{msb: 1, lsb: 0};
        let mut buf = Vec::new();
        let mut serializer = F3BitSerializer::new(&mut buf).unwrap();
        serializer.write(&mut buf, a).unwrap();
        serializer.finish(&mut buf).unwrap();

        let mut deserializer = F3BitDeserializer::new(&mut buf.as_slice()).unwrap();
        let b = deserializer.read(&mut buf.as_slice()).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_serialize_deserialize_multiple(){
        let a = F3{msb: 1, lsb: 0};
        let b = F3{msb: 0, lsb: 1};
        let mut buf = Vec::new();
        let mut serializer = F3BitSerializer::new(&mut buf).unwrap();
        serializer.write(&mut buf, a).unwrap();
        serializer.write(&mut buf, b).unwrap();
        serializer.write(&mut buf, b).unwrap();
        serializer.write(&mut buf, b).unwrap();
        serializer.write(&mut buf, b).unwrap();
        serializer.write(&mut buf, b).unwrap();
        serializer.finish(&mut buf).unwrap();

        let mut deserializer = F3BitDeserializer::new(&mut buf.as_slice()).unwrap();
        let c = deserializer.read(&mut buf.as_slice()).unwrap();
        let _d = deserializer.read(&mut buf.as_slice()).unwrap();
        let _d = deserializer.read(&mut buf.as_slice()).unwrap();
        let _d = deserializer.read(&mut buf.as_slice()).unwrap();
        let d = deserializer.read(&mut buf.as_slice()).unwrap();
        assert_eq!(a, c);
        assert_eq!(b, d);
    }

    #[test]
    fn test_conditional_choose(){
        let a = F3::ZERO;
        let b = F3::ONE;
        let c = F3::conditional_select(&a, &b, Choice::from(0));
        assert_eq!(c, a);
        let d = F3::conditional_select(&a, &b, Choice::from(1));
        assert_eq!(d, b);
    }

    #[test]
    fn test_serialize_size(){
        let size = <F3 as serialization::CanonicalSerialize>::Serializer::serialized_size(10);
        assert_eq!(size, 2);
        let size = <F3 as serialization::CanonicalSerialize>::Serializer::serialized_size(20);
        assert_eq!(size, 4);
        let size = <F3 as serialization::CanonicalSerialize>::Serializer::serialized_size(100);
        assert_eq!(size, 100/5);
    }

    test_field!(test_field, crate::field::F3);
}