
use scuttlebutt::{field::F3, ring::FiniteRing};

// Setup timing for different window sizes
// 4  -> 5ms
// 8  -> 78ms
// 16 -> 16s

// Run timing for different windows sizes
// NO -> 760us
// 4  -> 578us
// 8  -> 287us
// 16 -> 155us

// Memory usage for different windows sizes
// 4  -> 168 KB
// 8  -> 1.3 MB
// 16 -> 172 MB

// Batch size to amortize table generation cost
// 4  -> 27
// 8  -> 165
// 16 -> 27k

const WINDOWS_SIZE: usize = 16;
type PackingSize = u16;

pub fn generate_precompute_tables(b: [[F3;256];82]) -> Vec<F3>{
    let mut table = Vec::new();
    // Compute all binary input to this row
    //let mut out = Vec::new();
    for k in 0..256/WINDOWS_SIZE{
        for i in 0..(1 as usize)<<WINDOWS_SIZE{
            for row in 0..82{
                let input = i as PackingSize;
                let mut output = F3::ZERO;
                for j in 0..WINDOWS_SIZE{
                    let bit: PackingSize = (input >> j) & 1;
                    if bit == 1{
                        output += b[row][k*WINDOWS_SIZE + j];
                    }
                }
                table.push(output);
            }
        }
    }
    table

}

pub fn compute_row_using_table(table: &Vec<F3>, input: [F3; 256] ) -> Vec<F3>{
    let mut msb: [PackingSize; 256/WINDOWS_SIZE] = [0; 256/WINDOWS_SIZE];
    let mut lsb: [PackingSize; 256/WINDOWS_SIZE] = [0; 256/WINDOWS_SIZE];

    for i in 0..256/WINDOWS_SIZE{
        let mut value: PackingSize = 0;
        for j in 0..WINDOWS_SIZE{
            let u8_value: u8 = input[i*WINDOWS_SIZE + j].into();
            let bit: PackingSize = (u8_value & 1).into();
            value |= bit << j;
        }
        lsb[i] = value;
        let mut value: PackingSize = 0;
        for j in 0..WINDOWS_SIZE{
            let u8_value: u8 = input[i*WINDOWS_SIZE + j].into();
            let bit: PackingSize = ((u8_value >> 1) & 1).into();
            value |= bit << j;
        }
        msb[i] = value;
    }

    let mut values = [F3::ZERO; 82];
    for i in 0..256/WINDOWS_SIZE{
        for row in 0..82{
            let sub_value = table[i*(82 * 1<<WINDOWS_SIZE)+(lsb[i] as usize)*82 + row]
                              - table[i*(82 * 1<<WINDOWS_SIZE)+(msb[i] as usize)*82 + row];
            values[row] += sub_value;
        }
    }
    values.into()

}

pub fn apply_b(b: [[F3;256];82], input: [F3; 256]) -> [F3; 82]{
    let mut out = [F3::ZERO; 82];
    for row in 0..82{
        let mut value = F3::ZERO;
        for j in 0..256{
            value = value + b[row][j]*input[j];
        }
        out[row] = value;
    }
    out
}

#[cfg(test)]
mod test{
    use rand::SeedableRng;
    use scuttlebutt::{field::F3, ring::FiniteRing, AesRng};
    use super::*;

    #[test]
    pub fn test_precompute_row(){
        let mut b_rng = AesRng::from_entropy();
        let mut b: [[F3; 256];82] = [[F3::ZERO; 256]; 82];
        // Randomly assing values to B
        for i in 0..82 {
            for j in 0..256 {
                b[i][j] = F3::random(&mut b_rng);
            }
        }
        let mut input = [F3::ZERO; 256];
        for i in 0..256{
            input[i] = F3::random(&mut b_rng);
        }

        let table = generate_precompute_tables(b);
        let out = compute_row_using_table(&table, input);

        let real = apply_b(b, input);
        for i in 0..82{
            assert_eq!(out[i], real[i]);
        }
    }
}