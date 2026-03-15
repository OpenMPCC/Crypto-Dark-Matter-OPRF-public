use std::time::Instant;

use rand::SeedableRng;
use scuttlebutt::{field::F64t, ring::FiniteRing, AesRng};

fn main(){
    let mut rng = AesRng::from_entropy();
    let mut acc = F64t::ZERO;
    let count = 10000000;
    let mut inputs = Vec::with_capacity(count);
    for _ in 0..count{
        let a = F64t::random(&mut rng);
        let b = F64t::random(&mut rng);
        inputs.push((a, b));
    }
    
    let time = Instant::now();
    for i in 0..count{
        let (a,b) = inputs[i];
        let c = a * b;
        acc += c;
    }
    let dur = time.elapsed();
    println!("Runtime: {:?}", dur);
    println!("Time per mul: {:?}ns", dur.as_nanos() / count as u128);
    println!("acc: {:?}", acc);
}
