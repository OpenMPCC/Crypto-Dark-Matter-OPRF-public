use criterion::{black_box, criterion_group, criterion_main, Criterion};
use scuttlebutt::field::F64t;


fn f64t_mul(c: &mut Criterion) {
    c.bench_function("f64t::mul", |b| {
        let a = F64t{msb: 0, lsb: 1 << 63};
        let c = F64t{msb: 1 << 63, lsb: 0};
        b.iter(|| {
            let result = a * c;
            black_box(result);
        });
    });
}

criterion_group! {
    name = f64t;
    config = Criterion::default();
    targets = f64t_mul
}
criterion_main!(f64t);
