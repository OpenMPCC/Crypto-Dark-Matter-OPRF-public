// End-to-end oracle for the real protocol implementation, driven from stdin
// (not a Python reconstruction of it). Originally built for the
// integral-cryptanalysis key-recovery attack, so an external driver can
// submit its own chosen queries, but it is a plain honest run of the
// protocol and has no attack-specific logic of its own.
//
// Protocol (`CDMOPRFReceiver::oprf_client` / `CDMOPRFSender::oprf_server`) is
// run honestly end to end, over an in-process channel, exactly as in
// `examples/bench_oprf.rs`. The only difference from that benchmark is that
// the batch of inputs is read from stdin instead of drawn at random, so an
// external driver (the Python attack code) can submit its own chosen queries.
//
// Wire protocol
//   stdin  : line 1 = N (number of queries); lines 2..N+1 = 32-hex-char
//            (128-bit, big-endian) input values.
//   stdout : "G "   followed by 191*128 values in {0,1,2}, row-major (row i,
//                    col j), i.e. the same public generator matrix used by
//                    `encode_input`.
//            "B "   followed by 82*256 values in {0,1,2}, row-major.
//            "KEY " followed by two 32-hex-char words: high, low of the
//                    honest server's F256b key (printed ONLY so the driver can
//                    check its recovered key -- the attack itself never reads
//                    this line as an input).
//            "OUT "  followed by N*82 values in {0,1,2}: for query j (0-indexed)
//                    and output coordinate i (0-indexed), entry j*82+i is
//                    F_k(x_j)_i, i.e. exactly (B .3 (M_k .2 enc(x_j)))_i.
//
// All of G, B and the per-query outputs come directly from the shipped
// `oprf` crate; nothing here re-implements field arithmetic or the encoding.
use std::io::{self, BufRead, Write};

use oprf::{
    input_encoding::generate_linear_code,
    matrix_util::generate_fixed_b,
    preprocessing::{init_cdm_oprf_receiver, init_cdm_oprf_sender},
    OPRF::OPRFSetting,
};
use rand::SeedableRng;
use scuttlebutt::{field::F128b, track_unix_channel_pair, AesRng};

fn read_inputs() -> Vec<u128> {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines
        .next()
        .expect("expected a line with the query count")
        .unwrap()
        .trim()
        .parse()
        .expect("first line must be an integer N");
    let mut xs = Vec::with_capacity(n);
    for _ in 0..n {
        let line = lines
            .next()
            .expect("stdin ended before N input lines were read")
            .unwrap();
        let v = u128::from_str_radix(line.trim(), 16).expect("expected 32 hex chars");
        xs.push(v);
    }
    xs
}

fn main() {
    let xs = read_inputs();
    let batch_size = xs.len();
    let stdout = io::stdout();
    let mut out = stdout.lock();

    // --- public generator G, exactly as encode_input() uses it -------------
    let (g, _gadget, _h) = generate_linear_code();
    write!(out, "G").unwrap();
    for row in g.iter() {
        for v in row.iter() {
            write!(out, " {}", u8::from(*v)).unwrap();
        }
    }
    writeln!(out).unwrap();

    // --- public B, same all-zero-seed convention as examples/bench_oprf.rs -
    let (b, bc) = generate_fixed_b();
    write!(out, "B").unwrap();
    for row in b.iter() {
        for v in row.iter() {
            write!(out, " {}", u8::from(*v)).unwrap();
        }
    }
    writeln!(out).unwrap();
    let bs = bc.clone();

    // --- run the real protocol, honestly, over an in-process channel -------
    let (client, server) = track_unix_channel_pair();
    let handle = std::thread::spawn(move || {
        let mut rng = AesRng::from_seed(Default::default());
        let mut channel = client;
        let inputs: Vec<F128b> = xs.iter().map(|&v| F128b::from(v)).collect();
        let mut receiver =
            init_cdm_oprf_receiver(&mut channel, &mut rng, inputs.len(), b, bc, OPRFSetting::RevealOutput);
        receiver.oprf_client(inputs, &mut channel, &mut rng)
    });

    let mut rng = AesRng::from_seed(Default::default());
    let mut channel = server;
    let mut sender = init_cdm_oprf_sender(&mut channel, &mut rng, batch_size, b, bs, OPRFSetting::RevealOutput);
    sender.oprf_server(batch_size, &mut channel, &mut rng);

    let fk_x = handle.join().expect("client thread panicked");
    assert_eq!(fk_x.len(), batch_size * 82);

    writeln!(out, "KEY {:032x} {:032x}", sender.key.high, sender.key.low).unwrap();

    write!(out, "OUT").unwrap();
    for v in fk_x.iter() {
        write!(out, " {}", u8::from(*v)).unwrap();
    }
    writeln!(out).unwrap();
}
