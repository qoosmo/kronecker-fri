//! Commit to a multilinear polynomial given by its table, open it at a point, and verify.
//!
//! Run: `cargo run --release --example quickstart`
use kronecker_fri::field::{Fp, Fp2};
use kronecker_fri::pcs::{Params, commit_table, open, verify};

fn main() {
    // n = 16 variables, rate 1/4, arity 8, Merkle caps of 128 nodes, l = 8 folding rounds,
    // 148 queries (100-bit query term), salted trees
    let p = Params::recommended(16, 148, 32);
    let table: Vec<Fp> = (0..1u64 << 16).map(Fp::new).collect(); // f on {0,1}^16
    let z: Vec<Fp2> = (0..16u64)
        .map(|i| Fp2(Fp::new(3 + i), Fp::new(7 * i)))
        .collect();

    // The seeds derive the Merkle salts: use fresh, secret randomness in practice.
    let commit_seed = [0x11u8; 32];
    let open_seed = [0x22u8; 32];

    let (root, pd) = commit_table(&p, &table, &commit_seed);
    let (v, proof) = open(&p, &pd, &z, &open_seed); // v = f(z)
    assert!(verify(&p, &root, &z, v, &proof).is_ok());
    println!("f(z) = {:?}", v);
    println!("proof size: {:.1} KiB", proof.size_bytes() as f64 / 1024.0);
    println!("verified: ok");
}
