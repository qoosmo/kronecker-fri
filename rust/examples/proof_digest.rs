//! Digest of one proof of each protocol (Pi_KF, Pi_IP, Pi_Had, Pi_Batch, R1CS) on fixed inputs and
//! seeds, for n = 6, 11, 15. CI checks that the digests are the same with and without the
//! feature `parallel`:
//!   diff <(cargo run --release --example proof_digest) \
//!        <(cargo run --release --features parallel --example proof_digest)
use kronecker_fri::batch::Stmt;
use kronecker_fri::field::{Field, Fp, Fp2};
use kronecker_fri::insecure::{
    commit_coeffs, commit_table_form, index, open, prove_batch, prove_had, prove_ip, prove_r1cs,
};
use kronecker_fri::pcs::Params;
use kronecker_fri::r1cs::sample_instance;
fn d(s: String) -> String {
    blake3::hash(s.as_bytes()).to_hex()[..16].to_string()
}
fn main() {
    for n in [6usize, 11, 15] {
        let p = Params::recommended(n, 40, 32);
        let t: Vec<Fp> = (0..1u64 << n).map(|i| Fp::new(i * 7 + 3)).collect();
        let u: Vec<Fp> = (0..1u64 << n).map(|i| Fp::new(i * i + 1)).collect();
        let c: Vec<Fp> = t.iter().zip(&u).map(|(&x, &y)| x * y).collect();
        let z: Vec<Fp2> = (0..n)
            .map(|k| Fp2(Fp::new(k as u64 + 2), Fp::new(9)))
            .collect();
        let (r0, pd) = commit_coeffs(&p, &t, &[1u8; 32]);
        let (v, pr) = open::<Fp2>(&p, &pd, &z, &[2u8; 32]);
        println!(
            "n={n} pcs {} {}",
            d(format!("{:?}{:?}{:?}", r0, v, pr.p)),
            d(format!("{:?}", pr.level0))
        );
        let (_, pa) = commit_table_form(&p, &t, &[3u8; 32]);
        let (_, pb) = commit_table_form(&p, &u, &[4u8; 32]);
        let (_, pc) = commit_table_form(&p, &c, &[5u8; 32]);
        let (s, ip) = prove_ip::<Fp2>(&p, &pa, &pb, &[6u8; 32]);
        println!("n={n} ip {}", d(format!("{:?}{:?}", s, ip)));
        let hp = prove_had::<Fp2>(&p, &pa, &pb, &pc, &[7u8; 32]);
        println!("n={n} had {}", d(format!("{:?}", hp)));
        let st = vec![
            Stmt::Had { a: 0, b: 1, c: 2 },
            Stmt::Ip {
                a: 0,
                b: 1,
                s: Fp2::from(s),
            },
        ];
        let bp = prove_batch(&p, &[&pa, &pb, &pc], &st, &[8u8; 32]);
        println!("n={n} batch {}", d(format!("{:?}", bp)));
        let (r, x, wit) = sample_instance(n, 2, 2, 5);
        let idx = index(&p, &r, &[9u8; 32]);
        let rp = prove_r1cs::<Fp2>(&p, &r, &idx, &x, &wit, &[10u8; 32]);
        println!("n={n} r1cs {}", d(format!("{:?}", rp)));
        let _ = Fp2::ONE;
    }
}
