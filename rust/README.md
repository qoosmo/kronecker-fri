# kronecker-fri

Reference implementation of **Kronecker-FRI**, a hash-based (transparent, post-quantum) multilinear
polynomial commitment scheme built on the coefficient-extraction identity

    f(z) = [X^(N-1)] U_f(X) K_z(X),

where U_f is the Kronecker encoding of the multilinear polynomial f in n variables (N = 2^n) and
K_z is a product-form kernel. An evaluation proof is one opening word, one virtual word and one
FRI-style folding test: no sumcheck.

- Paper: [Kronecker-FRI (PDF)](https://github.com/qoosmo/kronecker-fri/blob/main/paper/kronecker-fri.pdf).
- Research note on sumcheck-free inner products, Hadamard checks, batches and R1CS:
  [note (PDF)](https://github.com/qoosmo/kronecker-fri/blob/main/notes/inner-product/note.pdf).
- The soundness of the protocols is machine-checked in Lean 4
  ([`lean/`](https://github.com/qoosmo/kronecker-fri/tree/main/lean)).

## Usage

```rust
use kronecker_fri::field::{Fp, Fp2};
use kronecker_fri::pcs::{Params, commit_table, open, verify};

// n = 16 variables; rate 1/4, arity 8, Merkle caps, 148 queries, 32-byte salts
let p = Params::recommended(16, 148, 32);
let table: Vec<Fp> = (0..1u64 << 16).map(Fp::new).collect(); // f on {0,1}^16
let z: Vec<Fp2> = (0..16u64).map(|i| Fp2(Fp::new(3 + i), Fp::new(7 * i))).collect();

// The salts of the Merkle trees are drawn from the operating system.
let (root, pd) = commit_table(&p, &table)?;
let (v, proof) = open(&p, &pd, &z)?; // v = f(z)
verify(&p, &root, &z, v, &proof)?;
```

## Modules

Stable API (the paper):

| Module | Contents |
|---|---|
| `field` | Goldilocks F_q, q = 2^64 - 2^32 + 1, and its extensions F_{q^2}, F_{q^4} |
| `poly` | Moebius transform, NTT, kernel polynomial, opening polynomials, kernel folds |
| `error` | `Error`, returned by every verifier and by `Params::validate` |
| `merkle` | salted BLAKE3 Merkle trees with fibre leaves and caps, Fiat-Shamir transcript |
| `pcs` | `Params`, `commit_table`, `commit_coeffs`, `open`, `verify` |

Research prototypes (the research note; their API may change between versions):

| Module | Contents |
|---|---|
| `ip`, `had` | sumcheck-free inner product and Hadamard check on committed tables |
| `batch`, `affine`, `ft` | many evaluations, inner products and Hadamard checks in one folding test, on affine forms of committed and public tables |
| `lincheck`, `r1cs` | sparse matrix-vector products and an R1CS argument without sumcheck |
| `spartan`, `sumcheck` | baselines: the core of Spartan and sumcheck-based inner product and Hadamard check, on the same commitment |

## Features

- `parallel`: multithreaded prover (rayon) for the commitment, the opening and the Merkle trees.
  The proofs are identical with and without it (checked in CI).

## Commands

```bash
cargo test --release                                        # unit and end-to-end tests
cargo run --release --example quickstart                    # commit / open / verify
cargo run --release --example small_field_checks            # independent checks over F_257
cargo run --release --example pq_params                     # exact post-quantum bound
cargo run --release --example bench -- scaling              # tables of the paper (also: arity, breakdown, stop, params)
cargo run --release --features parallel --example ip_bench  # multithreaded prover
```

## Conventions

- Bits, variables and rounds are numbered from 0 in the code and from 1 in the paper: bit a_k is
  bit `k-1`, z_k is `z[k-1]`, r_j is `rs[j-1]`.
- Position i of a word on L_j is omega_j^i; the fibre over position k of L_{j+1} is
  {k, k + M_{j+1}}; a Merkle leaf holds one fibre.
- The prover's randomness (the seeds of the Merkle salts) comes from the operating system's secure random number generator; the API takes no seeds. Seeded provers for test vectors exist only behind the feature `insecure-test-vectors`.

## Status

This is research code, not audited. It follows the structure of the compiler of
Chiesa-Di-Hu-Zheng (salted leaves, one salt per round, challenges from all previous roots and
salts) but has not been checked against it byte by byte, so the post-quantum corollary of the paper
is not claimed for this code. Zero knowledge is not provided.

## License

MIT or Apache-2.0, at your option.
