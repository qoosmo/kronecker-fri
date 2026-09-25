# Kronecker-FRI

**A hash-based multilinear polynomial commitment from a coefficient-extraction identity — evaluation proofs without sumcheck.**

[![Rust](https://github.com/qoosmo/kronecker-fri/actions/workflows/rust.yml/badge.svg)](https://github.com/qoosmo/kronecker-fri/actions/workflows/rust.yml)
[![Paper](https://github.com/qoosmo/kronecker-fri/actions/workflows/paper.yml/badge.svg)](https://github.com/qoosmo/kronecker-fri/actions/workflows/paper.yml)
![Rust 2024](https://img.shields.io/badge/Rust-2024_edition-orange)
![License](https://img.shields.io/badge/code-MIT%20%7C%20Apache--2.0-blue)
![Paper](https://img.shields.io/badge/paper-CC%20BY%204.0-lightgrey)

| | What | Where |
|---|---|---|
| 📄 | A self-contained paper (60 pages): definitions, theorems and full proofs, experiments, comparison | [`paper/kronecker-fri.pdf`](paper/kronecker-fri.pdf) |
| ⚙️ | A Rust reference implementation (Goldilocks, quadratic and quartic extensions, salted Merkle trees) | [`rust/`](rust/) |
| 📊 | Raw benchmark data behind every table of the paper | [`bench/`](bench/) |
| 🌐 | Project page | [qoosmo.github.io/kronecker-fri](https://qoosmo.github.io/kronecker-fri/) |

## The idea

Write a multilinear polynomial in coefficient form, $f = \sum_{a<N} \alpha_a x^a$ with $N = 2^n$ and $x^a = \prod_{k:a_k=1} x_k$. Its **Kronecker encoding** is the univariate polynomial

$$U_f(X) = \sum_a \alpha_a X^a = f\bigl(X, X^2, X^4, \dots, X^{2^{n-1}}\bigr),$$

and the **kernel polynomial** of a point $z \in \mathbb{F}^n$ is

$$K_z(X) = \prod_{k=1}^{n} \bigl(X^{2^{k-1}} + z_k\bigr).$$

The coefficient of $X^{N-1-a}$ in $K_z$ is $z^a$, so an evaluation is **one coefficient of a product**:

$$f(z) = [X^{N-1}]\; U_f(X)\,K_z(X).$$

To prove $f(z) = v$, the prover splits $X\,U_f K_z = A + v\,X^N + X^{N+1}H$ with $A, H$ of degree $< N$. It commits to $A$ only; the verifier computes $H$ at each query point from the identity (a *virtual word*), batches the three words with one random challenge, and runs plain FRI. A wrong $v$ makes the virtual word far from the code, so the proximity test alone enforces the evaluation claim.

## Protocol at a glance

1. **Commit.** $\mathrm{Enc}(f) = \mathrm{ev}_L(U_f)$, a Reed–Solomon codeword of rate $\rho = 2^{-R}$ ($R \ge 2$) on a smooth multiplicative domain $L$ of order $M = N/\rho$. One NTT.
2. **Round 1.** The prover sends $w_A = \mathrm{ev}_L(A)$; the verifier sends $\beta$. The batched word is $w + \beta w_A + \beta^2 h$, where $h(\xi) = (\xi\,w(\xi)K_z(\xi) - w_A(\xi) - v\xi^N)/\xi^{N+1}$.
3. **Rounds 2 to ℓ+1.** FRI folding (kernel fold, equivalent to the classical fold up to reparametrisation).
4. **Round ℓ+2.** Final polynomial of $N/2^\ell$ coefficients, then $\kappa$ queries. Each query reads the commitment and $w_A$ on one fibre $\{\pm\xi\}$ and one fibre per folded word.

No sumcheck. The verifier is an FRI verifier plus $O(n)$ field operations per query.

## Results (all proved in the paper)

| Result | Statement | Paper |
|---|---|---|
| Extraction identity | $f(z) = [X^{N-1}]\,U_f K_z$ | Thm 4.5 |
| Identity lemma | $X U K_z = A + vX^N + X^{N+1}H$ with $\deg A, H < N$ forces $v = [X^{N-1}] U K_z$ | Lem 4.10, 4.12 |
| Folding test | soundness for arbitrary words, witness sets, codeword chain | Thm 5.24 |
| Batching lemma | correlated agreement for curves of degree 2 + identity lemma via the virtual word | Lem 7.4 |
| Soundness | $\varepsilon_{\mathrm{KF}} < 3M/\lvert\mathbb{F}\rvert + (1-\delta)^\kappa$ for all $\delta \le (1-\rho)/2$ | Thm 7.8 |
| Knowledge | round-by-round knowledge soundness with a decoding extractor; evaluation binding | Thm 7.11, Cor 7.12 |
| Post-quantum | straightline knowledge soundness in the QROM via Chiesa–Di–Hu–Zheng; $\varepsilon_{\mathrm{ext}}(2^{64}) < 2^{-31.8}$ | Thm 8.5, Cor 8.6 |
| Batched openings | $m$ polynomials at one point for the cost of one opening; error $(m-1)M/\lvert\mathbb{F}\rvert + \varepsilon_{\mathrm{KF}}$ | Thm 11.2 |

The only external result about codes is the correlated-agreement theorem of Ben-Sasson, Carmon, Ishai, Kopparty and Saraf, in the unique-decoding regime. Theorem numbers refer to [`paper/kronecker-fri.pdf`](paper/kronecker-fri.pdf).

## Measurements

One core, $n = 20$, $\rho = 1/4$, $\kappa = 148$, $\mathbb{F} = \mathbb{F}_{q^2}$ (Goldilocks), same machine and session, unsalted trees ([`bench/`](bench/), paper §10):

| Scheme | Commit | Open | Verify | Proof |
|---|---:|---:|---:|---:|
| **Kronecker-FRI** | 0.98 s | 3.03 s | 6.6 ms | 1173 KiB |
| KBFold (sumcheck + kernel folding) | 1.01 s | 0.83 s | 6.5 ms | 1072 KiB |
| Coefficient-form baseline (BaseFold-style) | 0.98 s | 0.85 s | 6.5 ms | 1072 KiB |

Commit and verify cost the same; proofs are 8–17% larger; opening is 3.0–3.7× slower across $n = 12,\dots,22$. The extra opening cost is the commitment to $A$ (product $U_f K_z$, one NTT, one Merkle tree, the virtual word), measured term by term in the paper.

Recommended parameter sets (paper §11.3, salted, $n = 20$, $\ell = n-8$):

| Target | Field | ρ | κ | Open | Verify | Proof |
|---|---|---|---:|---:|---:|---:|
| 100 bits | $\mathbb{F}_{q^2}$ | 1/4 | 148 | 3.97 s | 6.8 ms | 1080 KiB |
| 100 bits | $\mathbb{F}_{q^2}$ | 1/8 | 121 | 7.07 s | 5.5 ms | 933 KiB |
| 128 bits | $\mathbb{F}_{q^4}$ | 1/4 | 189 | 6.74 s | 8.5 ms | 1453 KiB |
| post-quantum (ε_ext < 2^-31.8 at 2^64 queries) | $\mathbb{F}_{q^4}$ | 1/4 | 248 | 6.73 s | 11.4 ms | 1904 KiB |

## Quick start

```bash
cd rust
cargo test --release                                   # unit and end-to-end tests
cargo run --release --example quickstart               # commit, open and verify one polynomial
cargo run --release --example small_field_checks       # independent checks over F_257
cargo run --release --example pq_params                # exact post-quantum bound (rational arithmetic)
cargo run --release --example bench -- scaling         # also: breakdown | stop | fields | params
```

```rust
use kronecker_fri::field::{Fp, Fp2};
use kronecker_fri::pcs::{commit_table, open, verify, Params};

let p = Params { n: 16, log_inv_rate: 2, ell: 12, queries: 148, salt_len: 32 };
let table: Vec<Fp> = (0..1u64 << 16).map(Fp::new).collect(); // f on {0,1}^16
let z: Vec<Fp2> = (0..16u64).map(|i| Fp2(Fp::new(3 + i), Fp::new(7 * i))).collect();
// The seeds derive the Merkle salts: use fresh, secret randomness in practice.
let (root, pd) = commit_table(&p, &table, &commit_seed);
let (v, proof) = open(&p, &pd, &z, &open_seed); // v = f(z)
assert!(verify(&p, &root, &z, v, &proof));
```

The full program is [`rust/examples/quickstart.rs`](rust/examples/quickstart.rs).

## Repository layout

```
paper/     LaTeX sources and the compiled paper (make)
rust/      reference implementation: field, poly, merkle, pcs; tests; examples; benchmarks
bench/     raw CSV output of every benchmark reported in the paper
docs/      project page, verification status, roadmap
```

## Scope — what is and is not claimed

- The identity $f(z) = [X^{N-1}]U_fK_z$ is an inner-product-as-coefficient identity; the same tensor structure appears in the pairing-based scheme Mercury. The contribution is the transparent, hash-based scheme built on it and its analysis.
- Kronecker-FRI is **not** faster than sumcheck-based Reed–Solomon schemes: its opening is 3–3.7× slower at identical engineering.
- The analysis is in the **unique-decoding** regime; list-decoding schemes (DeepFold, WHIR) have much smaller proofs.
- The post-quantum statement covers **one opening**, uses the quoted theorem of Chiesa–Di–Hu–Zheng, and applies to their compiler; the code follows its structure (salted trees, round salts, the challenge maps) but has not been checked against it byte by byte.
- Batched openings are proved for the interactive protocol and are not yet implemented. Zero knowledge is out of scope.

See [`docs/VERIFICATION.md`](docs/VERIFICATION.md) for the status of every result and [`docs/ROADMAP.md`](docs/ROADMAP.md) for what comes next (Lean 4 formalisation, list decoding, batching in the post-quantum setting).

## Related work in this series

- **KBFold** — [github.com/qoosmo/kbfold](https://github.com/qoosmo/kbfold): the Boolean-kernel basis $\{K_b\}_{b \in \{0,1\}^n}$, in which FRI folding is table restriction, a BaseFold-type scheme built on it, and a Lean 4 formalisation. Kronecker-FRI uses the same product $K_z$ at an arbitrary point $z$, as a multiplier instead of a basis.

## Citation

```bibtex
@misc{Mkhida2026KroneckerFRI,
  author = {Abdelali Mkhida},
  title  = {Kronecker-FRI: A Hash-Based Multilinear Polynomial Commitment from a Coefficient-Extraction Identity},
  year   = {2026},
  note   = {Preprint},
  url    = {https://github.com/qoosmo/kronecker-fri}
}
```

## License

Code: dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
Paper (`paper/`): [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).

Abdelali Mkhida · Algorizk Labs · ali.mkhida@algorizk.xyz · ORCID [0009-0009-2101-9070](https://orcid.org/0009-0009-2101-9070)
