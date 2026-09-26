# Kronecker-FRI

**A hash-based multilinear polynomial commitment from a coefficient-extraction identity — evaluation proofs without sumcheck.**

[![Rust](https://github.com/qoosmo/kronecker-fri/actions/workflows/rust.yml/badge.svg)](https://github.com/qoosmo/kronecker-fri/actions/workflows/rust.yml)
[![Paper](https://github.com/qoosmo/kronecker-fri/actions/workflows/paper.yml/badge.svg)](https://github.com/qoosmo/kronecker-fri/actions/workflows/paper.yml)
[![Lean](https://github.com/qoosmo/kronecker-fri/actions/workflows/lean.yml/badge.svg)](https://github.com/qoosmo/kronecker-fri/actions/workflows/lean.yml)
![Rust 2024](https://img.shields.io/badge/Rust-2024_edition-orange)
![License](https://img.shields.io/badge/code-MIT%20%7C%20Apache--2.0-blue)
![Paper](https://img.shields.io/badge/paper-CC%20BY%204.0-lightgrey)

| | What | Where |
|---|---|---|
| 📄 | A self-contained paper (63 pages): definitions, theorems and full proofs, experiments, comparison | [`paper/kronecker-fri.pdf`](paper/kronecker-fri.pdf) |
| ✅ | A Lean 4 formalisation of §4–§7 and §11: no `sorry`, one axiom (correlated agreement) | [`lean/`](lean/) |
| ⚙️ | A Rust reference implementation (Goldilocks, quadratic and quartic extensions, salted Merkle trees, folding arity $2^k$, Merkle caps) | [`rust/`](rust/) |
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
3. **Rounds 2 to ℓ+1.** FRI folding (kernel fold, equivalent to the classical fold up to reparametrisation), of any arity $2^k$: only every $k$-th folded word is committed.
4. **Round ℓ+2.** Final polynomial of $N/2^\ell$ coefficients, then $\kappa$ queries. Each query reads the commitment, $w_A$ and each committed folded word on one coset of $2^k$ points.

No sumcheck. The verifier is an FRI verifier plus $O(n)$ field operations per query.

## Results (proved in the paper, machine-checked in Lean)

| Result | Statement | Paper | Lean |
|---|---|---|---|
| Extraction identity | $f(z) = [X^{N-1}]\,U_f K_z$ | Thm 4.5 | `extraction` |
| Identity lemma | $X U K_z = A + vX^N + X^{N+1}H$ with $\deg A, H < N$ forces $v = [X^{N-1}] U K_z$ | Lem 4.10, 4.12 | `split_iff`, `identity_lemma` |
| Folding test | soundness for arbitrary words, witness sets, codeword chain | Thm 5.24 | `fpt_sound`, `chain_final` |
| Higher arity | committing to every $k$-th folded word only leaves every error term unchanged | Prop 5.28 | `acceptsC_iff`, `fptC_sound` |
| Batching lemma | correlated agreement for curves of degree 2 + identity lemma via the virtual word | Lem 7.4 | `batching` |
| Soundness | $\varepsilon_{\mathrm{KF}} < 3M/\lvert\mathbb{F}\rvert + (1-\delta)^\kappa$ for all $\delta \le (1-\rho)/2$ | Thm 7.8 | `soundness`, `soundnessC` |
| Knowledge | round-by-round knowledge soundness with a decoding extractor; evaluation binding | Thm 7.11, Cor 7.12 | `rbr_knowledge`, `knowledge`, `binding` |
| Post-quantum | straightline knowledge soundness in the QROM via Chiesa–Di–Hu–Zheng; $\varepsilon_{\mathrm{ext}}(2^{64}) < 2^{-31.8}$ | Thm 8.5, Cor 8.6 | — (paper only) |
| Batched openings | $m$ polynomials at one point for the cost of one opening; error $(m-1)M/\lvert\mathbb{F}\rvert + \varepsilon_{\mathrm{KF}}$ | Thm 11.2 | `batch_soundness`, `batch_knowledge` |

The only external result about codes is the correlated-agreement theorem of Ben-Sasson, Carmon, Ishai, Kopparty and Saraf, in the unique-decoding regime. Theorem numbers refer to [`paper/kronecker-fri.pdf`](paper/kronecker-fri.pdf).

**Lean 4.** Every result in the table except the post-quantum one is formalised in [`lean/`](lean/) (Lean 4.23.0, Mathlib v4.23.0). There is no `sorry`, and the single axiom is correlated agreement for curves. CI builds the project and checks the axioms of every main theorem. The post-quantum theorem rests on the Chiesa–Di–Hu–Zheng BCS theorem, which has no Lean formalisation. See [`lean/README.md`](lean/README.md) for the paper ↔ Lean table.

```bash
cd lean && lake exe cache get && lake build && lake env lean KroneckerFRI/Audit.lean
```

## Measurements

One core, $\rho = 1/4$, $\kappa = 148$ (100-bit query term), $\mathbb{F} = \mathbb{F}_{q^2}$ (Goldilocks), unsalted trees, all numbers from one session on one machine ([`bench/`](bench/), paper §10).

**Recommended configuration KF-8** (arity 8, Merkle caps of 128 nodes, $\ell = n-8$):

| $n$ | Commit | Open | Verify | Proof |
|---:|---:|---:|---:|---:|
| 16 | 41 ms | 92 ms | 2.4 ms | 184 KiB |
| 18 | 160 ms | 388 ms | 3.0 ms | 248 KiB |
| 20 | 0.73 s | 1.69 s | 3.4 ms | 299 KiB |
| 22 | 3.18 s | 9.28 s | 4.5 ms | 372 KiB |

**At identical engineering** ($n = 20$, arity 2, no caps, $\ell = n-4$, the configuration of the KBFold code):

| Scheme | Commit | Open | Verify | Proof |
|---|---:|---:|---:|---:|
| **Kronecker-FRI** | 0.73 s | 2.14 s | 6.3 ms | 1117 KiB |
| KBFold (sumcheck + kernel folding) | 0.77 s | 0.71 s | 5.9 ms | 1072 KiB |
| Coefficient-form baseline (BaseFold-style) | 0.74 s | 0.60 s | 5.7 ms | 1072 KiB |

Commit and verify cost the same across $n = 12,\dots,22$, with proofs within 5%; the opening additionally commits to $A$ (product $U_f K_z$, one NTT, one Merkle tree, the virtual word), measured term by term in the paper. Arity and caps are generic FRI optimisations that would also shrink the proofs of the sumcheck-based schemes; the table above isolates the protocols.

Recommended parameter sets (paper §11.3, KF-8, **salted**, $n = 20$):

| Target | Field | ρ | κ | Commit | Open | Verify | Proof |
|---|---|---|---:|---:|---:|---:|---:|
| 100 bits | $\mathbb{F}_{q^2}$ | 1/4 | 148 | 0.96 s | 2.18 s | 3.6 ms | 390 KiB |
| 100 bits | $\mathbb{F}_{q^2}$ | 1/8 | 121 | 1.83 s | 4.45 s | 3.2 ms | 346 KiB |
| 128 bits | $\mathbb{F}_{q^4}$ | 1/4 | 189 | 0.96 s | 3.96 s | 9.0 ms | 586 KiB |
| post-quantum (ε_ext < 2^-31.8 at 2^64 queries) | $\mathbb{F}_{q^4}$ | 1/4 | 248 | 0.92 s | 3.95 s | 9.5 ms | 755 KiB |

## Quick start

```bash
cd rust
cargo test --release                                   # unit and end-to-end tests
cargo run --release --example quickstart               # commit, open and verify one polynomial
cargo run --release --example small_field_checks       # independent checks over F_257
cargo run --release --example pq_params                # exact post-quantum bound (rational arithmetic)
cargo run --release --example bench -- scaling         # also: arity | breakdown | stop | params
```

```rust
use kronecker_fri::field::{Fp, Fp2};
use kronecker_fri::pcs::{commit_table, open, verify, Params};

// rate 1/4, arity 8, Merkle caps, l = n - 8, 148 queries, 32-byte salts
let p = Params::recommended(16, 148, 32);
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
lean/      Lean 4 formalisation (lake build)
rust/      reference implementation: field, poly, merkle, pcs; tests; examples; benchmarks
bench/     raw CSV output of every benchmark reported in the paper
docs/      project page, verification status, roadmap
```

## Scope and future work

- Proofs are in the unique-decoding regime; the post-quantum theorem covers one opening, for the compiler of Chiesa–Di–Hu–Zheng.
- Batched openings are proved for the interactive protocol; zero knowledge is future work.
- Next: a list-decoding analysis (fewer queries) and post-quantum batched openings.

See [`docs/VERIFICATION.md`](docs/VERIFICATION.md) for the status of every result and [`docs/ROADMAP.md`](docs/ROADMAP.md) for the roadmap.

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
