# kronecker-fri (Rust)

Reference implementation of the paper [`../paper/kronecker-fri.pdf`](../paper/kronecker-fri.pdf). Single-threaded, no SIMD, one dependency (BLAKE3).

| Module | Contents | Paper |
|---|---|---|
| `field` | Goldilocks $\mathbb{F}_q$, $q = 2^{64}-2^{32}+1$; $\mathbb{F}_{q^2} = \mathbb{F}_q[u]/(u^2-7)$; $\mathbb{F}_{q^4} = \mathbb{F}_q[\iota]/(\iota^4-7)$ | §9.1 |
| `poly` | Möbius transform, NTT, $K_z(\xi)$, $K_z$ on the domain, $U_f K_z$, opening polynomials, kernel folds | §2, §4, §5, §6.3 |
| `merkle` | salted Merkle trees (fibre leaves), group openings, transcript, challenge maps $\phi$ and pos | §3.4, §8.1, §9.3 |
| `pcs` | `commit_coeffs`, `commit_table`, `open`, `verify`, `verify_detail`; test-only cheating provers | §6, §9 |

## Commands

```bash
cargo test --release                                  # 14 unit tests + 3 end-to-end tests
cargo run --release --example quickstart              # commit / open / verify
cargo run --release --example small_field_checks      # independent checks over F_257
cargo run --release --example pq_params               # exact evaluation of the post-quantum bound
cargo run --release --example bench -- scaling        # tables of paper §10 (also: breakdown, stop, fields, params)
cargo run --release --features parallel --example ip_bench  # multithreaded prover
```

## Conventions

- Bits, variables and rounds are numbered from 0 in the code and from 1 in the paper: bit $a_k$ is bit `k-1`, $z_k$ is `z[k-1]`, $r_j$ is `rs[j-1]`.
- Position $i$ of a word on $L_j$ is $\omega_j^i$; the fibre over position $k$ of $L_{j+1}$ is $\{k, k+M_{j+1}\}$; Merkle leaf $k$ holds that fibre.
- Seeds passed to `commit_*` and `open` derive all salts; they must be fresh and secret.

## Status

The implementation follows the structure of the compiler of Chiesa–Di–Hu–Zheng (salted leaves, one salt per round, challenges from all previous roots and salts) but has not been checked against it byte by byte, so the post-quantum corollary of the paper is not claimed for this code. The batched protocol of §11.2 is not implemented.
