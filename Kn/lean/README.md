# Lean verification of odd complete graph tensors

This project accompanies [The Exact Asymptotic Rank Exponent of Odd Complete Graph Tensors](../Kn-asymptotic-rank.pdf). Target PDF SHA-256: `ed549b3b5e8289131f0b12a7e63be72b57d96d546f64220f6767487331d9c1dd`.

| Manuscript claim | Lean entry point |
| --- | --- |
| Exact complete-graph coefficients and grouped rectangular model | `completeGraph_eq_wires_dim`, `grouped_clique_eq_rectangle` |
| Balanced three-block partition and odd-order exponent | `grouped_balanced_clique`, `odd_complete_exact_exponent` |
| Ordinary finite rank lower bound for (K_5) | `k5_ordinary_rank_lower` |
| Affine Zariski-closure power bound and complex border rank | `rank_power_le_of_zariski`, `k5_border_rank_lower` |
| Euclidean endpoint pricing obstruction and sharp example | `k5_directed_pricing_upper`, `k5_price_isGreatest` |

The graph tensor is the coefficient tensor of the pinned complete-graph model over a field. The exponent for odd order (2m+1) uses base 2 with binary edge dimensions. The (K_5) ordinary lower bound holds for arbitrary integral (q ge 2). Border rank is tested against the affine Zariski closure of the set of ordinary-rank-at-most-(r) tensors over (mathbb C), not merely against an explicit one-parameter approximation. The polynomial-size overhead proof uses bounded monomial exponents.

The Euclidean statement concerns the specific single-site transport estimate in Proposition 4. The projector inequality uses endpoint min–max intervals and Gaussian mean width normalized by the first absolute moment of a standard real Gaussian. It does not assert an obstruction to other geometric certificates.

## Reproduce

With Git, Python 3, and elan installed, run `python3 replay.py` from this directory. This script uses Lean 4.34.1, the dependency manifest and the included fixed-point compatibility patch. It checks the audited declarations against Lean's three standard axioms, rebuilding from pinned source except for the Mathlib cache. Initial setup needs network access, disk space and time.

OpenAI/math pin: `3344da59991ed94f9ba711217b29c1d760badfa6`. Lemmata pin: `a20ff2d299b36e7357170ddd584eb4e462e95b06`.
