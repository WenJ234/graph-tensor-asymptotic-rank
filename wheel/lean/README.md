# Lean verification of the wheel graph tensor paper

This project accompanies [Exact asymptotic rank exponents of wheel graph tensors](../wheel-graph-tensors.pdf). Target PDF SHA-256: `fa8f6f76e7f569a5172893ff8e5638d85eb9bbf56217dbb4d46796bec3102a6f`.

`AuditWheel.lean` specifies the audited declarations. The wheel is the product of the binary rim and spoke wires with `r` rim vertices and one hub. The even and odd main theorems quantify over every field. The formalization uses the pinned OpenAI division-free rectangular exponent, verifies its equality with the grouped tensor's logarithmic asymptotic rank at integral widths, and proves the required copositive spectral constraints instead of adding them as axioms.

| Manuscript claim | Lean entry point |
| --- | --- |
| Equation (2): arithmetic and graph tensor rank normalization | `triangle_asymptotic_rank_exact` |
| Lemma 2 and optimality of the parity grouping | `graph_three_block_rank_lower`, `wheel_parity_grouping_isGreatest` |
| Theorem 1, both parities | `even_wheel_exact_exponent`, `odd_wheel_exact_exponent` |
| Common optimum of the strengthened CP and SDP bounds | `even_wheel_conic_optima`, `odd_wheel_conic_optima` |
| Cut flattening, maximum cut and excess (Proposition 3) | `exact_wheel_cut_flattening_rank`, `wheel_cut_exact`, `even_wheel_excess`, `odd_wheel_excess` |

## Reproduce

Install Git, Python 3, and Lean through elan; the toolchain is pinned in `lean-toolchain`. From this directory run `python3 replay.py`. The script fetches the exact source revisions, obtains the Mathlib cache, applies the included fixed-point compatibility patch, and rebuilds the proof dependencies. It checks the complete axiom set of each audited statement against `propext`, `Classical.choice`, and `Quot.sound`. The initial build needs time, disk space and network access. This is a source replay, not a download of the project's compiled proof artifacts.

Upstream pins: OpenAI/math `3344da59991ed94f9ba711217b29c1d760badfa6`, Lemmata `a20ff2d299b36e7357170ddd584eb4e462e95b06`, with other dependencies in `lake-manifest.json`.
