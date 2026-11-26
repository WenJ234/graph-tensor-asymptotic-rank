# The Exact Asymptotic Rank Exponents of Cycle Graph Tensors

Manuscript by Wen Jiang.

- [Original signed PDF](cycle-graph-tensors-Wen-Jiang.pdf)
- [Original source and certificate ZIP](cycle-proof-sources-and-certificates.zip)

For the binary cycle tensor over the complex numbers, the paper obtains exponent `n` for even `n` and `n − 1 + 1/[4(n − 2)]` for odd `n`. To replay the companion exact rational checks, extract the ZIP and run `python3 -B verify_all.py`. The supplied replay and independent checkers passed for the finite odd orders and the uniform tail. These checks use the cited mathematical results and are not an end-to-end Lean 4 verification.

## Scope: equal edge dimensions

Here the same dimension `q` is used on all edges; the binary exponent above is scaled by `log2(q)` for a common dimension `q`. For independently chosen edge dimensions and arbitrary unequal edge weights, see [The Asymptotic Rank of Weighted Cycle Tensors](../weighted-cycles/), a separate manuscript with its own Theorem 1.1.
