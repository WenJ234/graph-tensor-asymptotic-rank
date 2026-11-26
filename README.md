# Graph Tensor Asymptotic Rank | Wen Jiang

Research manuscripts on **exact asymptotic tensor rank** over the complex numbers, with papers, source files, and reproducibility materials.

## Which paper answers which cycle problem?

- **Arbitrary weighted cycles, including unequal edge weights and nonuniform edge dimensions:** [The Asymptotic Rank of Weighted Cycle Tensors](#the-asymptotic-rank-of-weighted-cycle-tensors).
- **Equal-weight cycles, including the binary cycle tensor for every cycle length:** [The Exact Asymptotic Rank Exponents of Cycle Graph Tensors](#the-exact-asymptotic-rank-exponents-of-cycle-graph-tensors).

These are separate manuscripts. In the equal-weight paper a single dimension is shared by every edge; in the weighted paper each edge dimension can be chosen independently.

## The Asymptotic Rank of Weighted Cycle Tensors

**Wen Jiang · Research manuscript**

[Paper (PDF)](weighted-cycles/weighted_cycle_tensors_Wen_Jiang.pdf) · [Main theorem (LaTeX source)](weighted-cycles/weighted_cycle_tensors_Wen_Jiang.tex#L36-L75) · [Formula, worked example, and reproduction guide](weighted-cycles/) · [Source and certificates (ZIP)](weighted-cycles/weighted_cycle_tensors_Wen_Jiang_source_and_certificates.zip)

**Question.** What is the exact asymptotic rank exponent of a cycle graph tensor when its edge dimensions are independent, including for odd cycles of length at least five with unequal weights?

**Result stated in Theorem 1.1.** For every cycle of length `n >= 3`, let `w_i = log2(q_i)` be the weight of edge `i` and let `S = sum_i w_i`. For even `n`, the exponent is `S`. For odd `n`, it is `max_i Omega(S - w_i - w_(i+1), w_i, w_(i+1))`, with cyclic indices, where `Omega` is the rectangular matrix multiplication exponent. The formula allows arbitrary positive integer edge dimensions and extends to arbitrary nonnegative real logarithmic weights. The [weighted-cycle guide](weighted-cycles/) gives the explicit piecewise function and an unequal-dimension five-cycle example.

## The Exact Asymptotic Rank Exponents of Cycle Graph Tensors

**Wen Jiang, 2026 · Research manuscript**

[Paper (PDF)](cn/cycle-graph-tensors-Wen-Jiang.pdf) · [Source and exact rational certificates (ZIP)](cn/cycle-proof-sources-and-certificates.zip) · [Reproduction guide](cn/)

**Question.** What is the exact exponent for all cycle lengths when every edge has the same dimension?

**Result.** In the binary normalization, the base-two logarithm of the asymptotic rank is `n` for even `n`, and `n - 1 + 1/[4(n - 2)]` for odd `n`. A common dimension `q` multiplies the binary exponent by `log2(q)`. The companion archive includes exact checks for small odd cycles and a uniform certificate for larger odd cycles. Certificate replay is not an end-to-end Lean 4 verification.

## Other manuscripts

| Manuscript | Main question or result | Files |
| --- | --- | --- |
| The Exact Asymptotic Rank Exponent of the Five-Cycle Graph Tensor | Determines the binary five-cycle exponent, `49/12`. | [PDF](c5/C5-asymptotic-rank-Wen-Jiang.pdf) · [Verification](c5/) |
| The Exact Asymptotic Rank Exponent of Odd Complete Graph Tensors | Determines the binary odd complete graph exponent, `n^2/4` for odd `n >= 3`. | [PDF](Kn/Kn-asymptotic-rank.pdf) · [Verification](Kn/) |
| Beyond the Maximum Cut for Graph Tensors | Determines the exponent for complete multipartite graphs and gives a strict separation from maximum cut for every odd cycle. | [PDF](beyond-maximum-cut/Beyond_the_Maximum_Cut_for_Graph_Tensors.pdf) · [Verification](beyond-maximum-cut/) |
| Exact Asymptotic Rank Exponents of Wheel Graph Tensors | Determines the exponent for wheel graph tensors, with separate even- and odd-rim formulas. | [PDF](wheel/wheel-graph-tensors.pdf) · [Manuscript notes](wheel/) |

## Citation

Cite each manuscript by its own title and PDF. See [references.bib](references.bib) for separate BibTeX entries for all six manuscripts and [CITATION.cff](CITATION.cff) for GitHub citation metadata.
