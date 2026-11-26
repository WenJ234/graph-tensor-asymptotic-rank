# The Asymptotic Rank of Weighted Cycle Tensors

**Wen Jiang**

This paper determines the asymptotic rank exponent of a complex cycle tensor for arbitrary edge dimensions. On an odd cycle, the exponent is the largest rectangular matrix multiplication exponent obtained by isolating a single vertex. The formula extends to nonnegative real logarithmic weights.

- [Paper (PDF)](weighted_cycle_tensors_Wen_Jiang.pdf)
- [Single-file LaTeX source](weighted_cycle_tensors_Wen_Jiang.tex)
- [Complete source, proof certificates and exact checkers (ZIP)](weighted_cycle_tensors_Wen_Jiang_source_and_certificates.zip)

## Reproduce the results

Extract the source and certificates ZIP. From its root, run `python -B verify.py` to replay the proof certificates or `python -B verify.py examples` to check the 29 sample comparisons. The included README describes the Python and compiler requirements and how to run individual checks.

For an example with integer dimensions, `python -B cycle_bounds.py --dims 4 4 4 4 8` returns the exact exponent `64/7`.
