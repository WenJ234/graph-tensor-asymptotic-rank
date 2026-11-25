# The Exact Asymptotic Rank Exponent of the Five-Cycle Graph Tensor

Research paper by Wen Jiang. The base-2 logarithm of the complex asymptotic rank of the binary five-cycle graph tensor is 49/12.

- [Signed manuscript](C5-asymptotic-rank-Wen-Jiang.pdf)
- [Complete source and verification archive](C5-Wen-Jiang-source-and-verification.zip)
- [Exact rational certificate](c5_certificate.json)

Run `python3 verify_c5_exact.py` or `python3 verify_certificate_independent.py c5_certificate.json`. Both checkers were replayed against the original certificate: 24 splits, 20 exclusion leaves, 5 local leaves, and 50 exact contradictions. The second checker evaluates 51,200 corners. The verification does not reprove the external rectangular exponent, spectral curvature, or copositivity results cited in the paper.
