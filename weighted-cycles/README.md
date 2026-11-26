# The Asymptotic Rank of Weighted Cycle Tensors

**Wen Jiang · Research manuscript**

This paper addresses the exact asymptotic tensor rank of cycle graph tensors over the complex numbers with **independently chosen edge dimensions**. It covers unequal weights on odd cycles of length at least five, not only equal-weight cycles or cycles with one exceptional edge.

[Paper (PDF)](weighted_cycle_tensors_Wen_Jiang.pdf) · [Theorem 1.1 and the explicit formula (LaTeX)](weighted_cycle_tensors_Wen_Jiang.tex#L36-L75) · [Source and certificates (ZIP)](weighted_cycle_tensors_Wen_Jiang_source_and_certificates.zip) · [Separate seven-cycle diameter certificate (ZIP)](c7_diameter_247_256.zip)

## Exact formula for arbitrary edge weights

Let $q_i$ be the positive integer dimension of edge $i$, $w_i=\log_2 q_i$, and $S=\sum_i w_i$. Write $\Gamma(w)$ for the base-two logarithm of the asymptotic rank. Theorem 1.1 states that for every $n\ge3$,

$$
\Gamma(w)=
\begin{cases}
S, & n\text{ even},\\[2pt]
\displaystyle\max_{1\le i\le n}\Omega(S-w_i-w_{i+1},w_i,w_{i+1}), & n\text{ odd}.
\end{cases}
$$

Indices are cyclic. To evaluate $\Omega$, first sort its arguments as $x\ge y\ge z\ge0$. If $z=0$, then $\Omega=x+y$. Otherwise,

$$
\Omega(x,y,z)=x+y+\frac{\max\{0,(x+y)z-xy\}^2}{4xyz}.
$$

The formula also holds for nonnegative real logarithmic weights using the limiting definition in the paper. For odd cycles, checking all adjacent edge pairs suffices: each pair corresponds to a three-block grouping that isolates their common vertex.

**Unequal-weight example.** A five-cycle with edge dimensions $(4,2,2,2,2)$ has logarithmic weights $(2,1,1,1,1)$ in that cyclic order. The adjacent pairs with weights $(1,1)$ yield $\Omega(4,1,1)=81/16$; those incident to the weight-$2$ edge yield $\Omega(3,2,1)=5$. The exponent is therefore $81/16$.

This is a separate result from the [equal-weight cycle tensor paper](../cn/), in which all edges share one dimension.

## Reproduce the certificate checks

Extract the [source and certificates ZIP](weighted_cycle_tensors_Wen_Jiang_source_and_certificates.zip). From its root, run `python -B verify.py` to replay its proof certificates or `python -B verify.py examples` to check the 29 sample comparisons. The archive's README describes the Python and compiler requirements and how to run individual checks. For example, `python -B cycle_bounds.py --dims 4 4 4 4 8` evaluates the exponent $64/7$.

The archive provides computational proof certificates and checkers, not an end-to-end Lean 4 verification. Cite this manuscript separately using [references.bib](../references.bib).
