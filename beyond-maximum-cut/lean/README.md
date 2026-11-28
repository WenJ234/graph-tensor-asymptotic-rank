# Lean verification of Beyond the Maximum Cut for Graph Tensors

This project accompanies [Beyond the Maximum Cut for Graph Tensors](../Beyond_the_Maximum_Cut_for_Graph_Tensors.pdf). Target PDF SHA-256: `7986de4e07e0bdf0775591111c6db107dfe668eecdecb9dc6cfab5ca0f92d362`.

The graph tensor is the sitewise product of binary wires indexed by the edges. The development identifies the grouped tensor with the rectangular tensor before applying the pinned division-free arithmetic exponent. For the strict upper endpoint, it uses the metric and CAT(0) extension of an attaining spectral point and proves its copositivity constraints through cloning and the complete-graph bound. The strict upper comparison does not claim equality at the lower endpoint.

| Manuscript claim | Lean entry point |
| --- | --- |
| Proposition 1: cut lower bound, bipartite exact rank | `maxCutWeight_le_graph_exponent`, `bipartite_graph_rank_of_coloring` |
| Lemma 2: actual graph grouping and three-block lower bound | `graph_groupClass_eq_triangle`, `graph_three_block_rank_lower` |
| Theorem 3: complete graph exact exponent and all odd-cycle cut gaps | `complete_graph_exponent_exact`, `odd_cycle_paper_lower_and_actual_cut` |
| Theorem 4: exact multipartite exponent and the cut equality criterion | `exists_maximal_part`, `multipartite_exponent_and_maxCut` |
| Proposition 5: upper bound for every Euclidean placement and equality on the line | `price_ratio_le_maxCut`, `real_line_price_ratio_isGreatest` |
| Proposition 6: strict bound for the actual five-cycle | `five_cycle_maxcut_paper_bounds` |

## Reproduce

With Git, Python 3 and elan installed, run `python3 replay.py` from this directory. The script fetches the exact dependency revisions, obtains the pinned Mathlib cache, applies the included fixed-point compatibility patch and rebuilds the proof dependencies. It checks the complete axiom sets listed in `AuditBeyondMaxCut.lean` against `propext`, `Classical.choice` and `Quot.sound`.

OpenAI/math is pinned at `3344da59991ed94f9ba711217b29c1d760badfa6` and Lemmata at `a20ff2d299b36e7357170ddd584eb4e462e95b06`. The toolchain and remaining pins are in `lean-toolchain` and `lake-manifest.json`.
