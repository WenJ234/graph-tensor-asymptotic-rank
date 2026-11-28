import GraphHeavyPart
import SortedEdgeCounting

namespace WenJ.GraphTensor.MaxCut
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification GraphTensorVerification
open scoped BigOperators
noncomputable section

/-- The heavy-independent-set upper bound for the graph tensor itself,
with no assumption about the equivalence of ordered and undirected edges. -/
theorem graph_heavy_independent_exponent_upper {K : Type} [Field K] {n : ℕ}
    [Nonempty (Fin n)] (E : Finset (SortedEdge n)) (H : Finset (Fin n))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hH : (H.card:ℝ) = b)
    (hO : ((Finset.univ \ H).card:ℝ) = a)
    (hno : ∀ i ∈ H, ∀ j ∈ H, graphEdgeTest E i j = false) :
    Real.logb 2 (SiteTensor.asymptoticRank (simpleGraphWire K E)) ≤ a*b :=
  graph_heavy_part_exponent_upper E H (graphEdgeTest E) a b ha hab hH hO hno
    (sum_ordered_edges E)

/-- In a labelled complete multipartite graph the fiber of a part is an
independent set, so the size comparison alone is enough for this bound. -/
theorem multipartite_heavy_part_exponent_upper
    {K P : Type} [Field K] [DecidableEq P] {n : ℕ} [Nonempty (Fin n)]
    (label : Fin n → P) (heavy : P)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hH : ((Finset.univ.filter (fun i => label i = heavy)).card:ℝ) = b)
    (hO : ((Finset.univ \ Finset.univ.filter (fun i => label i = heavy)).card:ℝ) = a) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    Real.logb 2 (SiteTensor.asymptoticRank (simpleGraphWire K E)) ≤ a*b := by
  dsimp only
  apply graph_heavy_independent_exponent_upper _ _ a b ha hab hH hO
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  apply decide_eq_false
  intro h
  change (i,j) ∈ doubledEdges _ at h
  unfold doubledEdges at h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨e,he,ee⟩ := Finset.mem_map.mp h
    have he' := (Finset.mem_filter.mp he).2
    change e.val = (i,j) at ee
    rw [ee] at he'
    exact he' (hi'.trans hj'.symm)
  · obtain ⟨e,he,ee⟩ := Finset.mem_map.mp h
    have he' := (Finset.mem_filter.mp he).2
    change e.val.swap = (i,j) at ee
    have ee' : e.val = (j,i) := by simpa using congrArg Prod.swap ee
    rw [ee'] at he'
    exact he' (hj'.trans hi'.symm)

#print axioms multipartite_heavy_part_exponent_upper
#print axioms graph_heavy_independent_exponent_upper
end
end WenJ.GraphTensor.MaxCut
