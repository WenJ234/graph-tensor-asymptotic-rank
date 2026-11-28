import GraphCliqueRestriction
import GraphCutRank
import EuclideanPrice
import WireGraphStructure

namespace WenJ.GraphTensor.MaxCut
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification GraphTensorVerification
open scoped BigOperators
noncomputable section

def graphEdgeSet {n : ℕ} (E : Finset (SortedEdge n)) : Finset (Fin n × Fin n) :=
  E.map ⟨Subtype.val, Subtype.val_injective⟩

theorem graph_cutWeight_eq_edgeCutSize {n : ℕ} (E : Finset (SortedEdge n))
    (f : Fin n → Bool) :
    cutWeight (graphEdgeSet E) f = (edgeCutSize (E.toList.map Subtype.val) f : ℝ) := by
  unfold cutWeight graphEdgeSet edgeCutSize
  rw [Finset.sum_map,List.map_map,Finset.sum_map_toList,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
  by_cases he : f e.val.1 = f e.val.2 <;> simp [he]

theorem graph_wire_asymptoticRank_ge_one {I K : Type} [Fintype I] [Nonempty I] [Field K]
    (es : List (I × I)) : 1 ≤ SiteTensor.asymptoticRank (graphWireTensor K es) := by
  have hne : graphWireTensor K es ≠ 0 := graphClass_ne_zero es
  unfold SiteTensor.asymptoticRank
  apply le_ciInf
  intro m
  have hpow : graphWireTensor K es ^ (m+1) ≠ 0 := pow_ne_zero _ hne
  have hr : 1 ≤ rank (graphWireTensor K es ^ (m+1)) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    have h := le_rank (graphWireTensor K es ^ (m+1))
    rw [hz,Nat.cast_zero] at h
    exact hpow (le_antisymm h (zero_le_tensor _))
  exact Real.one_le_rpow (by exact_mod_cast hr) (by positivity)

theorem graph_cut_le_exponent_any {I : Type} [Fintype I] [Nonempty I]
    (K : Type) [Field K] (es : List (I × I)) (f : I → Bool) :
    (edgeCutSize es f : ℝ) ≤ Real.logb 2 (SiteTensor.asymptoticRank (graphWireTensor K es)) := by
  classical
  by_cases h : Function.Surjective f
  · exact graph_cut_le_exponent K es f h
  · have hc (i j : I) : f i = f j := by
      unfold Function.Surjective at h
      push_neg at h
      obtain ⟨b,hb⟩ := h
      have hi := hb i
      have hj := hb j
      cases b <;> cases h₁ : f i <;> cases h₂ : f j <;> simp_all
    have hz : edgeCutSize es f = 0 := by
      induction es with
      | nil => rfl
      | cons e es ih =>
        change (if f e.1 ≠ f e.2 then 1 else 0) + edgeCutSize es f = 0
        simp [hc e.1 e.2, ih]
    rw [hz,Nat.cast_zero]
    exact Real.logb_nonneg (by norm_num) (graph_wire_asymptoticRank_ge_one (K := K) es)

/-- Use the same edge-set MaxCut for the cut lower bound and the Euclidean
price comparison, including the edgeless graph and trivial cuts. -/
theorem maxCutWeight_le_graph_exponent {K : Type} [Field K] {n : ℕ} [Nonempty (Fin n)]
    (E : Finset (SortedEdge n)) :
    maxCutWeight (graphEdgeSet E) ≤ Real.logb 2 (SiteTensor.asymptoticRank (simpleGraphWire K E)) := by
  obtain ⟨f,hf⟩ := cut_attains_maxCutWeight (graphEdgeSet E)
  rw [← hf,graph_cutWeight_eq_edgeCutSize,simpleGraphWire_eq_list]
  exact graph_cut_le_exponent_any K _ f

#print axioms graph_cutWeight_eq_edgeCutSize
#print axioms graph_cut_le_exponent_any
#print axioms maxCutWeight_le_graph_exponent
end
end WenJ.GraphTensor.MaxCut
