import GraphThreeBlock
import SpectralCliqueBound
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ComparisonBound

namespace WenJ.GraphTensor.MaxCut
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification GraphTensorVerification
open scoped BigOperators
noncomputable section

private theorem one_le_wire (K : Type) [Field K] {I : Type} [Fintype I]
    [Nonempty I] (a b : I) : 1 ≤ wireAt K a b := by
  apply one_le_of_ne_zero
  intro h
  have hd : (Raw.diagonal (Fin 2) K (Fin 2)).coeff ≠ 0 := by
    intro he
    have hz := congrFun he (fun _ => (0 : Fin 2))
    change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at hz
    simp [Raw.diagonal, funext_iff] at hz
  exact (((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff ![a,b]).mpr hd)
    ((ofRaw_eq_zero_iff _).mp h)

/-- An undirected simple graph on labelled vertices, with each edge
stored once, is the product of the binary wires in its edge subset. -/
def simpleGraphWire (K : Type) [Field K] {n : ℕ} [Nonempty (Fin n)]
    (E : Finset (SortedEdge n)) : TensorClass.{0} (Fin n) K :=
  ∏ e ∈ E, wireAt K e.val.1 e.val.2

/-- Exact conversion to the edge-list model used by the grouping proofs. -/
theorem simpleGraphWire_eq_list (K : Type) [Field K] {n : ℕ} [Nonempty (Fin n)]
    (E : Finset (SortedEdge n)) :
    simpleGraphWire K E =
      graphWireTensor K (E.toList.map Subtype.val) := by
  unfold simpleGraphWire graphWireTensor
  rw [List.map_map, Finset.prod_map_toList] <;> rfl

theorem simpleGraphWire_le_complete (K : Type) [Field K] {n : ℕ} [Nonempty (Fin n)]
    (E : Finset (SortedEdge n)) :
    simpleGraphWire K E ≤ ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2) := by
  classical
  rw [completeGraph_eq_wires]
  have he (e : SortedEdge n) :
      ofRaw (cliqueWire K e) = wireAt K e.val.1 e.val.2 := by
    have h : sortedEndpoints e = ![e.val.1,e.val.2] := by
      funext i
      fin_cases i <;> simp [sortedEndpoints]
    rw [wireAt,cliqueWire,h]
  simp_rw [he]
  unfold simpleGraphWire
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    (fun e _ _ => one_le_wire K e.val.1 e.val.2)

/-- The matching complete-graph upper bound for actual simple graph tensors. -/
theorem simpleGraphWire_asymptoticRank_upper (K : Type) [Field K] {n : ℕ}
    [Nonempty (Fin n)] (hn : 2 ≤ n) (E : Finset (SortedEdge n)) :
    SiteTensor.asymptoticRank (simpleGraphWire K E) ≤
      (2 : ℝ)^((n : ℝ)^2 / 4) := by
  have hnt : 1 < Fintype.card (Fin n) := by simpa using (show 1 < n by omega)
  letI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp hnt
  obtain ⟨φ,hφ⟩ := exists_spectral_value_eq_asymptoticRank (simpleGraphWire K E)
  rw [← hφ]
  have h := simpleGraphWire_le_complete K E
  have hh : (φ.val (simpleGraphWire K E) : ℝ) ≤
      φ.val (ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2)) := by
    exact_mod_cast (φ.property.2.2.2.2 _ _ h)
  exact hh.trans ((spectral_le_lemmata φ
      (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2)).trans
      (Lemmata.TensorRank.completeGraphBounds (𝕜 := K) n 2 hn (by decide)).2.1)

#print axioms simpleGraphWire_le_complete
#print axioms simpleGraphWire_asymptoticRank_upper
end
end WenJ.GraphTensor.MaxCut
