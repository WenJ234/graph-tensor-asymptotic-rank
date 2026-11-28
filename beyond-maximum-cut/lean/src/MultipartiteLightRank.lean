import GraphCliqueRestriction
import OddCliquePairCount
import RectangleAlgebra
import WheelRectangle

namespace WenJ.GraphTensor.MaxCut
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification GraphTensorVerification OddCliquePaper
open scoped BigOperators
noncomputable section

theorem formalOmega_multipartite_block_sizes (K : Type) [Field K]
    (x y z : ℝ) (hz : 0 < z) (hzy : z ≤ y) (hyx : y ≤ x) (hhalf : x ≤ y+z) :
    formalOmega K (x*y) (x*z) (y*z) = (x+y+z)^2/4 := by
  have hy := hz.trans_le hzy
  have hx := hy.trans_le hyx
  rw [formalOmega_sorted K _ _ _
    (mul_le_mul_of_nonneg_left hzy hx.le)
    (mul_le_mul_of_nonneg_right hyx hz.le)
    (mul_nonneg hy.le hz.le)]
  simpa only [rectangle, max_comm (0:ℝ)] using rectangle_three_group_algebra x y z hx hy hz hhalf

theorem multipartite_between_count {n : ℕ} {P : Type} [DecidableEq P]
    (label : Fin n → P) (group : P → Fin 3) (i j : Fin 3) (hij : i ≠ j) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    graphBetween (E.toList.map Subtype.val) (group ∘ label) i j =
      Fintype.card (ColorClass (group ∘ label) i) *
        Fintype.card (ColorClass (group ∘ label) j) := by
  classical
  dsimp only
  rw [← pairCount_eq_product (group ∘ label) i j hij]
  unfold graphBetween pairCount
  rw [List.map_map, Finset.sum_map_toList]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : label e.val.1 = label e.val.2
  · have hzero : ¬ ((group (label e.val.2) = i ∧ group (label e.val.2) = j) ∨
        (group (label e.val.2) = j ∧ group (label e.val.2) = i)) := by
      rintro (⟨hi,hj⟩ | ⟨hj,hi⟩) <;> exact hij (hi.symm.trans hj)
    simp [h,between,Function.comp_def,hzero]
  · simp [h,between,Function.comp_def]

/-- A three-way grouping of whole parts yields the exact square lower
bound for the actual multipartite graph tensor.  The largest group
is assigned label 1 to match the pinned rectangular width order. -/
theorem multipartite_three_color_lower {K P : Type} [Field K] [DecidableEq P]
    {n : ℕ} [Nonempty (Fin n)] (label : Fin n → P) (group : P → Fin 3)
    (x y z : ℕ)
    (hx : Fintype.card (ColorClass (group ∘ label) 1) = x)
    (hy : Fintype.card (ColorClass (group ∘ label) 0) = y)
    (hz : Fintype.card (ColorClass (group ∘ label) 2) = z)
    (hzpos : 0 < z) (hzy : z ≤ y) (hyx : y ≤ x)
    (hsum : x+y+z = n) (hhalf : x ≤ y+z) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    (n:ℝ)^2/4 ≤ Real.logb 2 (SiteTensor.asymptoticRank (simpleGraphWire K E)) := by
  dsimp only
  let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
  change _ ≤ Real.logb 2 (SiteTensor.asymptoticRank (simpleGraphWire K E))
  have hs : Function.Surjective (group ∘ label) := by
    intro i
    have hc : 0 < Fintype.card (ColorClass (group ∘ label) i) := by
      fin_cases i
      · change 0 < Fintype.card (ColorClass (group ∘ label) 0)
        rw [hy]
        omega
      · change 0 < Fintype.card (ColorClass (group ∘ label) 1)
        rw [hx]
        omega
      · change 0 < Fintype.card (ColorClass (group ∘ label) 2)
        rw [hz]
        omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hc
    exact ⟨v.val,v.property⟩
  have h := graph_three_block_rank_lower K (E.toList.map Subtype.val) (group ∘ label) hs
  rw [multipartite_between_count label group 0 1 (by decide),
    multipartite_between_count label group 2 1 (by decide),
    multipartite_between_count label group 2 0 (by decide),hx,hy,hz,
    ← simpleGraphWire_eq_list] at h
  push_cast at h
  rw [mul_comm (y:ℝ) (x:ℝ),mul_comm (z:ℝ) (x:ℝ),mul_comm (z:ℝ) (y:ℝ),
    formalOmega_multipartite_block_sizes K _ _ _
      (by exact_mod_cast hzpos) (by exact_mod_cast hzy) (by exact_mod_cast hyx)
      (by exact_mod_cast hhalf)] at h
  have hnr : (x:ℝ)+(y:ℝ)+(z:ℝ) = (n:ℝ) := by exact_mod_cast hsum
  simpa only [hnr] using h

#print axioms multipartite_three_color_lower
#print axioms formalOmega_multipartite_block_sizes
#print axioms multipartite_between_count
end
end WenJ.GraphTensor.MaxCut
