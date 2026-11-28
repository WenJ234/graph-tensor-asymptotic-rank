import C5.OddFoldTensor
import C5.OddCutWitness
import GraphCutRank

namespace WenJ.GraphTensor.MaxCut
open C5GeneralCycles
open scoped BigOperators
noncomputable section

private theorem fold_edgeCutSize_sum (k : ℕ) (f : Fin (2*k+3) → Bool) :
    edgeCutSize (foldEdges k) f =
      ∑ i : Fin (2*k+3), if f i ≠ f (finRotate _ i) then 1 else 0 := by
  simp only [edgeCutSize, foldEdges, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem odd_cycle_actual_cut_upper (k : ℕ) (f : Fin (2*k+3) → Bool) :
    edgeCutSize (foldEdges k) f ≤ 2*k+2 := by
  rw [fold_edgeCutSize_sum]
  let n := 2*k+3
  have hodd : Odd (Fintype.card (Fin n)) := by
    rw [Fintype.card_fin]
    exact ⟨k+1, by dsimp [n]; omega⟩
  have hsame := C5Placement.odd_permutation_has_uncut_edge hodd (finRotate n) f
  obtain ⟨i,hi⟩ := hsame
  have hlt : (∑ j : Fin n, if f j ≠ f (finRotate _ j) then (1:ℕ) else 0) <
      ∑ _j : Fin n, (1:ℕ) := by
    apply Finset.sum_lt_sum
    · intro j _
      split <;> omega
    · exact ⟨i, Finset.mem_univ _, by simp [hi]⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
  apply Nat.le_of_lt_succ
  refine lt_of_le_of_lt ?_ hlt
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : f j = f (finRotate _ j) <;> simp [hj]

theorem odd_cycle_actual_cut_attained (k : ℕ) :
    ∃ f : Fin (2*k+3) → Bool, edgeCutSize (foldEdges k) f = 2*k+2 := by
  let f (i : Fin (2*k+3)) : Bool := decide (i.val % 2 = 1)
  refine ⟨f,?_⟩
  rw [fold_edgeCutSize_sum, Fin.sum_univ_castSucc]
  have hl : f (Fin.last (2*k+2)) = f 0 := by
    have hk : (2*k+2)%2 ≠ 1 := by omega
    simp [f,hk]
  rw [finRotate_last, if_neg (not_not_intro hl), Nat.add_zero]
  have h (i : Fin (2*k+2)) : (if f i.castSucc ≠ f (finRotate _ i.castSucc)
      then (1:ℕ) else 0) = 1 := by
    have hi : finRotate (2*k+3) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [hi, if_pos]
    intro he
    have hb : (i.val%2 = 1) ↔ ((i.val+1)%2 = 1) := by
      simpa [f] using he
    omega
  simp_rw [h]
  simp

#print axioms odd_cycle_actual_cut_upper
#print axioms odd_cycle_actual_cut_attained
end
end WenJ.GraphTensor.MaxCut
