import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace C5GeneralCycles
open scoped BigOperators

/-- Mark 0 is the singleton C; the other sites alternate A, B. -/
def foldColor (k : ℕ) (i : Fin (2*k+3)) : Fin 3 :=
  if i.val=0 then 2 else if i.val%2=1 then 0 else 1

theorem fold_color_surjective (k : ℕ) : Function.Surjective (foldColor k) := by
  intro i
  fin_cases i
  · exact ⟨⟨1,by omega⟩,rfl⟩
  · refine ⟨⟨2,by omega⟩,?_⟩
    simp [foldColor,Matrix.cons_val_zero]
  · exact ⟨⟨0,by omega⟩,rfl⟩

/-- Counting the edges of the three-site quotient, with multiplicity.
The AB exponent is m−2 and the other two exponents are one. -/
theorem fold_color_wire_sum (k : ℕ) (d : Fin 3 → Fin 3 → ℝ)
    (hs : ∀ i j,d i j=d j i) :
    (∑ i : Fin (2*k+3), d (foldColor k i) (foldColor k (finRotate _ i))) =
      (2*k+1:ℕ)*d 0 1 + d 1 2 + d 2 0 := by
  let f (i : Fin (2*k+3)) := d (foldColor k i) (foldColor k (finRotate _ i))
  have hl : f (Fin.last (2*k+2)) = d 1 2 := by
    unfold f
    rw [finRotate_last]
    have h : foldColor k (Fin.last (2*k+2))=1 := by
      unfold foldColor
      change (if 2*k+2=0 then 2 else if (2*k+2)%2=1 then 0 else 1)=1
      rw [if_neg (by omega),if_neg (by omega)]
    rw [h]
    rfl
  have h0 : f (0 : Fin (2*k+3)) = d 2 0 := by
    unfold f
    have hh : finRotate (2*k+3) 0 = ⟨1,by omega⟩ :=
      finRotate_of_lt (n:=2*k+2) (k:=0) (by omega)
    rw [hh]
    rfl
  have hodd (j : Fin (2*k+1)) : f j.succ.castSucc=d 0 1 := by
    unfold f
    have hh : finRotate (2*k+3) j.succ.castSucc = j.succ.succ :=
      finRotate_of_lt j.succ.isLt
    rw [hh]
    let n := j.val
    change d (if n+1=0 then 2 else if (n+1)%2=1 then 0 else 1)
      (if n+2=0 then 2 else if (n+2)%2=1 then 0 else 1) = _
    rw [if_neg (show n+1≠0 by omega), if_neg (show n+2≠0 by omega)]
    by_cases h : (n+1)%2=1
    · rw [if_pos h,if_neg (show (n+2)%2≠1 by omega)]
    · rw [if_neg h,if_pos (show (n+2)%2=1 by omega),hs 1 0]
  change (∑ i,f i) = _
  rw [Fin.sum_univ_castSucc,hl,Fin.sum_univ_succ]
  change f 0 + (∑ i : Fin (2*k+1), f i.succ.castSucc) + d 1 2 = _
  rw [h0]
  simp only [hodd,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

#print axioms fold_color_surjective
#print axioms fold_color_wire_sum
end C5GeneralCycles
