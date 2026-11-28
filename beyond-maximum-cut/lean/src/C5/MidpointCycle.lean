import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace C5GeneralCycles
open scoped BigOperators

/-- A finite periodic collection of CN midpoint inequalities cannot have
a positive separation between any pair of opposing neighbors. -/
theorem midpoint_cycle {I : Type*} [Fintype I] (e : I ≃ I)
    (f d : I → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h : ∀ i, f i ≤ (f (e.symm i) + f (e i))/2 - d i/4) :
    ∀ i, d i = 0 := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => h i)
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    Equiv.sum_comp] at hs
  have h0 : (∑ i, d i) ≤ 0 := by linarith
  intro i
  have hi : d i ≤ ∑ j, d j :=
    Finset.single_le_sum (f := d) (fun j _ => hd j) (Finset.mem_univ i)
  exact le_antisymm (hi.trans h0) (hd i)

#print axioms midpoint_cycle
end C5GeneralCycles
