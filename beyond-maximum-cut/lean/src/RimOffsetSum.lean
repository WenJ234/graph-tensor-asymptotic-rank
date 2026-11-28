import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! At one vertex the consecutive offset pairs enumerate exactly the
    internal offsets. This is the directed form of the chord count. -/
namespace WheelVerification
open scoped BigOperators

theorem paired_offset_sum (f : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range m, (f (2*(j+1)) + f (2*(j+1)+1))) =
      ∑ i ∈ Finset.range (2*m), f (i+2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have he : 2*(m+1) = (2*m+1)+1 := by omega
    rw [he, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : 2*m+1+1 = 2*m+2 := by omega
    have h2 : 2*m+1+1+1 = 2*m+1+2 := by omega
    rw [h2, h1]
    exact (add_assoc _ _ _).symm

theorem paired_rim_right_sum (r k : ℕ) [NeZero r]
    (d : ZMod r → ZMod r → ℝ) :
    (∑ j ∈ Finset.range (k-1), ∑ v : ZMod r,
      (d v (v + (2*(j+1) : ℕ)) + d v (v + (2*(j+1)+1 : ℕ)))) =
    ∑ v : ZMod r, ∑ i ∈ Finset.range (2*(k-1)), d v (v + (i+2 : ℕ)) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => paired_offset_sum (fun i => d v (v + (i : ℕ))) (k-1)

#print axioms paired_offset_sum
#print axioms paired_rim_right_sum
end WheelVerification
