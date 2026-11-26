import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic

/-! For each fixed offset, translating all rim vertices visits every rim edge once. -/
namespace WheelVerification
open scoped BigOperators

theorem rim_translate_sum (r : ℕ) [NeZero r] (d : ZMod r → ZMod r → ℝ)
    (a : ZMod r) :
    (∑ v : ZMod r, d (v+a) (v+a+1)) = ∑ v : ZMod r, d v (v+1) := by
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

theorem paired_rim_left_sum (r k : ℕ) [NeZero r] (d : ZMod r → ZMod r → ℝ) :
    (∑ j ∈ Finset.range (k-1), ∑ v : ZMod r,
      d (v + (2*((j:ℕ)+1) : ℕ)) (v + (2*((j:ℕ)+1) : ℕ) + 1)) =
      ((k-1 : ℕ) : ℝ) * ∑ v : ZMod r, d v (v+1) := by
  calc
    _ = ∑ _j ∈ Finset.range (k-1), ∑ v : ZMod r, d v (v+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact rim_translate_sum r d (↑(2*(j+1) : ℕ))
    _ = _ := by simp [nsmul_eq_mul]

#print axioms rim_translate_sum
#print axioms paired_rim_left_sum
end WheelVerification
