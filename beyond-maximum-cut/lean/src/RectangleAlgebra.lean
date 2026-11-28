import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
namespace WenJ.GraphTensor.MaxCut
theorem rectangle_three_group_algebra
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hhalf : p ≤ q + r) :
    p*q + p*r +
      (max 0 (((p*q)+(p*r))*(q*r) - (p*q)*(p*r)))^2 / (4*(p*q)*(p*r)*(q*r)) =
      (p+q+r)^2/4 := by
  have hpoly : ((p*q)+(p*r))*(q*r) - (p*q)*(p*r) = p*q*r*(q+r-p) := by ring
  rw [hpoly, max_eq_right (mul_nonneg (by positivity) (sub_nonneg.mpr hhalf))]
  field_simp [ne_of_gt hp, ne_of_gt hq, ne_of_gt hr]; ring
end WenJ.GraphTensor.MaxCut
#print axioms WenJ.GraphTensor.MaxCut.rectangle_three_group_algebra
