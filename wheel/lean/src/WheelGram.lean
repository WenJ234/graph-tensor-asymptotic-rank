import WheelMetricCP
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WheelVerification
open scoped BigOperators

/-- A positive combination of outer products is PSD, in the real
quadratic-form definition used for the wheel SDP. -/
theorem psd_of_rank_one_family {I J : Type} [Fintype I] [Fintype J]
    (z : I → ℝ) (f : J → I → ℝ) (c : ℝ) (hc : 0 ≤ c) (u : I → ℝ) :
    0 ≤ ∑ i, ∑ j,
      u i * (z i*z j + c*(∑ h, f h i * f h j)) * u j := by
  have hz : ∀ g : I → ℝ,
      (∑ i, ∑ j, u i * (g i*g j) * u j) = (∑ i, u i*g i)^2 := by
    intro g
    have h (i j : I) : u i*(g i*g j)*u j = (u i*g i)*(u j*g j) := by ring
    simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have ha (i j : I) :
      u i * (z i*z j + c*(∑ h, f h i * f h j)) * u j =
      u i*(z i*z j)*u j + c*(∑ h, u i*(f h i*f h j)*u j) := by
    rw [mul_add, add_mul]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    ring
  simp_rw [ha, Finset.sum_add_distrib, ← Finset.mul_sum, hz]
  have hswap :
      (∑ i : I, ∑ j : I, ∑ h : J, u i*(f h i*f h j)*u j) =
      ∑ h : J, ∑ i : I, ∑ j : I, u i*(f h i*f h j)*u j := by
    simp_rw [show ∀ i : I, (∑ j : I, ∑ h : J, u i*(f h i*f h j)*u j) =
      ∑ h : J, ∑ j : I, u i*(f h i*f h j)*u j from fun _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [hz]
  exact add_nonneg (sq_nonneg _) (mul_nonneg hc (Finset.sum_nonneg fun _ _ => sq_nonneg _))

#print axioms psd_of_rank_one_family
end WheelVerification
