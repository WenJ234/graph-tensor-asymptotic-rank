import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Final scalar step of the odd-wheel conic bound, including the smallest rim. -/
namespace WheelVerification

theorem odd_wheel_upper_of_pairing_and_cp (r L S D : ℝ) (hr : 0 < r + 1)
    (hpair : (r + 1) * L ≤ 4 * D)
    (hcp : 4 * (D + ((r + 1) / 4) * S) ≤ (r + (r + 1) / 4) ^ 2) :
    L + S ≤ (5 * r + 1) ^ 2 / (16 * (r + 1)) := by
  apply (le_div_iff₀ (show 0 < 16 * (r + 1) by linarith)).mpr
  nlinarith only [hpair, hcp]

#print axioms odd_wheel_upper_of_pairing_and_cp
end WheelVerification
