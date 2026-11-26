import WheelGram
import Mathlib.Tactic.FieldSimp

namespace WheelVerification
noncomputable section

def oddWheelX (r : ℝ) : ℝ := (r+1)/4
def oddWheelS (r : ℝ) : ℝ := oddWheelX r/r
def oddWheelA (r : ℝ) : ℝ := (r^2-(oddWheelX r)^2)/(r^2-1)

theorem oddWheel_parameters (r : ℝ) (hr : 3 ≤ r) :
    0 ≤ oddWheelS r ∧ oddWheelS r ≤ 1 ∧
    0 ≤ oddWheelA r ∧ oddWheelA r ≤ 1 ∧
    (oddWheelS r)^2 + oddWheelA r*(1-(1/r)^2) = 1 := by
  have rp : 0 < r := by linarith
  have hx : 1 ≤ oddWheelX r := by unfold oddWheelX; linarith
  have hxr : oddWheelX r ≤ r := by unfold oddWheelX; linarith
  have hden : 0 < r^2-1 := by
    nlinarith [mul_nonneg (show 0 ≤ r-3 by linarith) (show 0 ≤ r+3 by linarith)]
  have hnum : 0 ≤ r^2-(oddWheelX r)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxr) (show 0 ≤ r+oddWheelX r by linarith)]
  have hnum' : r^2-(oddWheelX r)^2 ≤ r^2-1 := by
    nlinarith [mul_nonneg (show 0 ≤ oddWheelX r-1 by linarith) (show 0 ≤ oddWheelX r+1 by linarith)]
  refine ⟨div_nonneg (by linarith) rp.le, (div_le_one rp).mpr hxr,
    div_nonneg hnum hden.le, (div_le_one hden).mpr hnum', ?_⟩
  unfold oddWheelS oddWheelA
  field_simp [rp.ne',hden.ne']
  <;> ring

#print axioms oddWheel_parameters
end
end WheelVerification
