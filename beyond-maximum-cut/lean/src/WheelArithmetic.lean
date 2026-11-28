import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Local, unconditional arithmetic pieces for the wheel manuscript.
These neither import nor establish its spectral or conic dependencies. -/
namespace WheelVerification

def rimNext (r i : ℕ) : ℕ := if i+1 < r then i+1 else 0

theorem rim_cross_even (k i : ℕ) (hi : i < 2*k) :
    i % 2 ≠ rimNext (2*k) i % 2 := by
  unfold rimNext
  split <;> omega

theorem rim_cross_odd (k i : ℕ) (hi : i < 2*k+1) :
    (i % 2 ≠ rimNext (2*k+1) i % 2) ↔ i < 2*k := by
  unfold rimNext
  split <;> omega

theorem even_spokes (k j : ℕ) (hj : j < k) :
    2*j < 2*k ∧ 2*j+1 < 2*k ∧ (2*j)%2 = 0 ∧ (2*j+1)%2 = 1 := by omega

theorem odd_spokes (k j : ℕ) (hj : j ≤ k) :
    2*j < 2*k+1 ∧ (2*j+1 < 2*k+1 ↔ j < k) ∧
    (2*j)%2 = 0 ∧ (2*j+1)%2 = 1 := by omega

noncomputable def rectangle (x y z : ℝ) : ℝ :=
  x+y+(max ((x+y)*z-x*y) 0)^2/(4*x*y*z)

theorem rectangle_even (k : ℝ) (hk : 0 < k) : rectangle (2*k) k k = 25*(2*k)/16 := by
  have h : (2*k+k)*k-(2*k)*k = k^2 := by ring
  unfold rectangle
  rw [h, max_eq_left (sq_nonneg k)]
  field_simp
  <;> ring

theorem rectangle_odd (k : ℝ) (hk : 1 ≤ k) :
    rectangle (2*k) (k+1) k = (5*(2*k+1)+1)^2/(16*((2*k+1)+1)) := by
  have hp : 0 < k := by linarith
  have hq : 0 < k+1 := by linarith
  have h : (2*k+(k+1))*k-(2*k)*(k+1) = k*(k-1) := by ring
  unfold rectangle
  rw [h, max_eq_left (mul_nonneg hp.le (by linarith))]
  field_simp
  <;> ring

theorem odd_lp_step (r L S D : ℝ) (hr : 0 < r+1)
    (pairing : 4*D ≥ (r+1)*L)
    (copositive : 4*(D+((r+1)/4)*S) ≤ (r+(r+1)/4)^2) :
    L+S ≤ (5*r+1)^2/(16*(r+1)) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) hr)).2
  nlinarith only [pairing, copositive]

theorem cut_upper (r s : ℕ) (hs : s ≤ r) :
    s+2*min s (r-s) ≤ (3*r)/2 := by
  by_cases h : s ≤ r-s
  · rw [Nat.min_eq_left h]; omega
  · rw [Nat.min_eq_right (by omega)]; omega

theorem cut_even (k : ℕ) : k+2*min k (2*k-k) = (3*(2*k))/2 := by
  have h : 2*k-k = k := by omega
  rw [h, min_self]
  omega

theorem cut_odd (k : ℕ) : k+1+2*min (k+1) (2*k+1-(k+1)) = (3*(2*k+1))/2 := by
  have h : 2*k+1-(k+1) = k := by omega
  rw [h, Nat.min_eq_right (by omega)]
  omega

#print axioms rim_cross_even
#print axioms rim_cross_odd
#print axioms even_spokes
#print axioms odd_spokes
#print axioms rectangle_even
#print axioms rectangle_odd
#print axioms odd_lp_step
#print axioms cut_upper
#print axioms cut_even
#print axioms cut_odd
end WheelVerification
