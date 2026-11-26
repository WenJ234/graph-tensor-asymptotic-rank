import WheelArithmetic
import OAI.LinearAlgebra.SpectralBooks.ExactExponent

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks

theorem formalOmega_sorted (K : Type) [Field K] (a b c : ℝ)
    (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c) :
    formalOmega K a b c = rectangle a b c := by
  rw [rectangular_exponent,rectangle]
  dsimp only
  rw [max_eq_left (hc.trans (hbc.trans hab)), max_eq_left (hc.trans hbc),
    max_eq_left hc, max_eq_left hbc, min_eq_right hbc, max_eq_left hab,
    min_eq_right (hbc.trans hab)]
  have h : a+b+c-a-c = b := by ring
  rw [h]

theorem wheel_rectangle_even (K : Type) [Field K] (k : ℝ) (hk : 0 < k) :
    formalOmega K (2*k) k k = 25*(2*k)/16 := by
  rw [formalOmega_sorted K _ _ _ (by linarith) (le_refl _) hk.le]
  exact rectangle_even k hk

theorem wheel_rectangle_odd (K : Type) [Field K] (k : ℝ) (hk : 1 ≤ k) :
    formalOmega K (2*k) (k+1) k = (5*(2*k+1)+1)^2/(16*((2*k+1)+1)) := by
  rw [formalOmega_sorted K _ _ _ (by linarith) (by linarith) (by linarith)]
  exact rectangle_odd k hk

#print axioms wheel_rectangle_even
#print axioms wheel_rectangle_odd
end WheelVerification
