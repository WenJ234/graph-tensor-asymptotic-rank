import OAI.LinearAlgebra.SpectralBooks.ExactExponent
import OAI.LinearAlgebra.SpectralBooks.Tensor
import IntegralRectangleRank

namespace C5GeneralCycles
open OAI.LinearAlgebra.SpectralBooks
open scoped BigOperators

theorem odd_cycle_rectangle_value (F : Type*) [Field F] (h : ℝ) (hh : 1 ≤ h) :
    formalOmega F h 1 1 = h+1+1/(4*h) := by
  rw [rectangular_exponent]
  dsimp only
  rw [max_eq_left (show 0 ≤ h by linarith),
    max_eq_left zero_le_one,min_self,max_self,max_eq_left hh,min_eq_right hh]
  rw [show h+1+1-h-1=1 by ring,show (h+1)*1-h*1=1 by ring]
  norm_num

/-- A finite-size lower bound with the same exponent, specialized from the
verified arbitrary-width rectangle inequality used by the wheel manuscript. -/
theorem odd_cycle_rectangle_rank_lower (F : Type*) [Field F] {n h : ℕ}
    (hn : 2 ≤ n) (hh : 1 ≤ h) :
    (n:ℝ)^((h:ℝ)+1+1/(4*h)) ≤ (tensorRank (matrixTensor F (n^h) n n):ℝ) := by
  have hR := WheelVerification.integral_rectangular_rank_lower F hn h 1 1
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  rw [Nat.cast_one,odd_cycle_rectangle_value F h hh'] at hR
  rw [Nat.pow_one] at hR
  exact hR

#print axioms odd_cycle_rectangle_value
#print axioms odd_cycle_rectangle_rank_lower
end C5GeneralCycles
