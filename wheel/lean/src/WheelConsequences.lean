import WheelExactExponent
import WheelMaxCut
import WheelConicOptima
import WheelArbitraryGrouping

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section

theorem even_wheel_excess (K : Type) [Field K] (k : ℕ) (hk : 2 ≤ k) :
    letI : NeZero (2*k) := ⟨by omega⟩
    Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K (2*k))) - (((3*(2*k))/2 : ℕ) : ℝ) =
      ((2*k : ℕ) : ℝ)/16 := by
  letI : NeZero (2*k) := ⟨by omega⟩
  rw [even_wheel_exact_exponent K k hk]
  have h : 3*(2*k)/2 = 3*k := by omega
  rw [h]
  push_cast
  ring

theorem odd_wheel_excess (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K (2*k+1))) -
      (((3*(2*k+1))/2 : ℕ) : ℝ) =
      (((2*k+1 : ℕ) : ℝ)-3)^2/(16*(((2*k+1 : ℕ) : ℝ)+1)) := by
  rw [odd_wheel_exact_exponent K k hk]
  have h : 3*(2*k+1)/2 = 3*k+1 := by omega
  rw [h]
  push_cast
  field_simp
  ring

theorem arbitrary_three_block_lower (K : Type) [Field K] (r : ℕ) [NeZero r]
    (σ : Option (ZMod r) → Fin 3) (hs : Function.Surjective σ) :
    formalOmega K (wheelBetween σ 0 1) (wheelBetween σ 2 1) (wheelBetween σ 2 0) ≤
      Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K r)) := by
  have h := grouped_asymptotic_rank_le σ hs (wheelTensor K r)
  rw [grouped_wheel_arbitrary] at h
  have hh := (triangle_asymptotic_rank_lower K _ _ _).trans h
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hh
  rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hl
  exact hl

#print axioms even_wheel_excess
#print axioms odd_wheel_excess
#print axioms arbitrary_three_block_lower
end
end WheelVerification
