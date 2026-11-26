import TriangleRankBridge
import WheelGroupRank

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section

private theorem log_of_lower (w x : ℝ) (h : (2 : ℝ)^w ≤ x) :
    w ≤ Real.logb 2 x := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) w) h
  rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hl
  exact hl

theorem formalOmega_swap23 (K : Type) [Field K] (a b c : ℝ) :
    formalOmega K a b c = formalOmega K a c b := by
  rw [rectangular_exponent, rectangular_exponent]
  dsimp only
  rw [max_comm (max b 0) (max c 0), min_comm (max b 0) (max c 0)]
  have h : max a 0 + max b 0 + max c 0 =
      max a 0 + max c 0 + max b 0 := by ring
  rw [h]

theorem even_wheel_exact_exponent (K : Type) [Field K] (k : ℕ) (hk : 2 ≤ k) :
    letI : NeZero (2*k) := ⟨by omega⟩
    Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K (2*k))) = 25*((2*k : ℕ) : ℝ)/16 := by
  letI : NeZero (2*k) := ⟨by omega⟩
  apply le_antisymm (wheel_rank_upper_by_rim_rows K (2*k))
  have h := grouped_asymptotic_rank_le (K := K) (wheelGroup (2*k))
      (wheelGroup_surj _ (by omega)) (wheelTensor K (2*k))
  rw [grouped_even_wheel_eq_triangle] at h
  have hl := (triangle_asymptotic_rank_lower K (2*k) k k).trans h
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  push_cast at hl
  rw [wheel_rectangle_even K _ hkR] at hl
  have he := log_of_lower _ _ hl
  push_cast
  exact he

theorem odd_wheel_exact_exponent (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K (2*k+1))) =
      (5 * ((2*k+1 : ℕ) : ℝ) + 1)^2 / (16 * (((2*k+1 : ℕ) : ℝ)+1)) := by
  apply le_antisymm (odd_wheel_rank_upper K k hk)
  have h := grouped_asymptotic_rank_le (K := K) (wheelGroup (2*k+1))
      (wheelGroup_surj _ (by omega)) (wheelTensor K (2*k+1))
  rw [grouped_odd_wheel_eq_triangle] at h
  have hl := (triangle_asymptotic_rank_lower K (2*k) (k+1) k).trans h
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast at hl
  rw [formalOmega_swap23 K (2 * (k : ℝ)) (k : ℝ) ((k : ℝ)+1),
    wheel_rectangle_odd K _ hkR] at hl
  have he := log_of_lower _ _ hl
  push_cast
  exact he

#print axioms even_wheel_exact_exponent
#print axioms odd_wheel_exact_exponent
end
end WheelVerification
