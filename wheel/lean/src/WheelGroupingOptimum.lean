import RectangleNormalization
import WheelConsequences

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section

def threeGroupExponent (K : Type) [Field K] (r : ℕ) [NeZero r]
    (σ : Option (ZMod r) → Fin 3) : ℝ :=
  Real.logb 2 (SiteTensor.asymptoticRank (groupClass σ (wheelTensor K r)))

private theorem threeGroupExponent_eq (K : Type) [Field K] (r : ℕ) [NeZero r]
    (σ : Option (ZMod r) → Fin 3) :
    threeGroupExponent K r σ =
    formalOmega K (wheelBetween σ 0 1) (wheelBetween σ 2 1) (wheelBetween σ 2 0) := by
  rw [threeGroupExponent,grouped_wheel_arbitrary,triangle_asymptotic_rank_exact,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]

theorem wheel_parity_grouping_isGreatest (K : Type) [Field K] (r : ℕ) [NeZero r] (hr : 3 ≤ r) :
    IsGreatest {x : ℝ | ∃ σ : Option (ZMod r) → Fin 3, Function.Surjective σ ∧
      x = threeGroupExponent K r σ} (threeGroupExponent K r (wheelGroup r)) := by
  constructor
  · exact ⟨wheelGroup r,wheelGroup_surj r (by omega),rfl⟩
  · rintro _ ⟨σ,hs,rfl⟩
    rw [threeGroupExponent_eq]
    have hu := arbitrary_three_block_lower K r σ hs
    have he : threeGroupExponent K r (wheelGroup r) =
        Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K r)) := by
      have splitR : (∃ k : ℕ, r = 2*k ∧ 2 ≤ k) ∨
          (∃ k : ℕ, r = 2*k+1 ∧ 1 ≤ k) := by
        rcases (show r = 2*(r/2) ∨ r = 2*(r/2)+1 by omega) with h|h
        · exact Or.inl ⟨r/2,h,by omega⟩
        · exact Or.inr ⟨r/2,h,by omega⟩
      rcases splitR with ⟨k,rfl,hk⟩|⟨k,rfl,hk⟩
      · rw [threeGroupExponent, grouped_even_wheel_eq_triangle,
          triangle_asymptotic_rank_exact,
          Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
          even_wheel_exact_exponent K k hk]
        push_cast
        exact wheel_rectangle_even K k (by exact_mod_cast (show 0 < k by omega))
      · rw [threeGroupExponent, grouped_odd_wheel_eq_triangle,
          triangle_asymptotic_rank_exact,
          Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1),
          odd_wheel_exact_exponent K k hk]
        push_cast
        rw [formalOmega_swap23]
        exact wheel_rectangle_odd K k (by exact_mod_cast hk)
    rwa [he]

#print axioms wheel_parity_grouping_isGreatest
end
end WheelVerification
