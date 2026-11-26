import RectangleRankAgreement
import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent
import OAI.LinearAlgebra.SpectralBooks.PowerThreshold

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped NNReal
noncomputable section

private theorem width_integral (n a : ℕ) :
    OAI.LinearAlgebra.SpectralBooks.wireDimension n a = n^a := by
  unfold OAI.LinearAlgebra.SpectralBooks.wireDimension
  rw [Real.rpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast]

theorem triangle_asymptotic_rank_exact (K : Type) [Field K] (a b c : ℕ) :
    SiteTensor.asymptoticRank (triangleWires K a b c) = (2 : ℝ)^formalOmega K a c b := by
  apply le_antisymm _ (triangle_asymptotic_rank_lower K a b c)
  let T := triangleWires K a b c
  let τ := formalOmega K a c b
  change SiteTensor.asymptoticRank T ≤ (2 : ℝ)^τ
  by_contra! hbad
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hx : 0 < SiteTensor.asymptoticRank T :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) τ).trans hbad
  have hg : τ < Real.logb 2 (SiteTensor.asymptoticRank T) :=
    (Real.lt_logb_iff_rpow_lt htwo hx).2 hbad
  let ε := (Real.logb 2 (SiteTensor.asymptoticRank T) - τ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hgrowth⟩ := (formalOmega_admissible K
    (Nat.cast_nonneg a) (Nat.cast_nonneg c) (Nat.cast_nonneg b)).rank_growth ε hε
  obtain ⟨φ,hφ⟩ := exists_spectral_value_eq_asymptoticRank T
  let f := normalizedSpectrum.toRingHom φ
  have hpow (n : ℕ) (_hn : 0 < n) :
      (SiteTensor.asymptoticRank T)^n ≤ C*((2 : ℝ)^(τ+ε))^n := by
    have hz : (f T : ℝ) = SiteTensor.asymptoticRank T := hφ
    have hp := φ.property.2.2.2.2 _ _ (SiteTensor.le_rank (T^n))
    change f (T^n) ≤ f ((SiteTensor.rank (T^n) : ℕ) : TensorClass (Fin 3) K) at hp
    rw [map_pow,map_natCast] at hp
    have h₁ : ((f T : ℝ)^n) ≤ (SiteTensor.rank (T^n) : ℝ) := by exact_mod_cast hp
    rw [hz] at h₁
    change _ ≤ (SiteTensor.rank ((triangleWires K a b c)^n) : ℝ) at h₁
    rw [triangleWires_power,rectWire_rank_eq] at h₁
    have h₂ := hgrowth (2^n) (Nat.succ_le_of_lt (pow_pos (by decide) n))
    rw [width_integral (2^n) a, width_integral (2^n) c, width_integral (2^n) b] at h₂
    simp only [Nat.cast_pow, Nat.cast_ofNat] at h₂
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] at h₂
    exact h₁.trans h₂
  have hle := le_of_pow_le_const_mul_pow
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  have he := (Real.logb_le_iff_le_rpow htwo hx).2 hle
  dsimp [ε] at he
  linarith

#print axioms triangle_asymptotic_rank_exact
end
end WheelVerification
