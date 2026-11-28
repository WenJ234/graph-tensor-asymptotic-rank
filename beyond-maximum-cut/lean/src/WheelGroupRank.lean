import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import OAI.LinearAlgebra.SpectralBooks.StrassenRank
namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section
variable {I J K : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [Field K]

theorem grouped_rank_le (σ:I→J) (surj:Function.Surjective σ) (T:TensorClass.{0} I K) :
 rank (groupClass σ T) ≤ rank T := by
  apply rank_le_of_le
  have h := groupClass_mono σ (le_rank T)
  change groupClass σ T ≤ groupRingHom σ surj (rank T : TensorClass.{0} I K) at h
  simpa only [map_natCast] using h

theorem grouped_asymptotic_rank_le (σ:I→J) (surj:Function.Surjective σ) (T:TensorClass.{0} I K) :
 asymptoticRank (groupClass σ T) ≤ asymptoticRank T := by
  change asymptoticRank (groupClass σ T) ≤
    ⨅ m : ℕ, (rank (T ^ (m+1)):ℝ)^((m+1:ℝ)⁻¹)
  apply le_ciInf
  intro m
  have h : rank ((groupClass σ T)^(m+1)) ≤ rank (T^(m+1)) := by
    change rank (((groupRingHom σ surj) T)^(m+1)) ≤ _
    rw [←map_pow]
    exact grouped_rank_le σ surj _
  have inf_le : asymptoticRank (groupClass σ T) ≤
    (rank ((groupClass σ T)^(m+1)):ℝ)^((m+1:ℝ)⁻¹) := by
    unfold asymptoticRank
    apply ciInf_le _ m
    exact ⟨0,by rintro _ ⟨k,rfl⟩; positivity⟩
  exact inf_le.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by positivity))
#print axioms grouped_asymptotic_rank_le
end
end WheelVerification
