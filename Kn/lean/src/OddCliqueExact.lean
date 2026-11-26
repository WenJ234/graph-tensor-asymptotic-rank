import OddCliquePartition
import OddCliqueRectangle
import TriangleRankBridge
import WheelGroupRank
import RankPowerModels
import Lemmata.TensorRank.Main

namespace OddCliquePaper
open OAI OAI.LinearAlgebra.SpectralBooks
open GraphTensorVerification WheelVerification
noncomputable section

theorem odd_complete_exact_exponent (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) :
    Real.logb 2 (Lemmata.TensorRank.Tensor.asymptoticRank
      (Lemmata.TensorRank.completeGraph (𝕜 := K) (2*m+1) 2)) =
      ((2*m+1 : ℕ) : ℝ)^2/4 := by
  let T := Lemmata.TensorRank.completeGraph (𝕜 := K) (2*m+1) 2
  change Real.logb 2 (Lemmata.TensorRank.Tensor.asymptoticRank T) = _
  have h := grouped_asymptotic_rank_le (K := K) (balancedColor m)
    (balancedColor_surjective hm) (SiteTensor.ofCoeffs T)
  change SiteTensor.asymptoticRank (SiteTensor.groupClass (balancedColor m)
    (SiteTensor.ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) (2*m+1) 2))) ≤ _ at h
  rw [grouped_balanced_clique,asymptotic_rank_agreement] at h
  have hl := (triangle_asymptotic_rank_lower K (m^2) m m).trans h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Nat.cast_pow, odd_clique_rectangle_value K m hmR] at hl
  push_cast
  push_cast at hl
  have hu : Lemmata.TensorRank.Tensor.asymptoticRank T ≤
      (2 : ℝ)^(((2*m+1 : ℕ) : ℝ)^2/4) :=
    (Lemmata.TensorRank.completeGraphBounds (𝕜 := K) (2*m+1) 2 (by omega) (by decide)).2.1
  push_cast at hu
  have he : Lemmata.TensorRank.Tensor.asymptoticRank T =
      (2 : ℝ)^((2*(m : ℝ)+1)^2/4) := le_antisymm hu hl
  rw [he,Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]

#print axioms odd_complete_exact_exponent
end
end OddCliquePaper
