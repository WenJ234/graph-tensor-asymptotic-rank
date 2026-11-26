import OddCliqueGroupDim
import OddCliqueExact
import TriangleRankBridge

/-! The ordinary finite rank lower bound for the exact graph tensor of the paper. -/
namespace OddCliquePaper
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification WheelVerification
noncomputable section

theorem k5_ordinary_rank_lower (K : Type) [Field K] (q : ℕ) (hq : 2 ≤ q) :
    ⌈(q : ℝ)^((25 : ℝ)/4)⌉₊ ≤
      Lemmata.TensorRank.Tensor.rank (Lemmata.TensorRank.completeGraph (𝕜 := K) 5 q) := by
  letI : NeZero q := ⟨by omega⟩
  let T := Lemmata.TensorRank.completeGraph (𝕜 := K) 5 q
  apply Nat.ceil_le.mpr
  change _ ≤ (Lemmata.TensorRank.Tensor.rank T : ℝ)
  rw [← coefficient_rank_agreement]
  let col := balancedColor 2
  have hg := grouped_rank_le (K := K) col (balancedColor_surjective (m := 2) (by decide)) (ofCoeffs T)
  have hrect : groupClass col (ofCoeffs T) = rectWire K (q^4) (q^2) (q^2) := by
    change groupClass (balancedColor 2) (ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) (2*2+1) q)) = _
    rw [grouped_clique_eq_rectangle,
      pairCount_eq_product _ 0 1 (by decide),
      pairCount_eq_product _ 2 0 (by decide),
      pairCount_eq_product _ 2 1 (by decide),
      balanced_color0_card, balanced_color1_card, balanced_color2_card]
  rw [hrect] at hg
  have hp : formalOmega K 4 2 2 = 25/4 := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num, show (2*(2 : ℝ)+1)^2 = 25 by norm_num]
      using odd_clique_rectangle_value K 2 (by norm_num)
  have ha := integral_rectangular_rank_lower K hq 4 2 2
  push_cast at ha
  rw [hp] at ha
  exact ha.trans (Nat.cast_le.mpr ((matrixRank_le_rectWire_rank K (q^4) (q^2) (q^2)).trans hg))

#print axioms k5_ordinary_rank_lower
end
end OddCliquePaper
