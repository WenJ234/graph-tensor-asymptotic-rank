import BorderPowerSpan
import OddCliqueFiniteRank
import Lemmata.TensorRank.Proof.Growth
import Lemmata.TensorRank.Proof.GraphRank

/-! Border-rank lower bound for the published K5 theorem, formulated for the
usual affine Zariski closure of the set of tensors of ordinary rank at most r. -/
namespace OddCliquePaper
open Lemmata.TensorRank Lemmata.TensorRank.Tensor
noncomputable section

theorem asymptoticRank_le_of_borderRankAtMost {F I : Type*} [Field F]
    [Fintype I] [DecidableEq I] {V : I → Type*} [∀ i, Fintype (V i)]
    (T : Tensor F I V) (r : ℕ)
    (h : InAffineZariskiClosure {X : Tensor F I V | rank X ≤ r} T) :
    asymptoticRank T ≤ (r : ℝ) := by
  apply asymptoticRank_le_of_polynomial_power_bound T 1 (r : ℝ) (by norm_num)
    (Nat.cast_nonneg _) (Fintype.card (∀ i, V i))
  intro n hn
  have hb := rank_power_le_of_zariski n r T h
  exact_mod_cast (by simpa only [one_mul] using hb :
    rank (power T n) ≤ 1 * (n+1)^Fintype.card (∀ i, V i) * r^n)

theorem k5_asymptoticRank_all_q (F : Type) [Field F] (q : ℕ) (hq : 2 ≤ q) :
    asymptoticRank (completeGraph (𝕜 := F) 5 q) = (q : ℝ)^((25 : ℝ)/4) := by
  apply le_antisymm
  · convert (completeGraphBounds (𝕜 := F) 5 q (by decide) (by omega)).2.1 using 1
    norm_num
  · unfold asymptoticRank
    apply le_ciInf
    intro n
    have hqn : 2 ≤ q^(n+1) := hq.trans (le_self_pow (by omega) (by omega))
    have hr := k5_ordinary_rank_lower F (q^(n+1)) hqn
    rw [rank_completeGraph_power] at hr
    have hb := (Nat.ceil_le.mp hr)
    unfold rankRoot
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (show 0 < (n : ℝ) + 1 by positivity)).mpr
    rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (by positivity : (0 : ℝ) ≤ q)]
    simpa only [Nat.cast_pow] using hb

theorem k5_border_rank_lower (q r : ℕ) (hq : 2 ≤ q)
    (h : InAffineZariskiClosure
      {X | rank X ≤ r} (completeGraph (𝕜 := ℂ) 5 q)) :
    ⌈(q : ℝ)^((25 : ℝ)/4)⌉₊ ≤ r := by
  apply Nat.ceil_le.mpr
  rw [← k5_asymptoticRank_all_q ℂ q hq]
  exact asymptoticRank_le_of_borderRankAtMost _ _ h

#print axioms k5_border_rank_lower
end
end OddCliquePaper
