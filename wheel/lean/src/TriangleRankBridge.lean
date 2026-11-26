import TriangleWireCoordinates
import IntegralRectangleRank
import WheelGroupedCounts
import WheelRectangle

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

private def packInputs {a b c : ℕ} (x : Fin c × Fin a) (y : Fin a × Fin b) (z : Fin b × Fin c) :
    ∀ i, matrixLeg a b c i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i => Fin.elim0 i)))

theorem matrixRank_le_rectWire_rank (K : Type) [Field K] (a b c : ℕ) :
    tensorRank (matrixTensor K a b c) ≤ SiteTensor.rank (rectWire K a b c) := by
  classical
  rw [rectWire_eq_coeff]
  apply tensorRank_le_of_rankAtMost
  let r := SiteTensor.rank (ofCoeffs (matrixCoeff K a b c))
  have hr : Lemmata.TensorRank.Tensor.RankLE (matrixCoeff K a b c) r :=
    (GraphTensorVerification.rankLE_iff_restrict_diag _ _).mpr (SiteTensor.le_rank _)
  obtain ⟨p, f, hf⟩ := hr
  refine ⟨fun t x => p t * f t 0 x, fun t y => f t 1 y, fun t z => f t 2 z, ?_⟩
  funext x y z
  have h := congrFun hf (packInputs x y z)
  change matrixTensor K a b c x y z = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Lemmata.TensorRank.Tensor.pure, Fin.prod_univ_succ, Fin.prod_univ_zero,
    OAI.MatrixMultiplication.Foundation.Tensor.rankOne, mul_one]
  change p t * (f t 0 x * (f t 1 y * f t 2 z)) = _
  ring

theorem triangleWires_power (K : Type) [Field K] (a b c k : ℕ) :
    (triangleWires K a b c)^k = rectWire K ((2^k)^a) ((2^k)^c) ((2^k)^b) := by
  simp only [triangleWires,rectWire,mul_pow, wireAt_pow_dimension, wireDimension_pow, ← pow_mul, Nat.mul_comm]

theorem triangle_asymptotic_rank_lower (K : Type) [Field K] (a b c : ℕ) :
    (2 : ℝ) ^ formalOmega K a c b ≤ SiteTensor.asymptoticRank (triangleWires K a b c) := by
  unfold SiteTensor.asymptoticRank
  apply le_ciInf
  intro k
  rw [triangleWires_power]
  let n : ℕ := 2^(k+1)
  have hn : 2 ≤ n := by
    dsimp [n]
    exact le_self_pow (by omega) (by omega)
  have hl := integral_rectangular_rank_lower K hn a c b
  have hr := matrixRank_le_rectWire_rank K (n^a) (n^c) (n^b)
  have hv : (n : ℝ)^(formalOmega K a c b) ≤
      (SiteTensor.rank (rectWire K (n^a) (n^c) (n^b)) : ℝ) := hl.trans (Nat.cast_le.mpr hr)
  have npos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have rankpos := (Real.rpow_pos_of_pos npos (formalOmega K a c b)).trans_le hv
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) rankpos.le
    (show 0 < (k : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [n, Nat.cast_pow, Nat.cast_ofNat] using hv

#print axioms triangle_asymptotic_rank_lower
end
end WheelVerification
