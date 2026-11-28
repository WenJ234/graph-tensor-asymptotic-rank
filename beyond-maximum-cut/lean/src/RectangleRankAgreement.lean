import TriangleRankBridge

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

private def packFactors {a b c : ℕ} {K : Type}
    (x : Fin c × Fin a → K) (y : Fin a × Fin b → K) (z : Fin b × Fin c → K) :
    ∀ i, matrixLeg a b c i → K :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i => Fin.elim0 i)))

theorem rectWire_rank_eq (K : Type) [Field K] (a b c : ℕ) :
    SiteTensor.rank (rectWire K a b c) = tensorRank (matrixTensor K a b c) := by
  classical
  apply le_antisymm _ (matrixRank_le_rectWire_rank K a b c)
  rw [rectWire_eq_coeff]
  apply rank_le_of_le
  apply (GraphTensorVerification.rankLE_iff_restrict_diag _ _).mp
  obtain ⟨f,g,h,he⟩ := rankAtMost_tensorRank (matrixTensor K a b c)
  refine ⟨fun _ => 1, fun t => packFactors (f t) (g t) (h t),?_⟩
  funext x
  change matrixTensor K a b c (x 0) (x 1) (x 2) = _
  rw [congrFun (congrFun (congrFun he (x 0)) (x 1)) (x 2)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [one_mul,Lemmata.TensorRank.Tensor.pure,Fin.prod_univ_succ,Fin.prod_univ_zero,
    OAI.MatrixMultiplication.Foundation.Tensor.rankOne,mul_one]
  change f t (x 0) * g t (x 1) * h t (x 2) =
    f t (x 0) * (g t (x 1) * h t (x 2))
  exact mul_assoc _ _ _

#print axioms rectWire_rank_eq
end
end WheelVerification
