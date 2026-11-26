import RankPowerCore
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.StrassenRank
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import Lemmata.TensorRank.Def.Asymptotic
import Mathlib.Algebra.BigOperators.Fin

/-! Coefficient-level bridge from the fixed-format Lemmata rank to
    the OAI restriction preorder. The fixed-format and spectral-rank infima use the same powers. -/
open scoped BigOperators
open OAI.LinearAlgebra.SpectralBooks

namespace GraphTensorVerification
open SiteTensor
variable {I K : Type} [Fintype I] [Nonempty I] [Field K]
variable {A : I → Type} [∀ i, Fintype (A i)]

theorem coefficient_rank_agreement (T : (∀ i, A i) → K) :
    SiteTensor.rank (ofCoeffs T) = Lemmata.TensorRank.Tensor.rank T := by
  apply le_antisymm
  · exact SiteTensor.rank_le_of_le ((rankLE_iff_restrict_diag _ _).1
      (Lemmata.TensorRank.Tensor.rankLE_rank _))
  · exact (Lemmata.TensorRank.Tensor.rank_le_iff _ _).2
      ((rankLE_iff_restrict_diag _ _).2 (SiteTensor.le_rank _))


theorem asymptotic_rank_agreement (T : (∀ i, A i) → K) :
    SiteTensor.asymptoticRank (ofCoeffs T) = Lemmata.TensorRank.Tensor.asymptoticRank T := by
  unfold SiteTensor.asymptoticRank Lemmata.TensorRank.Tensor.asymptoticRank
    Lemmata.TensorRank.Tensor.rankRoot
  simp only [← ofCoeffs_power, coefficient_rank_agreement]

#print axioms rankLE_iff_restrict_diag
#print axioms ofCoeffs_power
#print axioms asymptotic_rank_agreement

end GraphTensorVerification
