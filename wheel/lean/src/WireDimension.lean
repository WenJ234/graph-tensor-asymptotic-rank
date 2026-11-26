import WheelTensorRankUpper
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section

def wireDimension {I : Type} [Fintype I] [Nonempty I] (K : Type) [Field K] (u v : I) (n : ℕ) :
    TensorClass.{0} I K := ofRaw ((Raw.diagonal (Fin 2) K (Fin n)).group ![u,v])

theorem wireDimension_groupNat {I : Type} [Fintype I] [Nonempty I] (K : Type) [Field K]
    (u v : I) (n : ℕ) : wireDimension K u v n =
      groupMulHom (![u,v] : Fin 2 → I) (n : TensorClass.{0} (Fin 2) K) := by
  rw [← ofRaw_diagonal_fin_eq_natCast (Fin 2) K n]
  rfl

theorem wireDimension_pow {I : Type} [Fintype I] [Nonempty I] (K : Type) [Field K]
    (u v : I) (n k : ℕ) :
    wireDimension K u v n ^ k = wireDimension K u v (n^k) := by
  rw [wireDimension_groupNat, wireDimension_groupNat, Nat.cast_pow, map_pow]

theorem wireAt_pow_dimension {I : Type} [Fintype I] [Nonempty I] (K : Type) [Field K]
    (u v : I) (k : ℕ) : wireAt K u v ^ k = wireDimension K u v (2^k) :=
  wireDimension_pow K u v 2 k

#print axioms wireAt_pow_dimension
end
end WheelVerification
