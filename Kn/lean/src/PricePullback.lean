import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

/-! At a pulled-back spectral point, the price of a source wire is the
target price between its two images, including coinciding images. -/
namespace GraphTensorVerification
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
variable {K : Type*} [Field K]

theorem pullback_wire_distance
 (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
 (f : I → J) (hf : Function.Surjective f) (c : ℝ) (u v : I) :
 rawWireDistance (groupSpectralPoint f hf φ) c u v =
 rawWireDistance φ c (f u) (f v) := by
  have heq : (f ∘ (![u,v] : Fin 2 → I)) = (![f u,f v] : Fin 2 → J) := by
    funext x
    fin_cases x <;> rfl
  unfold rawWireDistance rawLogPrice
  change c * Real.logb 2 (φ.val
    (ofRaw (((Raw.diagonal (Fin 2) K (Fin 2)).group ![u,v]).group f)) : ℝ)
    = c * Real.logb 2 (φ.val
    (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![f u,f v])) : ℝ)
  rw [ofRaw_eq_iff.mpr ((Raw.diagonal (Fin 2) K (Fin 2)).group_group_equivalent
    (![u,v] : Fin 2 → I) f), heq]

#print axioms pullback_wire_distance
end
end GraphTensorVerification
