import C5.SpectralUpperBridge
import ZhouCopositivity

/-! Exact C5 upper bound, with no unproved copositivity premise. -/
namespace C5Certificate
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section
variable {K : Type} [Field K]
theorem binary_cycle_upper_unconditional :
    Real.logb 2 (asymptoticRank (binaryCycle K)) ≤ (49 : ℝ) / 12 := by
  apply binary_cycle_upper
  intro φ
  intro w hw
  exact GraphTensorVerification.spectral_copositive φ w hw
#print axioms binary_cycle_upper_unconditional
end
end C5Certificate
