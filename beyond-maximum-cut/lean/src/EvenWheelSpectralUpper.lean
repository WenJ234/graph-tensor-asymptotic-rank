import WheelMetricTriple
import RimReindex
import ZhouCopositivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

/-- The rim-row bound on actual normalized tensor spectral points.
    The algebraic upper bound itself is valid on odd rims too. -/
theorem wheel_spectral_upper_by_rim_rows (K : Type) [Field K] (r : ℕ) [NeZero r]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option (ZMod r)) K → _ → Prop)) :
    (∑ v : ZMod r, rawWireDistance φ 1 (some v) (some (v+1))) +
      (∑ v : ZMod r, rawWireDistance φ 1 none (some v)) ≤ 25*(r : ℝ)/16 := by
  let d := rawWireDistance φ 1
  let rim (v : ZMod r) := d (some v) (some (v+1))
  let spoke (v : ZMod r) := d none (some v)
  have hrow (v : ZMod r) : 4*rim v + 2*spoke v + 2*spoke (v+1) ≤ 25/4 := by
    let a : Option (ZMod r) := some v
    let b : Option (ZMod r) := some (v+1)
    exact triple_weight_row d a b none (rawWireDistance_symm φ 1)
      (rawWireDistance_self φ 1 zero_le_one)
      (GraphTensorVerification.spectral_copositive φ _ (tripleWeight_nonneg a b none))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod r)))
    (fun v _ => hrow v)
  have htrans : (∑ v : ZMod r, spoke (v+1)) = ∑ v : ZMod r, spoke v :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod r)) _ _ (fun _ => rfl)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, htrans, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul] at hsum
  change (∑ v : ZMod r, rim v) + (∑ v : ZMod r, spoke v) ≤ _
  linarith only [hsum]

#print axioms wheel_spectral_upper_by_rim_rows
end
end WheelVerification
