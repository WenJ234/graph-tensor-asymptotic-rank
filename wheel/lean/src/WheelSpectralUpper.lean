import WheelMetricCP
import OddRimAllPairs
import OddUpperFinish
import ZhouCopositivity

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

/-- The odd-wheel price bound on a genuine normalized tensor spectral point,
    not on a distance matrix carrying an assumed copositivity row. -/
theorem odd_wheel_spectral_upper (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k)
    (φ : normalizedSpectrum ((· ≤ ·) :
      TensorClass.{0} (Option (ZMod (2*k+1))) K → _ → Prop)) :
    (∑ v : ZMod (2*k+1), rawWireDistance φ 1 (some v) (some (v+1))) +
      (∑ v : ZMod (2*k+1), rawWireDistance φ 1 none (some v)) ≤
      (5 * ((2*k+1 : ℕ) : ℝ) + 1)^2 / (16 * (((2*k+1 : ℕ) : ℝ)+1)) := by
  let R := ZMod (2*k+1)
  letI : LinearOrder R := LinearOrder.lift' ZMod.val (ZMod.val_injective _)
  let d := rawWireDistance φ 1
  let r : ℝ := (2*k+1 : ℕ)
  let L : ℝ := ∑ v : R, d (some v) (some (v+1))
  let S : ℝ := ∑ v : R, d none (some v)
  let D : ℝ := (∑ v : R, ∑ w : R, d (some v) (some w)) / 2
  let t : ℝ := (r+1)/4
  have hz := rawWireDistance_self φ 1 zero_le_one
  have hs := rawWireDistance_symm φ 1
  have ht := rawWireDistance_triangle φ 1 zero_le_one
  have hp := odd_rim_all_pairs_bound k hk (fun v w => d (some v) (some w))
    (fun v w => hs _ _) (fun v a b => by
      simpa only [hs (some a) (some v)] using ht (some a) (some v) (some b))
  have hsum : (∑ v : R, ∑ w : R, if w ≠ v then d (some v) (some w) else 0) =
      ∑ v : R, ∑ w : R, d (some v) (some w) := by
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    by_cases he : w = v
    · subst w
      exact by simp [d]
    · exact ite_eq_left he
  rw [hsum] at hp
  have hpair : (r+1)*L ≤ 4*D := by
    dsimp only [r,L,D]
    linarith only [hp]
  have hr : 0 < r+1 := by positivity
  have hw (i : Option R) : 0 ≤ HubWeight t i := by
    cases i
    · exact div_nonneg hr.le (by norm_num)
    · exact zero_le_one
  have hc := GraphTensorVerification.spectral_copositive φ (HubWeight t) hw
  have hcp := hub_weight_row d t hs (hz none) hc
  have hcard : (Fintype.card R : ℝ) = r := by
    change (Fintype.card (ZMod (2*k+1)) : ℝ) = _
    rw [ZMod.card]
  rw [hcard] at hcp
  have hcpFinal : 4*(D + ((r+1)/4)*S) ≤ (r+(r+1)/4)^2 := by
    change 2*(∑ v : R, ∑ w : R, d (some v) (some w)) + 4*t*S ≤ (r+t)^2 at hcp
    dsimp only [D,t] at *
    linarith only [hcp]
  exact odd_wheel_upper_of_pairing_and_cp r L S D hr hpair hcpFinal

#print axioms odd_wheel_spectral_upper
end
end WheelVerification
