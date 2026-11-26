import WheelMetricTriple
import RimReindex
import OddRimAllPairs
import OddUpperFinish
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WheelVerification
open scoped BigOperators
noncomputable section

def WheelCopositive {I : Type} [Fintype I] (d : I → I → ℝ) : Prop :=
  ∀ u : I → ℝ, (∀ i, 0 ≤ u i) → 0 ≤ ∑ i, ∑ j, u i*(1-2*d i j)*u j

theorem wheel_cp_upper_even_or_odd (r : ℕ) [NeZero r]
    (d : Option (ZMod r) → Option (ZMod r) → ℝ)
    (hs : ∀ i j, d i j = d j i) (hz : ∀ i, d i i = 0)
    (hcp : WheelCopositive d) :
    (∑ v : ZMod r, d (some v) (some (v+1))) +
      (∑ v : ZMod r, d none (some v)) ≤ 25*(r : ℝ)/16 := by
  let rim (v : ZMod r) := d (some v) (some (v+1))
  let spoke (v : ZMod r) := d none (some v)
  have hrow (v : ZMod r) : 4*rim v + 2*spoke v + 2*spoke (v+1) ≤ 25/4 := by
    let a : Option (ZMod r) := some v
    let b : Option (ZMod r) := some (v+1)
    exact triple_weight_row d a b none hs hz
      (hcp _ (tripleWeight_nonneg a b none))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod r)))
    (fun v _ => hrow v)
  have htrans : (∑ v : ZMod r, spoke (v+1)) = ∑ v : ZMod r, spoke v :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod r)) _ _ (fun _ => rfl)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, htrans, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul] at hsum
  change (∑ v : ZMod r, rim v) + (∑ v : ZMod r, spoke v) ≤ _
  linarith only [hsum]

theorem wheel_cp_upper_odd (k : ℕ) (hk : 1 ≤ k)
    (d : Option (ZMod (2*k+1)) → Option (ZMod (2*k+1)) → ℝ)
    (hs : ∀ i j, d i j = d j i) (hz : ∀ i, d i i = 0)
    (ht : ∀ i j v, d i v ≤ d i j + d j v)
    (hcp : WheelCopositive d) :
    (∑ v : ZMod (2*k+1), d (some v) (some (v+1))) +
      (∑ v : ZMod (2*k+1), d none (some v)) ≤
      (5 * ((2*k+1 : ℕ) : ℝ) + 1)^2 / (16 * (((2*k+1 : ℕ) : ℝ)+1)) := by
  let R := ZMod (2*k+1)
  letI : LinearOrder R := LinearOrder.lift' ZMod.val (ZMod.val_injective _)
  let r : ℝ := (2*k+1 : ℕ)
  let L : ℝ := ∑ v : R, d (some v) (some (v+1))
  let S : ℝ := ∑ v : R, d none (some v)
  let D : ℝ := (∑ v : R, ∑ w : R, d (some v) (some w)) / 2
  let t : ℝ := (r+1)/4
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
      exact by simp [hz]
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
  have hc := hcp (HubWeight t) hw
  have hhub := hub_weight_row d t hs (hz none) hc
  have hcard : (Fintype.card R : ℝ) = r := by
    change (Fintype.card (ZMod (2*k+1)) : ℝ) = _
    rw [ZMod.card]
  rw [hcard] at hhub
  have hcpFinal : 4*(D + ((r+1)/4)*S) ≤ (r+(r+1)/4)^2 := by
    change 2*(∑ v : R, ∑ w : R, d (some v) (some w)) + 4*t*S ≤ (r+t)^2 at hhub
    dsimp only [D,t] at *
    linarith only [hhub]
  exact odd_wheel_upper_of_pairing_and_cp r L S D hr hpair hcpFinal

#print axioms wheel_cp_upper_even_or_odd
#print axioms wheel_cp_upper_odd
end
end WheelVerification
