import WheelGroup
import WheelArithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

namespace WheelVerification
open scoped BigOperators

def spokesCut (r : ℕ) [NeZero r] (f : ZMod r → Bool) : ℕ :=
  ∑ v : ZMod r, if f v then 1 else 0

def rimCut (r : ℕ) [NeZero r] (f : ZMod r → Bool) : ℕ :=
  ∑ v : ZMod r, if f v ≠ f (v+1) then 1 else 0

def wheelCutSize (r : ℕ) [NeZero r] (f : ZMod r → Bool) : ℕ := spokesCut r f + rimCut r f

theorem wheel_cut_upper (r : ℕ) [NeZero r] (f : ZMod r → Bool) :
    wheelCutSize r f ≤ (3*r)/2 := by
  let s := spokesCut r f
  let c (v : ZMod r) : ℕ := if f v then 1 else 0
  let d (v : ZMod r) : ℕ := if f v then 0 else 1
  have hsum : (∑ v, c v) + ∑ v, d v = r := by
    rw [←Finset.sum_add_distrib]
    have h (v : ZMod r) : c v + d v = 1 := by
      unfold c d
      cases f v <;> simp
    simp [h,ZMod.card]
  have hsb : s ≤ r := by
    change s + _ = _ at hsum
    omega
  have hrim (u : ZMod r → ℕ)
      (hu : ∀ v, (if f v ≠ f (v+1) then 1 else (0:ℕ)) ≤ u v + u (v+1)) :
      rimCut r f ≤ 2 * ∑ v, u v := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod r))) fun v _ => hu v
    have ht : (∑ v : ZMod r, u (v+1)) = ∑ v : ZMod r, u v :=
      Fintype.sum_equiv (Equiv.addRight (1 : ZMod r)) _ _ (fun _ => rfl)
    simpa only [rimCut, Finset.sum_add_distrib, ht, two_mul] using h
  have hc := hrim c (fun v => by unfold c; cases f v <;> cases f (v+1) <;> decide)
  have hd := hrim d (fun v => by unfold d; cases f v <;> cases f (v+1) <;> decide)
  have h : rimCut r f ≤ 2 * min s (r-s) := by
    change s + _ = _ at hsum
    change rimCut r f ≤ 2*s at hc
    by_cases hs : s ≤ r-s
    · rwa [Nat.min_eq_left hs]
    · rw [Nat.min_eq_right (by omega)]
      omega
  change s + rimCut r f ≤ _
  exact (Nat.add_le_add_left h s).trans (cut_upper r s hsb)

private theorem sum_val (f : ℕ → ℕ) (r : ℕ) [NeZero r] :
    (∑ v : ZMod r, f v.val) = ∑ i ∈ Finset.range r, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv r).symm.toEquiv
  intro v
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

def parityCut (r : ℕ) (v : ZMod r) : Bool := decide (v.val%2 = 0)

theorem parity_spokes (r : ℕ) [NeZero r] :
    spokesCut r (parityCut r) = spokeClass r 0 := by
  unfold spokesCut spokeClass parityCut
  simpa only [decide_eq_true_eq] using sum_val (fun i => if i%2=0 then 1 else 0) r

theorem parity_rim (r : ℕ) [NeZero r] :
    rimCut r (parityCut r) = crossRim r := by
  unfold rimCut crossRim parityCut
  simp_rw [rim_val_next r]
  have h (a b : ℕ) : (decide (a%2=0) ≠ decide (b%2=0)) ↔ a%2 ≠ b%2 := by
    have ha : a%2=0 ∨ a%2=1 := by omega
    have hb : b%2=0 ∨ b%2=1 := by omega
    rcases ha with ha|ha <;> rcases hb with hb|hb <;> simp [ha,hb]
  simp_rw [h]
  exact sum_val (fun i => if i%2 ≠ rimNext' r i%2 then 1 else 0) r

theorem wheel_parity_cut_size (r : ℕ) [NeZero r] :
    wheelCutSize r (parityCut r) = (3*r)/2 := by
  simp only [wheelCutSize, parity_spokes, parity_rim]
  have hr : r = 2*(r/2) ∨ r = 2*(r/2)+1 := by omega
  rcases hr with h|h
  · let k := r/2
    have he : r = 2*k := h
    rw [he, spokeClass_even k 0 (by omega), crossRim_even]
    omega
  · let k := r/2
    have he : r = 2*k+1 := h
    rw [he, spokeClass_odd_zero, crossRim_odd]
    omega

theorem wheel_cut_exact (r : ℕ) [NeZero r] :
    IsGreatest (Set.range (wheelCutSize r)) ((3*r)/2) := by
  constructor
  · exact ⟨parityCut r,wheel_parity_cut_size r⟩
  · intro n hn
    obtain ⟨f,rfl⟩ := hn
    exact wheel_cut_upper r f

#print axioms wheel_cut_upper
#print axioms wheel_cut_exact
end WheelVerification
