import OddRimPairingBound
import RimChordComplement
import OddUpperFinish

namespace WheelVerification
open scoped BigOperators

/-- D is the unordered all-rim pair sum, expressed as half the ordered
    off-diagonal sum. This proves the paper's actual inequality (4D ≥ (r+1)L). -/
theorem odd_rim_all_pairs_bound (k : ℕ) (hk : 1 ≤ k)
    [LinearOrder (ZMod (2*k+1))]
    (d : ZMod (2*k+1) → ZMod (2*k+1) → ℝ)
    (hs : ∀ v w, d v w = d w v)
    (ht : ∀ v a b, d a b ≤ d v a + d v b) :
    ((2*k+1 : ℕ) + 1 : ℝ) * (∑ v : ZMod (2*k+1), d v (v+1)) ≤
    2 * (∑ v : ZMod (2*k+1), ∑ w : ZMod (2*k+1), if w ≠ v then d v w else 0) := by
  classical
  let I := ZMod (2*k+1)
  have hne : (1 : I) ≠ 0 := by
    intro h
    have hv : (1 : I).val = 1 := ZMod.val_one'' (by omega)
    rw [h, ZMod.val_zero] at hv
    omega
  have htwo : (2 : I) ≠ 0 := by
    intro h
    have hv : (2 : I).val = 2 := ZMod.val_natCast_of_lt (by omega : 2 < 2*k+1)
    rw [h, ZMod.val_zero] at hv
    omega
  have split (v w : I) : (if w ≠ v then d v w else 0) =
      (if w = v+1 then d v w else 0) +
      (if v = w+1 then d v w else 0) +
      (if oddRimChord v w then d v w else 0) := by
    by_cases h0 : w = v
    · subst w
      have hh : v ≠ v+1 := by
        intro h
        apply hne
        exact add_left_cancel (h.symm.trans (add_zero v).symm)
      simp [hh, oddRimChord_irrefl]
    · by_cases h1 : w = v+1
      · have h2 : v ≠ w+1 := by
          intro h
          apply htwo
          have hh : v+(1+1) = v+0 := by rw [← add_assoc, ← h1, ← h, add_zero]
          exact (one_add_one_eq_two (R := I)).symm.trans (add_left_cancel hh)
        have hc : ¬oddRimChord v w := fun h => ((oddRimChord_iff_nonneighbor k hk v w).mp h).2.1 h1
        simp only [ite_eq_left h0, ite_eq_left h1, ite_eq_right h2, ite_eq_right hc, add_zero]
      · by_cases h2 : v = w+1
        · have hc : ¬oddRimChord v w := fun h => ((oddRimChord_iff_nonneighbor k hk v w).mp h).2.2 h2
          simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_left h2, ite_eq_right hc, zero_add, add_zero]
        · have hc := (oddRimChord_iff_nonneighbor k hk v w).mpr ⟨h0,h1,h2⟩
          simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left hc, zero_add]
  have hsum :
      (∑ v : I, ∑ w : I, if w ≠ v then d v w else 0) =
      2*(∑ v : I, d v (v+1)) +
        ∑ v : I, ∑ w : I, if oddRimChord v w then d v w else 0 := by
    simp_rw [split, Finset.sum_add_distrib]
    have hb : (∑ v : I, ∑ w : I, if v = w+1 then d v w else 0) =
        ∑ v : I, d v (v+1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      calc
        (∑ w : I, if w = v+1 then d w v else 0) = d (v+1) v :=
          Fintype.sum_ite_eq' (v+1) (fun w => d w v)
        _ = d v (v+1) := hs _ _
    have ha : (∑ v : I, ∑ w : I, if w = v+1 then d v w else 0) =
        ∑ v : I, d v (v+1) := by
      apply Finset.sum_congr rfl
      intro v _
      exact Fintype.sum_ite_eq' (v+1) (d v)
    rw [ha,hb]
    ring
  have hp := odd_rim_pairing_bound k hk d hs ht
  rw [← directed_chord_sum_eq_twice oddRimChord oddRimChord_symm oddRimChord_irrefl d hs] at hp
  change ((2*k+1 : ℕ) + 1 : ℝ) * (∑ v : I, d v (v+1)) ≤ _
  rw [hsum]
  have hcast : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub hk : ((k-1 : ℕ) : ℝ) = _)
  rw [hcast] at hp
  push_cast
  nlinarith only [hp]

#print axioms odd_rim_all_pairs_bound
end WheelVerification
