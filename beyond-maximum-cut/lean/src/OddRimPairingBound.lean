import RimOffsetSum
import RimChordOffsets
import RimReindex
import SymmetricChordSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace WheelVerification
open scoped BigOperators

/-- Summing the actual odd rim triangle rows. Each rim edge is visited
    once per offset pair, and each unordered chord twice in total. -/
theorem odd_rim_pairing_bound (k : ℕ) (hk : 1 ≤ k)
    [LinearOrder (ZMod (2*k+1))]
    (d : ZMod (2*k+1) → ZMod (2*k+1) → ℝ)
    (hs : ∀ v w, d v w = d w v)
    (ht : ∀ v a b, d a b ≤ d v a + d v b) :
    ((k-1 : ℕ) : ℝ) * (∑ v : ZMod (2*k+1), d v (v+1)) ≤
    2 * ∑ v : ZMod (2*k+1), ∑ w : ZMod (2*k+1),
      if v < w ∧ oddRimChord v w then d v w else 0 := by
  have hb :
      (∑ j ∈ Finset.range (k-1), ∑ v : ZMod (2*k+1),
        d (v + (2*(j+1) : ℕ)) (v + (2*(j+1) : ℕ) + 1)) ≤
      ∑ j ∈ Finset.range (k-1), ∑ v : ZMod (2*k+1),
        (d v (v + (2*(j+1) : ℕ)) + d v (v + (2*(j+1)+1 : ℕ))) := by
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro v _
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      ht v (v + (2*(j+1) : ℕ)) (v + (2*(j+1) : ℕ) + 1)
  rw [paired_rim_left_sum, paired_rim_right_sum] at hb
  simp_rw [oddRimChord_sum_offsets k hk] at hb
  rwa [directed_chord_sum_eq_twice oddRimChord oddRimChord_symm oddRimChord_irrefl d hs] at hb

#print axioms odd_rim_pairing_bound
end WheelVerification
