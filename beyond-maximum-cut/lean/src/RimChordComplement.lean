import RimChordOffsets
import Mathlib.Tactic.LinearCombination

namespace WheelVerification

/-- The directed chord test omits precisely the vertex itself and the
    two rim neighbors, including wraparound at either end. -/
theorem oddRimChord_iff_nonneighbor (k : ℕ) (hk : 1 ≤ k)
    (v w : ZMod (2*k+1)) :
    oddRimChord v w ↔ w ≠ v ∧ w ≠ v+1 ∧ v ≠ w+1 := by
  let z := w-v
  have hone : (1 : ZMod (2*k+1)).val = 1 := ZMod.val_one'' (by omega)
  have hnonzero : (1 : ZMod (2*k+1)) ≠ 0 := by
    intro H
    rw [H, ZMod.val_zero] at hone
    omega
  have hmone : (-1 : ZMod (2*k+1)).val = 2*k := by
    rw [ZMod.neg_val, ite_eq_right hnonzero, hone]
    omega
  have h0 : z.val = 0 ↔ w = v := (ZMod.val_eq_zero z).trans sub_eq_zero
  have h1 : z.val = 1 ↔ w = v+1 := by
    calc
      z.val = 1 ↔ z.val = (1 : ZMod (2*k+1)).val := by simp only [hone]
      _ ↔ z = 1 := (ZMod.val_injective (2*k+1)).eq_iff
      _ ↔ w = v+1 := by
        change w-v = 1 ↔ _
        rw [sub_eq_iff_eq_add, add_comm (1 : ZMod (2*k+1)) v]
  have hm : z.val = 2*k ↔ v = w+1 := by
    calc
      z.val = 2*k ↔ z.val = (-1 : ZMod (2*k+1)).val := by simp only [hmone]
      _ ↔ z = -1 := (ZMod.val_injective (2*k+1)).eq_iff
      _ ↔ v = w+1 := by
        change w-v = -1 ↔ _
        constructor <;> intro h <;> linear_combination -h
  have hlt := z.val_lt
  change (2 ≤ z.val ∧ z.val < 2*k) ↔ _
  simp only [Ne, ← h0, ← h1, ← hm]
  omega

#print axioms oddRimChord_iff_nonneighbor
end WheelVerification
