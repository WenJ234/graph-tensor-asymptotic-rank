import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

namespace WheelVerification
open scoped BigOperators

def oddRimChord {k : ℕ} (v w : ZMod (2*k+1)) : Prop :=
  2 ≤ (w-v).val ∧ (w-v).val < 2*k

instance {k : ℕ} : DecidableRel (@oddRimChord k) :=
  fun v w => inferInstanceAs (Decidable (2 ≤ (w-v).val ∧ (w-v).val < 2*k))

theorem oddRimChord_symm {k : ℕ} (v w : ZMod (2*k+1)) :
    oddRimChord v w ↔ oddRimChord w v := by
  have h {a b : ZMod (2*k+1)} : oddRimChord a b → oddRimChord b a := by
    intro hab
    change 2 ≤ (b-a).val ∧ (b-a).val < 2*k at hab
    have hn : b-a ≠ 0 := by
      intro hz
      have := hab.1
      rw [hz, ZMod.val_zero] at this
      omega
    change 2 ≤ (a-b).val ∧ (a-b).val < 2*k
    rw [← neg_sub, ZMod.neg_val, ite_eq_right hn]
    omega
  exact ⟨h,h⟩

theorem oddRimChord_irrefl {k : ℕ} (v : ZMod (2*k+1)) : ¬oddRimChord v v := by
  simp [oddRimChord]

theorem oddRimChord_sum_offsets (k : ℕ) (hk : 1 ≤ k)
    (v : ZMod (2*k+1)) (g : ZMod (2*k+1) → ℝ) :
    (∑ i ∈ Finset.range (2*(k-1)), g (v + (i+2 : ℕ))) =
      ∑ w : ZMod (2*k+1), if oddRimChord v w then g w else 0 := by
  rw [← Finset.sum_filter]
  have hi (i : ℕ) (hm : i ∈ Finset.range (2*(k-1))) :
      ((v + (i+2 : ℕ) - v) : ZMod (2*k+1)).val = i+2 := by
    have hs : i < 2*(k-1) := Finset.mem_range.mp hm
    rw [add_sub_cancel_left, ZMod.val_cast_of_lt (by omega)]
  refine Finset.sum_bij (fun i _ => v + (i+2 : ℕ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hm
    have hs := Finset.mem_range.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold oddRimChord
    rw [hi i hm]
    omega
  · intro i hm j hj h
    have h' := congrArg (fun w : ZMod (2*k+1) => (w-v).val) h
    rw [hi i hm, hi j hj] at h'
    omega
  · intro w hw
    have hh := (Finset.mem_filter.mp hw).2
    change 2 ≤ (w-v).val ∧ (w-v).val < 2*k at hh
    refine ⟨(w-v).val - 2, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hh.1, ZMod.natCast_zmod_val]
    abel

#print axioms oddRimChord_symm
#print axioms oddRimChord_irrefl
#print axioms oddRimChord_sum_offsets
end WheelVerification
