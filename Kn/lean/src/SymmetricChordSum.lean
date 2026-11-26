import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! An undirected off-diagonal sum is half the directed sum; the
    strict order simply chooses one representative of each unordered pair. -/
namespace WheelVerification
open scoped BigOperators

theorem directed_chord_sum_eq_twice {I : Type} [Fintype I] [LinearOrder I]
    (chord : I → I → Prop) [DecidableRel chord]
    (hck : ∀ x y, chord x y ↔ chord y x) (hdiag : ∀ x, ¬ chord x x)
    (d : I → I → ℝ) (hd : ∀ x y, d x y = d y x) :
    (∑ x : I, ∑ y : I, if chord x y then d x y else 0) =
      2 * ∑ x : I, ∑ y : I, if x < y ∧ chord x y then d x y else 0 := by
  classical
  let f : I → I → ℝ := fun x y => if x < y ∧ chord x y then d x y else 0
  have hf : ∀ x y, (if chord x y then d x y else 0) = f x y + f y x := by
    intro x y
    by_cases h : chord x y
    · have h' := (hck x y).mp h
      have hne : x ≠ y := by rintro rfl; exact hdiag x h
      rcases lt_or_gt_of_ne hne with hl | hr
      · simp [f, h, h', hl, not_lt_of_gt hl]
      · simp [f, h, h', hr, not_lt_of_gt hr, hd x y]
    · have h' : ¬ chord y x := fun hy => h ((hck x y).mpr hy)
      simp [f, h, h']
  simp_rw [hf, Finset.sum_add_distrib]
  change (∑ x : I, ∑ y : I, f x y) + (∑ x : I, ∑ y : I, f y x) =
    2 * ∑ x : I, ∑ y : I, f x y
  have he : (∑ x : I, ∑ y : I, f y x) = ∑ x : I, ∑ y : I, f x y := Finset.sum_comm
  rw [he, two_mul]

#print axioms directed_chord_sum_eq_twice
end WheelVerification
