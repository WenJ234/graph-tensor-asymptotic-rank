import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The pointwise real projection bound used in Proposition 4. -/
namespace OddCliquePaper
open scoped BigOperators

private def doubleGap (x : Fin 5 → ℝ) : ℝ := ∑ i, ∑ j, |x i - x j|

private theorem doubleGap_perm (x : Fin 5 → ℝ) (p : Equiv.Perm (Fin 5)) :
    doubleGap (x ∘ p) = doubleGap x := by
  unfold doubleGap
  simp only [Function.comp_apply]
  calc
    (∑ i, ∑ j, |x (p i) - x (p j)|) = ∑ i, ∑ j, |x (p i) - x j| :=
      Finset.sum_congr rfl (fun i _ => Equiv.sum_comp p (fun j : Fin 5 => |x (p i) - x j|))
    _ = _ := Equiv.sum_comp p (fun i : Fin 5 => ∑ j : Fin 5, |x i - x j|)

private theorem doubleGap_sorted (x : Fin 5 → ℝ) (h : Monotone x) :
    doubleGap x = 8*(x 4-x 0) + 4*(x 3-x 1) := by
  have h01 : x 0 ≤ x 1 := h (by decide : (0 : Fin 5) ≤ 1)
  have h02 : x 0 ≤ x 2 := h (by decide : (0 : Fin 5) ≤ 2)
  have h03 : x 0 ≤ x 3 := h (by decide : (0 : Fin 5) ≤ 3)
  have h04 : x 0 ≤ x 4 := h (by decide : (0 : Fin 5) ≤ 4)
  have h12 : x 1 ≤ x 2 := h (by decide : (1 : Fin 5) ≤ 2)
  have h13 : x 1 ≤ x 3 := h (by decide : (1 : Fin 5) ≤ 3)
  have h14 : x 1 ≤ x 4 := h (by decide : (1 : Fin 5) ≤ 4)
  have h23 : x 2 ≤ x 3 := h (by decide : (2 : Fin 5) ≤ 3)
  have h24 : x 2 ≤ x 4 := h (by decide : (2 : Fin 5) ≤ 4)
  have h34 : x 3 ≤ x 4 := h (by decide : (3 : Fin 5) ≤ 4)
  simp only [doubleGap, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (|x 0 - x 0| + (|x 0 - x 1| + (|x 0 - x 2| + (|x 0 - x 3| + (|x 0 - x 4|))))) + ((|x 1 - x 0| + (|x 1 - x 1| + (|x 1 - x 2| + (|x 1 - x 3| + (|x 1 - x 4|))))) + ((|x 2 - x 0| + (|x 2 - x 1| + (|x 2 - x 2| + (|x 2 - x 3| + (|x 2 - x 4|))))) + ((|x 3 - x 0| + (|x 3 - x 1| + (|x 3 - x 2| + (|x 3 - x 3| + (|x 3 - x 4|))))) + ((|x 4 - x 0| + (|x 4 - x 1| + (|x 4 - x 2| + (|x 4 - x 3| + (|x 4 - x 4|))))))))) = _
  simp only [sub_self, abs_zero, add_zero, zero_add,
    abs_of_nonpos (sub_nonpos.mpr h01), abs_of_nonneg (sub_nonneg.mpr h01),
    abs_of_nonpos (sub_nonpos.mpr h02), abs_of_nonneg (sub_nonneg.mpr h02),
    abs_of_nonpos (sub_nonpos.mpr h03), abs_of_nonneg (sub_nonneg.mpr h03),
    abs_of_nonpos (sub_nonpos.mpr h04), abs_of_nonneg (sub_nonneg.mpr h04),
    abs_of_nonpos (sub_nonpos.mpr h12), abs_of_nonneg (sub_nonneg.mpr h12),
    abs_of_nonpos (sub_nonpos.mpr h13), abs_of_nonneg (sub_nonneg.mpr h13),
    abs_of_nonpos (sub_nonpos.mpr h14), abs_of_nonneg (sub_nonneg.mpr h14),
    abs_of_nonpos (sub_nonpos.mpr h23), abs_of_nonneg (sub_nonneg.mpr h23),
    abs_of_nonpos (sub_nonpos.mpr h24), abs_of_nonneg (sub_nonneg.mpr h24),
    abs_of_nonpos (sub_nonpos.mpr h34), abs_of_nonneg (sub_nonneg.mpr h34)]
  linarith

/-- Sum over all ordered pairs, or twice the sum over the ten edges of K5. -/
theorem k5_real_projection_bound (x : Fin 5 → ℝ) (a b : ℝ)
    (ha : ∀ i, a ≤ x i) (hb : ∀ i, x i ≤ b) :
    (∑ i, ∑ j, |x i - x j|) ≤ 12*(b-a) := by
  change doubleGap x ≤ _
  let p := Tuple.sort x
  rw [← doubleGap_perm x p, doubleGap_sorted _ (Tuple.monotone_sort x)]
  have ha0 := ha (p 0)
  have ha1 := ha (p 1)
  have hb3 := hb (p 3)
  have hb4 := hb (p 4)
  dsimp only [Function.comp_apply]
  linarith

private def clamp (a b x : ℝ) : ℝ := max a (min b x)

private theorem endpoint_clamp_gap (a b x y : ℝ) (hay : a ≤ y) (hyb : y ≤ b) :
    |y - clamp a b x| ≤ |y - x| := by
  have hab := hay.trans hyb
  by_cases hxa : x < a
  · rw [clamp, min_eq_right (hxa.le.trans hab), max_eq_left hxa.le,
      abs_of_nonneg (sub_nonneg.mpr hay), abs_of_nonneg (sub_nonneg.mpr (hxa.le.trans hay))]
    linarith
  · have hax : a ≤ x := le_of_not_gt hxa
    by_cases hbx : b < x
    · rw [clamp, min_eq_left hbx.le, max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hyb),
        abs_of_nonpos (sub_nonpos.mpr (hyb.trans hbx.le))]
      linarith
    · rw [clamp, min_eq_right (le_of_not_gt hbx), max_eq_right hax]

/-- Projected terminal and local transportation costs, counted on ordered edges.
The center coordinates need not lie in the terminal range. -/
theorem k5_projected_transport_bound (p : Fin 5 → Fin 5 → ℝ) (z : Fin 5 → ℝ) (a b : ℝ)
    (hab : a ≤ b) (ha : ∀ i j, i ≠ j → a ≤ p i j) (hb : ∀ i j, i ≠ j → p i j ≤ b) :
    (∑ i, ∑ j, |p i j - p j i|) ≤
      12*(b-a) + 2*(∑ i, ∑ j, if i = j then 0 else |p i j - z i|) := by
  let w i := clamp a b (z i)
  let c (i j : Fin 5) := if i = j then (0 : ℝ) else |p i j - z i|
  have hw := k5_real_projection_bound w a b (fun i => le_max_left _ _)
    (fun i => max_le hab (min_le_left _ _))
  have hn : ∀ i j, |p i j - p j i| ≤ c i j + (|w i - w j| + c j i) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [c]
    · have h₁ := endpoint_clamp_gap a b (z i) (p i j) (ha i j hij) (hb i j hij)
      have h₂ := endpoint_clamp_gap a b (z j) (p j i) (ha j i (Ne.symm hij)) (hb j i (Ne.symm hij))
      have ht1 := abs_sub_le (p i j) (w i) (p j i)
      have ht2 := abs_sub_le (w i) (w j) (p j i)
      rw [abs_sub_comm (w j) (p j i)] at ht2
      simp only [c, if_neg hij, if_neg (Ne.symm hij)]
      change |p i j - w i| ≤ _ at h₁
      change |p j i - w j| ≤ _ at h₂
      linarith
  have hsum : (∑ i, ∑ j, |p i j - p j i|) ≤
      (∑ i, ∑ j, (c i j + (|w i - w j| + c j i))) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hn i j))
  simp only [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_comm (f := fun i j => c j i)] at hsum
  change _ ≤ _ + 2*(∑ i, ∑ j, c i j)
  linarith

#print axioms k5_projected_transport_bound

#print axioms k5_real_projection_bound
end OddCliquePaper
