import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace WheelVerification
open scoped BigOperators

def HubWeight {R : Type} (t : ℝ) : Option R → ℝ
  | none => t
  | some _ => 1

theorem cp_row_to_ordered_metric {I : Type} [Fintype I] (d : I → I → ℝ) (w : I → ℝ)
    (h : 0 ≤ ∑ i, ∑ j, w i * (1 - 2 * d i j) * w j) :
    2 * (∑ i, ∑ j, w i * d i j * w j) ≤ (∑ i, w i)^2 := by
  have hs (i j : I) : w i * (1 - 2 * d i j) * w j =
      w i * w j - 2 * (w i * d i j * w j) := by ring
  simp_rw [hs, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsq : (∑ i : I, w i * (∑ j : I, w j)) = (∑ i, w i)^2 := by
    rw [← Finset.sum_mul, pow_two]
  rw [hsq] at h
  linarith only [h]

theorem hub_weight_row {R : Type} [Fintype R] (d : Option R → Option R → ℝ) (t : ℝ)
    (hs : ∀ i j, d i j = d j i) (hz : d none none = 0)
    (h : 0 ≤ ∑ i, ∑ j, HubWeight t i * (1 - 2 * d i j) * HubWeight t j) :
    2 * (∑ i : R, ∑ j : R, d (some i) (some j)) +
      4*t*(∑ i : R, d none (some i)) ≤ ((Fintype.card R : ℝ) + t)^2 := by
  have hh := cp_row_to_ordered_metric d (HubWeight t) h
  have ht : (∑ i : Option R, HubWeight t i) = t + Fintype.card R := by
    rw [univ_option, Finset.sum_insertNone]
    simp [HubWeight]
  have hd : (∑ i : Option R, ∑ j : Option R, HubWeight t i * d i j * HubWeight t j) =
      (∑ i : R, ∑ j : R, d (some i) (some j)) + 2*t*(∑ i : R, d none (some i)) := by
    simp only [univ_option, Finset.sum_insertNone, HubWeight, hz, mul_zero, zero_mul, one_mul, mul_one, zero_add,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have he : (∑ i : R, d (some i) none) = ∑ i : R, d none (some i) :=
      Finset.sum_congr rfl fun i _ => hs (some i) none
    rw [he]
    ring
  rw [ht,hd] at hh
  nlinarith only [hh]

#print axioms cp_row_to_ordered_metric
#print axioms hub_weight_row
end WheelVerification
