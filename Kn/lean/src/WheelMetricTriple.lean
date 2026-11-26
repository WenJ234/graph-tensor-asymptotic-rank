import WheelMetricCP
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace WheelVerification
open scoped BigOperators

private def delta {I : Type} [DecidableEq I] (a : I) (c : ℝ) (i : I) : ℝ :=
  if i = a then c else 0

noncomputable def tripleWeight {I : Type} [DecidableEq I] (a b h : I) (i : I) : ℝ :=
  delta a 1 i + delta b 1 i + delta h (1/2) i

theorem tripleWeight_nonneg {I : Type} [DecidableEq I] (a b h i : I) :
    0 ≤ tripleWeight a b h i := by
  unfold tripleWeight delta
  positivity

theorem triple_weight_row {I : Type} [Fintype I] [DecidableEq I]
    (d : I → I → ℝ) (a b h : I) (hs : ∀ i j, d i j = d j i)
    (hz : ∀ i, d i i = 0)
    (hcp : 0 ≤ ∑ i, ∑ j, tripleWeight a b h i * (1-2*d i j)*tripleWeight a b h j) :
    4*d a b + 2*d h a + 2*d h b ≤ 25/4 := by
  let f := tripleWeight a b h
  have H := cp_row_to_ordered_metric d f hcp
  have hsum (u : I) (x : ℝ) : (∑ i : I, delta u x i) = x := by
    exact Fintype.sum_ite_eq' u (fun _ => x)
  have htotal : (∑ i : I, f i) = 5/2 := by
    simp only [f, tripleWeight, Finset.sum_add_distrib, hsum]
    norm_num
  rw [htotal] at H
  let B (p q : I → ℝ) : ℝ := ∑ i, ∑ j, p i * d i j * q j
  have hleft (p q r : I → ℝ) :
      B (fun i => p i + q i) r = B p r + B q r := by
    simp only [B, add_mul, Finset.sum_add_distrib]
  have hright (p q r : I → ℝ) :
      B p (fun i => q i + r i) = B p q + B p r := by
    simp only [B, mul_add, Finset.sum_add_distrib]
  have hdelta (u v : I) (x y : ℝ) :
      B (delta u x) (delta v y) = x*d u v*y := by
    unfold B delta
    simp only [ite_mul, mul_ite, zero_mul, mul_zero, Fintype.sum_ite_eq']
  change 2*B f f ≤ _ at H
  change 2*B (fun i => delta a 1 i + delta b 1 i + delta h (1/2) i)
    (fun i => delta a 1 i + delta b 1 i + delta h (1/2) i) ≤ _ at H
  simp only [hleft,hright,hdelta,hz,mul_zero,zero_mul] at H
  rw [hs b a,hs a h,hs b h] at H
  linarith only [H]

#print axioms tripleWeight_nonneg
#print axioms triple_weight_row
end WheelVerification
