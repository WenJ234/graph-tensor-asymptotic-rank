import OddWheelCandidate

namespace WheelVerification
open scoped BigOperators
noncomputable section

theorem oddWheelCandidate_triangle {I J : Type} [Fintype J] [Nonempty J]
    (f : J → I → Bool) (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (x y z : Option I) :
    oddWheelCandidate f s a x z ≤
      oddWheelCandidate f s a x y + oddWheelCandidate f s a y z := by
  let d (i j : I) : ℝ := a/(Fintype.card J : ℝ) * ∑ h, cutDistance (f h) i j
  have hcard : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hc : 0 ≤ a/(Fintype.card J : ℝ) := div_nonneg ha hcard.le
  have hcut (h : J) (i j : I) : 0 ≤ cutDistance (f h) i j ∧ cutDistance (f h) i j ≤ 1 := by
    unfold cutDistance
    split <;> norm_num
  have hd0 (i j : I) : 0 ≤ d i j := mul_nonneg hc (Finset.sum_nonneg fun h _ => (hcut h i j).1)
  have hd1 (i j : I) : d i j ≤ 1 := by
    have hv : (∑ h, cutDistance (f h) i j) ≤ (Fintype.card J : ℝ) := by
      simpa using Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => (hcut h i j).2)
    calc
      d i j ≤ a/(Fintype.card J : ℝ) * (Fintype.card J : ℝ) :=
        mul_le_mul_of_nonneg_left hv hc
      _ = a := div_mul_cancel₀ a hcard.ne'
      _ ≤ 1 := ha'
  have hdtri (i j k : I) : d i k ≤ d i j + d j k := by
    unfold d
    rw [← mul_add,← Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun h _ => cutDistance_triangle (f h) i j k) hc
  cases x <;> cases y <;> cases z <;> simp only [oddWheelCandidate]
  all_goals try linarith
  all_goals try (rename_i i j; change _ at *; linarith [hd0 i j,hd1 i j])
  all_goals try (rename_i i j k; exact hdtri i j k)

#print axioms oddWheelCandidate_triangle
end
end WheelVerification
