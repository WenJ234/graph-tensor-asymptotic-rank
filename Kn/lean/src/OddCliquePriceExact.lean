import OddCliquePriceWidth
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! Optimize the single-site centers and exhibit a sharp two-versus-three placement. -/
namespace OddCliquePaper
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def minTransport (p : Fin 5 → Fin 5 → E) : ℝ := ⨅ z : Fin 5 → E, localTransport p z

theorem minTransport_nonneg (p : Fin 5 → Fin 5 → E) : 0 ≤ minTransport p := by
  apply le_ciInf
  intro z
  unfold localTransport
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  split <;> positivity

theorem optimized_pricing_upper (p : Fin 5 → Fin 5 → E) (hp : 0 < terminalMeanWidth p) :
    (directedLength p / 2 - minTransport p) / terminalMeanWidth p ≤ 6 := by
  apply (div_le_iff₀ hp).mpr
  have hle : directedLength p / 2 - 6 * terminalMeanWidth p ≤ minTransport p := by
    apply le_ciInf
    intro z
    have hz := k5_directed_pricing_upper p z
    linarith
  linarith

def twoThreeCenter (i : Fin 5) : ℝ := if i.val < 2 then 0 else 1
def twoThreePlacement (i _ : Fin 5) : ℝ := twoThreeCenter i

private theorem line_inner (a g : ℝ) : innerSL ℝ a g = a*g := by
  rw [innerSL_apply_apply]
  simp [Real.inner_apply, mul_comm]

theorem two_three_width : terminalMeanWidth twoThreePlacement = 1 := by
  have h0 (g : ℝ) : innerSL ℝ (terminal twoThreePlacement (⟨(0,1),by decide⟩ : K5Terminal)) g = 0 := by
    norm_num [terminal,twoThreePlacement,twoThreeCenter,line_inner]
  have h1 (g : ℝ) : innerSL ℝ (terminal twoThreePlacement (⟨(2,0),by decide⟩ : K5Terminal)) g = g := by
    norm_num [terminal,twoThreePlacement,twoThreeCenter,line_inner]
  have hup (g : ℝ) : upper twoThreePlacement g = max 0 g := by
    unfold upper
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      change innerSL ℝ (twoThreeCenter i.val.1) g ≤ _
      rw [line_inner, twoThreeCenter]
      split
      · simpa only [zero_mul] using (le_max_left (0 : ℝ) g)
      · simpa only [one_mul] using (le_max_right (0 : ℝ) g)
    · apply max_le
      · have := Finset.le_sup' (fun i : K5Terminal => innerSL ℝ (terminal twoThreePlacement i) g)
          (Finset.mem_univ (⟨(0,1),by decide⟩ : K5Terminal))
        simpa only [h0 g] using this
      · have := Finset.le_sup' (fun i : K5Terminal => innerSL ℝ (terminal twoThreePlacement i) g)
          (Finset.mem_univ (⟨(2,0),by decide⟩ : K5Terminal))
        simpa only [h1 g] using this
  have hlo (g : ℝ) : lower twoThreePlacement g = min 0 g := by
    unfold lower
    apply le_antisymm
    · apply le_min
      · have := Finset.inf'_le (fun i : K5Terminal => innerSL ℝ (terminal twoThreePlacement i) g)
          (Finset.mem_univ (⟨(0,1),by decide⟩ : K5Terminal))
        simpa only [h0 g] using this
      · have := Finset.inf'_le (fun i : K5Terminal => innerSL ℝ (terminal twoThreePlacement i) g)
          (Finset.mem_univ (⟨(2,0),by decide⟩ : K5Terminal))
        simpa only [h1 g] using this
    · apply Finset.le_inf'
      intro i hi
      change _ ≤ innerSL ℝ (twoThreeCenter i.val.1) g
      rw [line_inner, twoThreeCenter]
      split
      · simpa only [zero_mul] using (min_le_left (0 : ℝ) g)
      · simpa only [one_mul] using (min_le_right (0 : ℝ) g)
  have hg (g : ℝ) : max 0 g - min 0 g = |g| := by
    rcases le_total 0 g with h | h
    · simp [max_eq_right h, min_eq_left h, abs_of_nonneg h]
    · simp [max_eq_left h, min_eq_right h, abs_of_nonpos h]
  unfold terminalMeanWidth
  simp_rw [hup,hlo,hg]
  have he := gaussian_inner_abs_mean (1 : ℝ)
  simp only [line_inner, one_mul, norm_one] at he
  rw [he, div_self gaussianAbsMean_pos.ne']

theorem two_three_length : directedLength twoThreePlacement = 12 := by
  norm_num [directedLength, twoThreePlacement, twoThreeCenter, Fin.sum_univ_succ, Real.norm_eq_abs]

theorem two_three_minTransport : minTransport twoThreePlacement = 0 := by
  apply le_antisymm _ (minTransport_nonneg _)
  have hz : localTransport twoThreePlacement twoThreeCenter = 0 := by
    simp [localTransport,twoThreePlacement]
  rw [← hz]
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro _ ⟨z,rfl⟩
  unfold localTransport
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  split <;> positivity

theorem k5_price_isGreatest :
    IsGreatest {r : ℝ | ∃ p : Fin 5 → Fin 5 → ℝ, 0 < terminalMeanWidth p ∧
      r = (directedLength p / 2 - minTransport p) / terminalMeanWidth p} 6 := by
  constructor
  · refine ⟨twoThreePlacement, by simp [two_three_width], ?_⟩
    norm_num [two_three_width, two_three_length, two_three_minTransport]
  · rintro r ⟨p, hp, rfl⟩
    exact optimized_pricing_upper p hp

#print axioms optimized_pricing_upper
#print axioms k5_price_isGreatest
end
end OddCliquePaper
