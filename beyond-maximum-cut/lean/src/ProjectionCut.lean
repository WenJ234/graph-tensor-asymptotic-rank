import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
open MeasureTheory
namespace WenJ.GraphTensor.MaxCut
universe u
variable {V : Type u}

noncomputable def cutWeight (edges : Finset (V × V)) (b : V → Bool) : ℝ :=
  ∑ e ∈ edges, if b e.1 = b e.2 then 0 else 1

noncomputable def pulse (a b : ℝ) : ℝ → ℝ :=
  (Set.Ioc (min a b) (max a b)).indicator fun _ => 1

private theorem pulse_integrable (a b : ℝ) : Integrable (pulse a b) := by
  unfold pulse
  exact (integrableOn_const (μ := volume) (C := (1 : ℝ))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioc

private theorem interval_one_integral (a b : ℝ) (h : a ≤ b) :
    (∫ x : ℝ, (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x) = b-a := by
  rw [integral_indicator_const 1 measurableSet_Ioc]
  simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr h), smul_eq_mul,
    mul_one]

private theorem integral_pulse (a b : ℝ) : (∫ x, pulse a b x) = |a-b| := by
  unfold pulse
  rw [interval_one_integral _ _ (min_le_max)]
  rcases le_total a b with h | h
  · simp [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
  · simp [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]

private theorem pulse_eq_cut (a b s : ℝ) :
    pulse a b s = if decide (s ≤ a) = decide (s ≤ b) then 0 else 1 := by
  classical
  rcases le_total a b with hab | hba
  · by_cases ha : s ≤ a
    · have hb := ha.trans hab
      simp [pulse, min_eq_left hab, max_eq_right hab, Set.indicator, ha, hb, not_lt_of_ge ha]
    · by_cases hb : s ≤ b
      · simp [pulse, min_eq_left hab, max_eq_right hab, Set.indicator, ha, hb, lt_of_not_ge ha]
      · simp [pulse, min_eq_left hab, max_eq_right hab, Set.indicator, ha, hb]
  · by_cases hb : s ≤ b
    · have ha := hb.trans hba
      simp [pulse, min_eq_right hba, max_eq_left hba, Set.indicator, ha, hb, not_lt_of_ge hb]
    · by_cases ha : s ≤ a
      · simp [pulse, min_eq_right hba, max_eq_left hba, Set.indicator, ha, hb, lt_of_not_ge hb]
      · simp [pulse, min_eq_right hba, max_eq_left hba, Set.indicator, ha, hb]

theorem proj_edge_sum_le_cut_times_range (edges : Finset (V × V))
    (t : V → ℝ) (lo hi K : ℝ) (hlohi : lo ≤ hi)
    (hbound : ∀ v, lo ≤ t v ∧ t v ≤ hi)
    (hcut : ∀ b : V → Bool, cutWeight edges b ≤ K) :
    ∑ e ∈ edges, |t e.1 - t e.2| ≤ K * (hi-lo) := by
  let F (e : V × V) (s : ℝ) := pulse (t e.1) (t e.2) s
  let I (s : ℝ) : ℝ := (Set.Ioc lo hi).indicator (fun _ => (1 : ℝ)) s
  have hloc : ∀ s, (∑ e ∈ edges, F e s) ≤ K * I s := by
    intro s
    by_cases hs : s ∈ Set.Ioc lo hi
    · simpa [I, hs, F, pulse_eq_cut, cutWeight] using hcut (fun v => decide (s ≤ t v))
    · have hzero (e : V × V) : F e s = 0 := by
        have he : s ∉ Set.Ioc (min (t e.1) (t e.2)) (max (t e.1) (t e.2)) := by
          intro he
          exact hs ⟨lt_of_le_of_lt (le_min (hbound _).1 (hbound _).1) he.1,
            he.2.trans (max_le (hbound _).2 (hbound _).2)⟩
        simp [F, pulse, he]
      simp [I, hs, hzero]
  have hf (e : V × V) : Integrable (F e) := pulse_integrable _ _
  have hI : Integrable I :=
    (integrableOn_const (μ := volume) (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioc
  have h := integral_mono (integrable_finsetSum edges (fun e _ => hf e)) (hI.const_mul K) hloc
  rw [integral_finsetSum edges (fun e _ => hf e), integral_const_mul] at h
  simpa [F, I, integral_pulse, interval_one_integral _ _ hlohi] using h
end WenJ.GraphTensor.MaxCut
#print axioms WenJ.GraphTensor.MaxCut.proj_edge_sum_le_cut_times_range
