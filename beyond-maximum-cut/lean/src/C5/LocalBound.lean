import C5.FiniteCover
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
namespace C5Certificate

private theorem product_bound {xb yb xc yc a bc : ℝ}
 (hyb : 0 ≤ yb) (hxc : 0 ≤ xc) (hb : 0 < xb-yb) (hc : xc-yc < 0)
 (pt : xb*yc ≤ yb*xc+a*bc) :
 0 < min (xb+yb) (xc+yc) ∧
 min (xb+yb) (xc+yc)*((xb-yb)-(xc-yc)) ≤ 2*a*bc := by
  have hSb : 0 < xb+yb := by linarith only [hyb,hb]
  have hSc : 0 < xc+yc := by linarith only [hxc,hc]
  constructor
  · exact lt_min hSb hSc
  · have t₁ := mul_nonneg (sub_nonneg.mpr (min_le_right (xb+yb) (xc+yc))) (le_of_lt hb)
    have t₂ := mul_nonneg (sub_nonneg.mpr (min_le_left (xb+yb) (xc+yc))) (neg_nonneg.mpr (le_of_lt hc))
    nlinarith only [pt,t₁,t₂]

private theorem estimate_le {xb yb xc yc a bc : ℝ}
 (ha : 0 ≤ a) (hyb : 0 ≤ yb) (hxc : 0 ≤ xc) (tb : xb-yb ≤ a) (tc : yc-xc ≤ a)
 (pt : xb*yc ≤ yb*xc+a*bc) (sb : 4*bc ≤ 3*(xb+yb)) (sc : 4*bc ≤ 3*(xc+yc)) :
 (xb-yb)-(xc-yc) ≤ 3*a/2 := by
  by_cases hb : 0 < xb-yb
  · by_cases hc : xc-yc < 0
    · obtain ⟨hm,hp⟩ := product_bound hyb hxc hb hc pt
      have hh : 4*bc ≤ 3*min (xb+yb) (xc+yc) := by
        rcases le_total (xb+yb) (xc+yc) with h|h
        · simpa [min_eq_left h] using sb
        · simpa [min_eq_right h] using sc
      have hmul := mul_le_mul_of_nonneg_right hh ha
      have hf : min (xb+yb) (xc+yc)*((xb-yb)-(xc-yc)) ≤ min (xb+yb) (xc+yc)*(3*a/2) := by
        nlinarith only [hp,hmul]
      exact le_of_mul_le_mul_left hf hm
    · linarith only [ha,tb,le_of_not_gt hc]
  · linarith only [ha,tc,le_of_not_gt hb]

private theorem estimate_lt {xb yb xc yc a bc : ℝ}
 (ha : 0 < a) (hyb : 0 ≤ yb) (hxc : 0 ≤ xc) (tb : xb-yb ≤ a) (tc : yc-xc ≤ a)
 (pt : xb*yc ≤ yb*xc+a*bc) (sb : 4*bc < 3*(xb+yb)) (sc : 4*bc < 3*(xc+yc)) :
 (xb-yb)-(xc-yc) < 3*a/2 := by
  by_cases hb : 0 < xb-yb
  · by_cases hc : xc-yc < 0
    · obtain ⟨hm,hp⟩ := product_bound hyb hxc hb hc pt
      have hh : 4*bc < 3*min (xb+yb) (xc+yc) := by
        rcases le_total (xb+yb) (xc+yc) with h|h
        · simpa [min_eq_left h] using sb
        · simpa [min_eq_right h] using sc
      have hmul := mul_lt_mul_of_pos_right hh ha
      have hf : min (xb+yb) (xc+yc)*((xb-yb)-(xc-yc)) < min (xb+yb) (xc+yc)*(3*a/2) := by
        nlinarith only [hp,hmul]
      exact lt_of_mul_lt_mul_left hf (le_of_lt hm)
    · linarith only [ha,tb,le_of_not_gt hc]
  · linarith only [ha,tc,le_of_not_gt hb]

theorem local0 (d : Fin 10 → ℝ) (h : MetricRows d) (loc : LocalAt d 0) :
 objective d ≤ (49:ℝ)/12 ∧ ((49:ℝ)/12 ≤ objective d → d 4 = 0 ∧ d 9 = 0) := by
  rcases loc with ⟨l0,l1,l2,l3,l4,l5⟩
  have tb0 : d 5-d 7 ≤ d 4 := by linarith only [h.tri123]
  have tc0 : d 1-d 0 ≤ d 4 := by linarith only [h.tri012]
  have pt0 : d 5*d 1 ≤ d 7*d 0+d 4*d 2 := by nlinarith only [h.pt1]
  have e0 := estimate_le (h.box 4).1 (h.box 7).1 (h.box 0).1 tb0 tc0 pt0 (le_of_lt l1) (le_of_lt l0)
  have ex0 (hp : 0 < d 4) := estimate_lt hp (h.box 7).1 (h.box 0).1 tb0 tc0 pt0 l1 l0
  have tb1 : d 6-d 8 ≤ d 4 := by linarith only [h.tri124]
  have tc1 : d 1-d 0 ≤ d 4 := by linarith only [h.tri012]
  have pt1 : d 6*d 1 ≤ d 8*d 0+d 4*d 3 := by nlinarith only [h.pt4]
  have e1 := estimate_le (h.box 4).1 (h.box 8).1 (h.box 0).1 tb1 tc1 pt1 (le_of_lt l3) (le_of_lt l2)
  have ex1 (hp : 0 < d 4) := estimate_lt hp (h.box 8).1 (h.box 0).1 tb1 tc1 pt1 l3 l2
  have tb2 : d 8-d 7 ≤ d 9 := by linarith only [h.tri234]
  have tc2 : d 2-d 3 ≤ d 9 := by linarith only [h.tri043]
  have pt2 : d 8*d 2 ≤ d 7*d 3+d 9*d 1 := by nlinarith only [h.pt10]
  have e2 := estimate_le (h.box 9).1 (h.box 7).1 (h.box 3).1 tb2 tc2 pt2 (le_of_lt l5) (le_of_lt l4)
  have ex2 (hp : 0 < d 9) := estimate_lt hp (h.box 7).1 (h.box 3).1 tb2 tc2 pt2 l5 l4
  have cp := h.cp 2 3 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold objective
  refine ⟨?_,?_⟩
  · linarith only [e0,e1,e2,cp]
  · intro maximal
    constructor
    · by_contra ne
      have hp : 0 < d 4 := lt_of_le_of_ne (h.box 4).1 (Ne.symm ne)
      have strict := ex0 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
    · by_contra ne
      have hp : 0 < d 9 := lt_of_le_of_ne (h.box 9).1 (Ne.symm ne)
      have strict := ex2 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
theorem local1 (d : Fin 10 → ℝ) (h : MetricRows d) (loc : LocalAt d 1) :
 objective d ≤ (49:ℝ)/12 ∧ ((49:ℝ)/12 ≤ objective d → d 7 = 0 ∧ d 3 = 0) := by
  rcases loc with ⟨l0,l1,l2,l3,l4,l5⟩
  have tb0 : d 8-d 9 ≤ d 7 := by linarith only [h.tri234]
  have tc0 : d 5-d 4 ≤ d 7 := by linarith only [h.tri123]
  have pt0 : d 8*d 5 ≤ d 9*d 4+d 7*d 6 := by nlinarith only [h.pt13]
  have e0 := estimate_le (h.box 7).1 (h.box 9).1 (h.box 4).1 tb0 tc0 pt0 (le_of_lt l1) (le_of_lt l0)
  have ex0 (hp : 0 < d 7) := estimate_lt hp (h.box 9).1 (h.box 4).1 tb0 tc0 pt0 l1 l0
  have tb1 : d 1-d 2 ≤ d 7 := by linarith only [h.tri032]
  have tc1 : d 5-d 4 ≤ d 7 := by linarith only [h.tri123]
  have pt1 : d 1*d 5 ≤ d 2*d 4+d 7*d 0 := by nlinarith only [h.pt1]
  have e1 := estimate_le (h.box 7).1 (h.box 2).1 (h.box 4).1 tb1 tc1 pt1 (le_of_lt l3) (le_of_lt l2)
  have ex1 (hp : 0 < d 7) := estimate_lt hp (h.box 2).1 (h.box 4).1 tb1 tc1 pt1 l3 l2
  have tb2 : d 2-d 9 ≤ d 3 := by linarith only [h.tri043]
  have tc2 : d 6-d 0 ≤ d 3 := by linarith only [h.tri104]
  have pt2 : d 2*d 6 ≤ d 9*d 0+d 3*d 5 := by nlinarith only [h.pt7]
  have e2 := estimate_le (h.box 3).1 (h.box 9).1 (h.box 0).1 tb2 tc2 pt2 (le_of_lt l5) (le_of_lt l4)
  have ex2 (hp : 0 < d 3) := estimate_lt hp (h.box 9).1 (h.box 0).1 tb2 tc2 pt2 l5 l4
  have cp := h.cp 3 2 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold objective
  refine ⟨?_,?_⟩
  · linarith only [e0,e1,e2,cp]
  · intro maximal
    constructor
    · by_contra ne
      have hp : 0 < d 7 := lt_of_le_of_ne (h.box 7).1 (Ne.symm ne)
      have strict := ex0 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
    · by_contra ne
      have hp : 0 < d 3 := lt_of_le_of_ne (h.box 3).1 (Ne.symm ne)
      have strict := ex2 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
theorem local2 (d : Fin 10 → ℝ) (h : MetricRows d) (loc : LocalAt d 2) :
 objective d ≤ (49:ℝ)/12 ∧ ((49:ℝ)/12 ≤ objective d → d 9 = 0 ∧ d 0 = 0) := by
  rcases loc with ⟨l0,l1,l2,l3,l4,l5⟩
  have tb0 : d 2-d 3 ≤ d 9 := by linarith only [h.tri043]
  have tc0 : d 8-d 7 ≤ d 9 := by linarith only [h.tri234]
  have pt0 : d 2*d 8 ≤ d 3*d 7+d 9*d 1 := by nlinarith only [h.pt10]
  have e0 := estimate_le (h.box 9).1 (h.box 3).1 (h.box 7).1 tb0 tc0 pt0 (le_of_lt l1) (le_of_lt l0)
  have ex0 (hp : 0 < d 9) := estimate_lt hp (h.box 3).1 (h.box 7).1 tb0 tc0 pt0 l1 l0
  have tb1 : d 5-d 6 ≤ d 9 := by linarith only [h.tri143]
  have tc1 : d 8-d 7 ≤ d 9 := by linarith only [h.tri234]
  have pt1 : d 5*d 8 ≤ d 6*d 7+d 9*d 4 := by nlinarith only [h.pt13]
  have e1 := estimate_le (h.box 9).1 (h.box 6).1 (h.box 7).1 tb1 tc1 pt1 (le_of_lt l3) (le_of_lt l2)
  have ex1 (hp : 0 < d 9) := estimate_lt hp (h.box 6).1 (h.box 7).1 tb1 tc1 pt1 l3 l2
  have tb2 : d 6-d 3 ≤ d 0 := by linarith only [h.tri104]
  have tc2 : d 1-d 4 ≤ d 0 := by linarith only [h.tri012]
  have pt2 : d 6*d 1 ≤ d 3*d 4+d 0*d 8 := by nlinarith only [h.pt4]
  have e2 := estimate_le (h.box 0).1 (h.box 3).1 (h.box 4).1 tb2 tc2 pt2 (le_of_lt l5) (le_of_lt l4)
  have ex2 (hp : 0 < d 0) := estimate_lt hp (h.box 3).1 (h.box 4).1 tb2 tc2 pt2 l5 l4
  have cp := h.cp 3 3 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold objective
  refine ⟨?_,?_⟩
  · linarith only [e0,e1,e2,cp]
  · intro maximal
    constructor
    · by_contra ne
      have hp : 0 < d 9 := lt_of_le_of_ne (h.box 9).1 (Ne.symm ne)
      have strict := ex0 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
    · by_contra ne
      have hp : 0 < d 0 := lt_of_le_of_ne (h.box 0).1 (Ne.symm ne)
      have strict := ex2 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
theorem local3 (d : Fin 10 → ℝ) (h : MetricRows d) (loc : LocalAt d 3) :
 objective d ≤ (49:ℝ)/12 ∧ ((49:ℝ)/12 ≤ objective d → d 3 = 0 ∧ d 4 = 0) := by
  rcases loc with ⟨l0,l1,l2,l3,l4,l5⟩
  have tb0 : d 6-d 0 ≤ d 3 := by linarith only [h.tri104]
  have tc0 : d 2-d 9 ≤ d 3 := by linarith only [h.tri043]
  have pt0 : d 6*d 2 ≤ d 0*d 9+d 3*d 5 := by nlinarith only [h.pt7]
  have e0 := estimate_le (h.box 3).1 (h.box 0).1 (h.box 9).1 tb0 tc0 pt0 (le_of_lt l1) (le_of_lt l0)
  have ex0 (hp : 0 < d 3) := estimate_lt hp (h.box 0).1 (h.box 9).1 tb0 tc0 pt0 l1 l0
  have tb1 : d 8-d 1 ≤ d 3 := by linarith only [h.tri204]
  have tc1 : d 2-d 9 ≤ d 3 := by linarith only [h.tri043]
  have pt1 : d 8*d 2 ≤ d 1*d 9+d 3*d 7 := by nlinarith only [h.pt10]
  have e1 := estimate_le (h.box 3).1 (h.box 1).1 (h.box 9).1 tb1 tc1 pt1 (le_of_lt l3) (le_of_lt l2)
  have ex1 (hp : 0 < d 3) := estimate_lt hp (h.box 1).1 (h.box 9).1 tb1 tc1 pt1 l3 l2
  have tb2 : d 1-d 0 ≤ d 4 := by linarith only [h.tri012]
  have tc2 : d 5-d 7 ≤ d 4 := by linarith only [h.tri123]
  have pt2 : d 1*d 5 ≤ d 0*d 7+d 4*d 2 := by nlinarith only [h.pt1]
  have e2 := estimate_le (h.box 4).1 (h.box 0).1 (h.box 7).1 tb2 tc2 pt2 (le_of_lt l5) (le_of_lt l4)
  have ex2 (hp : 0 < d 4) := estimate_lt hp (h.box 0).1 (h.box 7).1 tb2 tc2 pt2 l5 l4
  have cp := h.cp 3 3 3 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold objective
  refine ⟨?_,?_⟩
  · linarith only [e0,e1,e2,cp]
  · intro maximal
    constructor
    · by_contra ne
      have hp : 0 < d 3 := lt_of_le_of_ne (h.box 3).1 (Ne.symm ne)
      have strict := ex0 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
    · by_contra ne
      have hp : 0 < d 4 := lt_of_le_of_ne (h.box 4).1 (Ne.symm ne)
      have strict := ex2 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
theorem local4 (d : Fin 10 → ℝ) (h : MetricRows d) (loc : LocalAt d 4) :
 objective d ≤ (49:ℝ)/12 ∧ ((49:ℝ)/12 ≤ objective d → d 0 = 0 ∧ d 7 = 0) := by
  rcases loc with ⟨l0,l1,l2,l3,l4,l5⟩
  have tb0 : d 1-d 4 ≤ d 0 := by linarith only [h.tri012]
  have tc0 : d 6-d 3 ≤ d 0 := by linarith only [h.tri104]
  have pt0 : d 1*d 6 ≤ d 4*d 3+d 0*d 8 := by nlinarith only [h.pt4]
  have e0 := estimate_le (h.box 0).1 (h.box 4).1 (h.box 3).1 tb0 tc0 pt0 (le_of_lt l1) (le_of_lt l0)
  have ex0 (hp : 0 < d 0) := estimate_lt hp (h.box 4).1 (h.box 3).1 tb0 tc0 pt0 l1 l0
  have tb1 : d 2-d 5 ≤ d 0 := by linarith only [h.tri013]
  have tc1 : d 6-d 3 ≤ d 0 := by linarith only [h.tri104]
  have pt1 : d 2*d 6 ≤ d 5*d 3+d 0*d 9 := by nlinarith only [h.pt7]
  have e1 := estimate_le (h.box 0).1 (h.box 5).1 (h.box 3).1 tb1 tc1 pt1 (le_of_lt l3) (le_of_lt l2)
  have ex1 (hp : 0 < d 0) := estimate_lt hp (h.box 5).1 (h.box 3).1 tb1 tc1 pt1 l3 l2
  have tb2 : d 5-d 4 ≤ d 7 := by linarith only [h.tri123]
  have tc2 : d 8-d 9 ≤ d 7 := by linarith only [h.tri234]
  have pt2 : d 5*d 8 ≤ d 4*d 9+d 7*d 6 := by nlinarith only [h.pt13]
  have e2 := estimate_le (h.box 7).1 (h.box 4).1 (h.box 9).1 tb2 tc2 pt2 (le_of_lt l5) (le_of_lt l4)
  have ex2 (hp : 0 < d 7) := estimate_lt hp (h.box 4).1 (h.box 9).1 tb2 tc2 pt2 l5 l4
  have cp := h.cp 3 3 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold objective
  refine ⟨?_,?_⟩
  · linarith only [e0,e1,e2,cp]
  · intro maximal
    constructor
    · by_contra ne
      have hp : 0 < d 0 := lt_of_le_of_ne (h.box 0).1 (Ne.symm ne)
      have strict := ex0 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
    · by_contra ne
      have hp : 0 < d 7 := lt_of_le_of_ne (h.box 7).1 (Ne.symm ne)
      have strict := ex2 hp
      linarith only [strict,e0,e1,e2,cp,maximal]
theorem objective_le_normalized (d : Fin 10 → ℝ) (h : MetricRows d)
 (n : Normalization d) : objective d ≤ (49:ℝ)/12 := by
  by_contra! bad
  obtain ⟨c,hc⟩ := finite_cover_normalized d h n (le_of_lt bad)
  fin_cases c
  · exact (not_le_of_gt bad) ((local0 d h hc).1)
  · exact (not_le_of_gt bad) ((local1 d h hc).1)
  · exact (not_le_of_gt bad) ((local2 d h hc).1)
  · exact (not_le_of_gt bad) ((local3 d h hc).1)
  · exact (not_le_of_gt bad) ((local4 d h hc).1)
#print axioms objective_le_normalized
end C5Certificate
