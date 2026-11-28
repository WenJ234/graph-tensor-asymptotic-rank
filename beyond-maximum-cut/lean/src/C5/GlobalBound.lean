import C5.LocalBound
namespace C5Certificate
set_option maxHeartbeats 0
private theorem least5 (a0 a1 a2 a3 a4 : ℝ) :
 (a0≤a1 ∧ a0≤a2 ∧ a0≤a3 ∧ a0≤a4) ∨ (a1≤a0 ∧ a1≤a2 ∧ a1≤a3 ∧ a1≤a4) ∨ (a2≤a0 ∧ a2≤a1 ∧ a2≤a3 ∧ a2≤a4) ∨ (a3≤a0 ∧ a3≤a1 ∧ a3≤a2 ∧ a3≤a4) ∨ (a4≤a0 ∧ a4≤a1 ∧ a4≤a2 ∧ a4≤a3) := by
  by_cases h1 : a0≤a1
  ·
    by_cases h2 : a0≤a2
    ·
      by_cases h3 : a0≤a3
      ·
        by_cases h4 : a0≤a4
        ·
          exact Or.inl ⟨h1, h2, h3, h4⟩
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨r4, (le_trans r4 h1), (le_trans r4 h2), (le_trans r4 h3)⟩))))
      · have r3 := le_of_lt (lt_of_not_ge h3)
        by_cases h4 : a3≤a4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r3, (le_trans r3 h1), (le_trans r3 h2), h4⟩)))
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 r3), (le_trans r4 (le_trans r3 h1)), (le_trans r4 (le_trans r3 h2)), r4⟩))))
    · have r2 := le_of_lt (lt_of_not_ge h2)
      by_cases h3 : a2≤a3
      ·
        by_cases h4 : a2≤a4
        ·
          exact Or.inr (Or.inr (Or.inl ⟨r2, (le_trans r2 h1), h3, h4⟩))
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 r2), (le_trans r4 (le_trans r2 h1)), r4, (le_trans r4 h3)⟩))))
      · have r3 := le_of_lt (lt_of_not_ge h3)
        by_cases h4 : a3≤a4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(le_trans r3 r2), (le_trans r3 (le_trans r2 h1)), r3, h4⟩)))
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 (le_trans r3 r2)), (le_trans r4 (le_trans r3 (le_trans r2 h1))), (le_trans r4 r3), r4⟩))))
  · have r1 := le_of_lt (lt_of_not_ge h1)
    by_cases h2 : a1≤a2
    ·
      by_cases h3 : a1≤a3
      ·
        by_cases h4 : a1≤a4
        ·
          exact Or.inr (Or.inl ⟨r1, h2, h3, h4⟩)
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 r1), r4, (le_trans r4 h2), (le_trans r4 h3)⟩))))
      · have r3 := le_of_lt (lt_of_not_ge h3)
        by_cases h4 : a3≤a4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(le_trans r3 r1), r3, (le_trans r3 h2), h4⟩)))
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 (le_trans r3 r1)), (le_trans r4 r3), (le_trans r4 (le_trans r3 h2)), r4⟩))))
    · have r2 := le_of_lt (lt_of_not_ge h2)
      by_cases h3 : a2≤a3
      ·
        by_cases h4 : a2≤a4
        ·
          exact Or.inr (Or.inr (Or.inl ⟨(le_trans r2 r1), r2, h3, h4⟩))
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 (le_trans r2 r1)), (le_trans r4 r2), r4, (le_trans r4 h3)⟩))))
      · have r3 := le_of_lt (lt_of_not_ge h3)
        by_cases h4 : a3≤a4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(le_trans r3 (le_trans r2 r1)), (le_trans r3 r2), r3, h4⟩)))
        · have r4 := le_of_lt (lt_of_not_ge h4)
          exact Or.inr (Or.inr (Or.inr (Or.inr (⟨(le_trans r4 (le_trans r3 (le_trans r2 r1))), (le_trans r4 (le_trans r3 r2)), (le_trans r4 r3), r4⟩))))
def p00 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 0
 | 1 => d 1
 | 2 => d 2
 | 3 => d 3
 | 4 => d 4
 | 5 => d 5
 | 6 => d 6
 | 7 => d 7
 | 8 => d 8
 | 9 => d 9
theorem mp00 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p00 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 0
    · exact h.box 1
    · exact h.box 2
    · exact h.box 3
    · exact h.box 4
    · exact h.box 5
    · exact h.box 6
    · exact h.box 7
    · exact h.box 8
    · exact h.box 9
  · change d 4 ≤ d 0+d 1
    simpa only [add_comm] using h.tri102
  · change d 5 ≤ d 0+d 2
    simpa only [add_comm] using h.tri103
  · change d 6 ≤ d 0+d 3
    simpa only [add_comm] using h.tri104
  · change d 7 ≤ d 1+d 2
    simpa only [add_comm] using h.tri203
  · change d 8 ≤ d 1+d 3
    simpa only [add_comm] using h.tri204
  · change d 9 ≤ d 2+d 3
    simpa only [add_comm] using h.tri304
  · change d 1 ≤ d 0+d 4
    simpa only [add_comm] using h.tri012
  · change d 2 ≤ d 0+d 5
    simpa only [add_comm] using h.tri013
  · change d 3 ≤ d 0+d 6
    simpa only [add_comm] using h.tri014
  · change d 7 ≤ d 4+d 5
    simpa only [add_comm] using h.tri213
  · change d 8 ≤ d 4+d 6
    simpa only [add_comm] using h.tri214
  · change d 9 ≤ d 5+d 6
    simpa only [add_comm] using h.tri314
  · change d 0 ≤ d 1+d 4
    simpa only [add_comm] using h.tri021
  · change d 2 ≤ d 1+d 7
    simpa only [add_comm] using h.tri023
  · change d 3 ≤ d 1+d 8
    simpa only [add_comm] using h.tri024
  · change d 5 ≤ d 4+d 7
    simpa only [add_comm] using h.tri123
  · change d 6 ≤ d 4+d 8
    simpa only [add_comm] using h.tri124
  · change d 9 ≤ d 7+d 8
    simpa only [add_comm] using h.tri324
  · change d 0 ≤ d 2+d 5
    simpa only [add_comm] using h.tri031
  · change d 1 ≤ d 2+d 7
    simpa only [add_comm] using h.tri032
  · change d 3 ≤ d 2+d 9
    simpa only [add_comm] using h.tri034
  · change d 4 ≤ d 5+d 7
    simpa only [add_comm] using h.tri132
  · change d 6 ≤ d 5+d 9
    simpa only [add_comm] using h.tri134
  · change d 8 ≤ d 7+d 9
    simpa only [add_comm] using h.tri234
  · change d 0 ≤ d 3+d 6
    simpa only [add_comm] using h.tri041
  · change d 1 ≤ d 3+d 8
    simpa only [add_comm] using h.tri042
  · change d 2 ≤ d 3+d 9
    simpa only [add_comm] using h.tri043
  · change d 4 ≤ d 6+d 8
    simpa only [add_comm] using h.tri142
  · change d 5 ≤ d 6+d 9
    simpa only [add_comm] using h.tri143
  · change d 7 ≤ d 8+d 9
    simpa only [add_comm] using h.tri243
  · change d 0*d 7 ≤ d 1*d 5+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 1*d 5 ≤ d 0*d 7+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 2*d 4 ≤ d 0*d 7+d 1*d 5
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 0*d 8 ≤ d 1*d 6+d 3*d 4
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 1*d 6 ≤ d 0*d 8+d 3*d 4
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 3*d 4 ≤ d 0*d 8+d 1*d 6
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 0*d 9 ≤ d 2*d 6+d 3*d 5
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 2*d 6 ≤ d 0*d 9+d 3*d 5
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 3*d 5 ≤ d 0*d 9+d 2*d 6
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 1*d 9 ≤ d 2*d 8+d 3*d 7
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 2*d 8 ≤ d 1*d 9+d 3*d 7
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 3*d 7 ≤ d 1*d 9+d 2*d 8
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 4*d 9 ≤ d 5*d 8+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 5*d 8 ≤ d 4*d 9+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 6*d 7 ≤ d 4*d 9+d 5*d 8
    simpa only [mul_comm,add_comm] using h.pt14
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    change 4*a0*a1*d 0+4*a0*a2*d 1+4*a0*a3*d 2+4*a0*a4*d 3+4*a1*a2*d 4+4*a1*a3*d 5+4*a1*a4*d 6+4*a2*a3*d 7+4*a2*a4*d 8+4*a3*a4*d 9 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op00 (d:Fin 10→ℝ) : objective (p00 d)=objective d := by
  change d 1+d 5+d 8+d 2+d 6=d 1+d 5+d 8+d 2+d 6
  ring
def p01 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 0
 | 1 => d 6
 | 2 => d 5
 | 3 => d 4
 | 4 => d 3
 | 5 => d 2
 | 6 => d 1
 | 7 => d 9
 | 8 => d 8
 | 9 => d 7
theorem mp01 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p01 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 0
    · exact h.box 6
    · exact h.box 5
    · exact h.box 4
    · exact h.box 3
    · exact h.box 2
    · exact h.box 1
    · exact h.box 9
    · exact h.box 8
    · exact h.box 7
  · change d 3 ≤ d 0+d 6
    simpa only [add_comm] using h.tri014
  · change d 2 ≤ d 0+d 5
    simpa only [add_comm] using h.tri013
  · change d 1 ≤ d 0+d 4
    simpa only [add_comm] using h.tri012
  · change d 9 ≤ d 6+d 5
    simpa only [add_comm] using h.tri314
  · change d 8 ≤ d 6+d 4
    simpa only [add_comm] using h.tri214
  · change d 7 ≤ d 5+d 4
    simpa only [add_comm] using h.tri213
  · change d 6 ≤ d 0+d 3
    simpa only [add_comm] using h.tri104
  · change d 5 ≤ d 0+d 2
    simpa only [add_comm] using h.tri103
  · change d 4 ≤ d 0+d 1
    simpa only [add_comm] using h.tri102
  · change d 9 ≤ d 3+d 2
    simpa only [add_comm] using h.tri304
  · change d 8 ≤ d 3+d 1
    simpa only [add_comm] using h.tri204
  · change d 7 ≤ d 2+d 1
    simpa only [add_comm] using h.tri203
  · change d 0 ≤ d 6+d 3
    simpa only [add_comm] using h.tri041
  · change d 5 ≤ d 6+d 9
    simpa only [add_comm] using h.tri143
  · change d 4 ≤ d 6+d 8
    simpa only [add_comm] using h.tri142
  · change d 2 ≤ d 3+d 9
    simpa only [add_comm] using h.tri043
  · change d 1 ≤ d 3+d 8
    simpa only [add_comm] using h.tri042
  · change d 7 ≤ d 9+d 8
    simpa only [add_comm] using h.tri243
  · change d 0 ≤ d 5+d 2
    simpa only [add_comm] using h.tri031
  · change d 6 ≤ d 5+d 9
    simpa only [add_comm] using h.tri134
  · change d 4 ≤ d 5+d 7
    simpa only [add_comm] using h.tri132
  · change d 3 ≤ d 2+d 9
    simpa only [add_comm] using h.tri034
  · change d 1 ≤ d 2+d 7
    simpa only [add_comm] using h.tri032
  · change d 8 ≤ d 9+d 7
    simpa only [add_comm] using h.tri234
  · change d 0 ≤ d 4+d 1
    simpa only [add_comm] using h.tri021
  · change d 6 ≤ d 4+d 8
    simpa only [add_comm] using h.tri124
  · change d 5 ≤ d 4+d 7
    simpa only [add_comm] using h.tri123
  · change d 3 ≤ d 1+d 8
    simpa only [add_comm] using h.tri024
  · change d 2 ≤ d 1+d 7
    simpa only [add_comm] using h.tri023
  · change d 9 ≤ d 8+d 7
    simpa only [add_comm] using h.tri324
  · change d 0*d 9 ≤ d 6*d 2+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 6*d 2 ≤ d 0*d 9+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 5*d 3 ≤ d 0*d 9+d 6*d 2
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 0*d 8 ≤ d 6*d 1+d 4*d 3
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 6*d 1 ≤ d 0*d 8+d 4*d 3
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 4*d 3 ≤ d 0*d 8+d 6*d 1
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 0*d 7 ≤ d 5*d 1+d 4*d 2
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 5*d 1 ≤ d 0*d 7+d 4*d 2
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 4*d 2 ≤ d 0*d 7+d 5*d 1
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 6*d 7 ≤ d 5*d 8+d 4*d 9
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 5*d 8 ≤ d 6*d 7+d 4*d 9
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 4*d 9 ≤ d 6*d 7+d 5*d 8
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 3*d 7 ≤ d 2*d 8+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 2*d 8 ≤ d 3*d 7+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 1*d 9 ≤ d 3*d 7+d 2*d 8
    simpa only [mul_comm,add_comm] using h.pt9
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a1 a0 a4 a3 a2 h1 h0 h4 h3 h2
    change 4*a0*a1*d 0+4*a0*a2*d 6+4*a0*a3*d 5+4*a0*a4*d 4+4*a1*a2*d 3+4*a1*a3*d 2+4*a1*a4*d 1+4*a2*a3*d 9+4*a2*a4*d 8+4*a3*a4*d 7 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op01 (d:Fin 10→ℝ) : objective (p01 d)=objective d := by
  change d 6+d 2+d 8+d 5+d 1=d 1+d 5+d 8+d 2+d 6
  ring
def p10 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 4
 | 1 => d 5
 | 2 => d 6
 | 3 => d 0
 | 4 => d 7
 | 5 => d 8
 | 6 => d 1
 | 7 => d 9
 | 8 => d 2
 | 9 => d 3
theorem mp10 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p10 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 4
    · exact h.box 5
    · exact h.box 6
    · exact h.box 0
    · exact h.box 7
    · exact h.box 8
    · exact h.box 1
    · exact h.box 9
    · exact h.box 2
    · exact h.box 3
  · change d 7 ≤ d 4+d 5
    simpa only [add_comm] using h.tri213
  · change d 8 ≤ d 4+d 6
    simpa only [add_comm] using h.tri214
  · change d 1 ≤ d 4+d 0
    simpa only [add_comm] using h.tri012
  · change d 9 ≤ d 5+d 6
    simpa only [add_comm] using h.tri314
  · change d 2 ≤ d 5+d 0
    simpa only [add_comm] using h.tri013
  · change d 3 ≤ d 6+d 0
    simpa only [add_comm] using h.tri014
  · change d 5 ≤ d 4+d 7
    simpa only [add_comm] using h.tri123
  · change d 6 ≤ d 4+d 8
    simpa only [add_comm] using h.tri124
  · change d 0 ≤ d 4+d 1
    simpa only [add_comm] using h.tri021
  · change d 9 ≤ d 7+d 8
    simpa only [add_comm] using h.tri324
  · change d 2 ≤ d 7+d 1
    simpa only [add_comm] using h.tri023
  · change d 3 ≤ d 8+d 1
    simpa only [add_comm] using h.tri024
  · change d 4 ≤ d 5+d 7
    simpa only [add_comm] using h.tri132
  · change d 6 ≤ d 5+d 9
    simpa only [add_comm] using h.tri134
  · change d 0 ≤ d 5+d 2
    simpa only [add_comm] using h.tri031
  · change d 8 ≤ d 7+d 9
    simpa only [add_comm] using h.tri234
  · change d 1 ≤ d 7+d 2
    simpa only [add_comm] using h.tri032
  · change d 3 ≤ d 9+d 2
    simpa only [add_comm] using h.tri034
  · change d 4 ≤ d 6+d 8
    simpa only [add_comm] using h.tri142
  · change d 5 ≤ d 6+d 9
    simpa only [add_comm] using h.tri143
  · change d 0 ≤ d 6+d 3
    simpa only [add_comm] using h.tri041
  · change d 7 ≤ d 8+d 9
    simpa only [add_comm] using h.tri243
  · change d 1 ≤ d 8+d 3
    simpa only [add_comm] using h.tri042
  · change d 2 ≤ d 9+d 3
    simpa only [add_comm] using h.tri043
  · change d 4 ≤ d 0+d 1
    simpa only [add_comm] using h.tri102
  · change d 5 ≤ d 0+d 2
    simpa only [add_comm] using h.tri103
  · change d 6 ≤ d 0+d 3
    simpa only [add_comm] using h.tri104
  · change d 7 ≤ d 1+d 2
    simpa only [add_comm] using h.tri203
  · change d 8 ≤ d 1+d 3
    simpa only [add_comm] using h.tri204
  · change d 9 ≤ d 2+d 3
    simpa only [add_comm] using h.tri304
  · change d 4*d 9 ≤ d 5*d 8+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 5*d 8 ≤ d 4*d 9+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 6*d 7 ≤ d 4*d 9+d 5*d 8
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 4*d 2 ≤ d 5*d 1+d 0*d 7
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 5*d 1 ≤ d 4*d 2+d 0*d 7
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 0*d 7 ≤ d 4*d 2+d 5*d 1
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 4*d 3 ≤ d 6*d 1+d 0*d 8
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 6*d 1 ≤ d 4*d 3+d 0*d 8
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 0*d 8 ≤ d 4*d 3+d 6*d 1
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 5*d 3 ≤ d 6*d 2+d 0*d 9
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 6*d 2 ≤ d 5*d 3+d 0*d 9
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 0*d 9 ≤ d 5*d 3+d 6*d 2
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 7*d 3 ≤ d 8*d 2+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 8*d 2 ≤ d 7*d 3+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 1*d 9 ≤ d 7*d 3+d 8*d 2
    simpa only [mul_comm,add_comm] using h.pt9
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a4 a0 a1 a2 a3 h4 h0 h1 h2 h3
    change 4*a0*a1*d 4+4*a0*a2*d 5+4*a0*a3*d 6+4*a0*a4*d 0+4*a1*a2*d 7+4*a1*a3*d 8+4*a1*a4*d 1+4*a2*a3*d 9+4*a2*a4*d 2+4*a3*a4*d 3 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op10 (d:Fin 10→ℝ) : objective (p10 d)=objective d := by
  change d 5+d 8+d 2+d 6+d 1=d 1+d 5+d 8+d 2+d 6
  ring
def p11 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 4
 | 1 => d 1
 | 2 => d 8
 | 3 => d 7
 | 4 => d 0
 | 5 => d 6
 | 6 => d 5
 | 7 => d 3
 | 8 => d 2
 | 9 => d 9
theorem mp11 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p11 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 4
    · exact h.box 1
    · exact h.box 8
    · exact h.box 7
    · exact h.box 0
    · exact h.box 6
    · exact h.box 5
    · exact h.box 3
    · exact h.box 2
    · exact h.box 9
  · change d 0 ≤ d 4+d 1
    simpa only [add_comm] using h.tri021
  · change d 6 ≤ d 4+d 8
    simpa only [add_comm] using h.tri124
  · change d 5 ≤ d 4+d 7
    simpa only [add_comm] using h.tri123
  · change d 3 ≤ d 1+d 8
    simpa only [add_comm] using h.tri024
  · change d 2 ≤ d 1+d 7
    simpa only [add_comm] using h.tri023
  · change d 9 ≤ d 8+d 7
    simpa only [add_comm] using h.tri324
  · change d 1 ≤ d 4+d 0
    simpa only [add_comm] using h.tri012
  · change d 8 ≤ d 4+d 6
    simpa only [add_comm] using h.tri214
  · change d 7 ≤ d 4+d 5
    simpa only [add_comm] using h.tri213
  · change d 3 ≤ d 0+d 6
    simpa only [add_comm] using h.tri014
  · change d 2 ≤ d 0+d 5
    simpa only [add_comm] using h.tri013
  · change d 9 ≤ d 6+d 5
    simpa only [add_comm] using h.tri314
  · change d 4 ≤ d 1+d 0
    simpa only [add_comm] using h.tri102
  · change d 8 ≤ d 1+d 3
    simpa only [add_comm] using h.tri204
  · change d 7 ≤ d 1+d 2
    simpa only [add_comm] using h.tri203
  · change d 6 ≤ d 0+d 3
    simpa only [add_comm] using h.tri104
  · change d 5 ≤ d 0+d 2
    simpa only [add_comm] using h.tri103
  · change d 9 ≤ d 3+d 2
    simpa only [add_comm] using h.tri304
  · change d 4 ≤ d 8+d 6
    simpa only [add_comm] using h.tri142
  · change d 1 ≤ d 8+d 3
    simpa only [add_comm] using h.tri042
  · change d 7 ≤ d 8+d 9
    simpa only [add_comm] using h.tri243
  · change d 0 ≤ d 6+d 3
    simpa only [add_comm] using h.tri041
  · change d 5 ≤ d 6+d 9
    simpa only [add_comm] using h.tri143
  · change d 2 ≤ d 3+d 9
    simpa only [add_comm] using h.tri043
  · change d 4 ≤ d 7+d 5
    simpa only [add_comm] using h.tri132
  · change d 1 ≤ d 7+d 2
    simpa only [add_comm] using h.tri032
  · change d 8 ≤ d 7+d 9
    simpa only [add_comm] using h.tri234
  · change d 0 ≤ d 5+d 2
    simpa only [add_comm] using h.tri031
  · change d 6 ≤ d 5+d 9
    simpa only [add_comm] using h.tri134
  · change d 3 ≤ d 2+d 9
    simpa only [add_comm] using h.tri034
  · change d 4*d 3 ≤ d 1*d 6+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 1*d 6 ≤ d 4*d 3+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 8*d 0 ≤ d 4*d 3+d 1*d 6
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 4*d 2 ≤ d 1*d 5+d 7*d 0
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 1*d 5 ≤ d 4*d 2+d 7*d 0
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 7*d 0 ≤ d 4*d 2+d 1*d 5
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 4*d 9 ≤ d 8*d 5+d 7*d 6
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 8*d 5 ≤ d 4*d 9+d 7*d 6
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 7*d 6 ≤ d 4*d 9+d 8*d 5
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 1*d 9 ≤ d 8*d 2+d 7*d 3
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 8*d 2 ≤ d 1*d 9+d 7*d 3
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 7*d 3 ≤ d 1*d 9+d 8*d 2
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 0*d 9 ≤ d 6*d 2+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 6*d 2 ≤ d 0*d 9+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 5*d 3 ≤ d 0*d 9+d 6*d 2
    simpa only [mul_comm,add_comm] using h.pt8
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a2 a1 a0 a4 a3 h2 h1 h0 h4 h3
    change 4*a0*a1*d 4+4*a0*a2*d 1+4*a0*a3*d 8+4*a0*a4*d 7+4*a1*a2*d 0+4*a1*a3*d 6+4*a1*a4*d 5+4*a2*a3*d 3+4*a2*a4*d 2+4*a3*a4*d 9 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op11 (d:Fin 10→ℝ) : objective (p11 d)=objective d := by
  change d 1+d 6+d 2+d 8+d 5=d 1+d 5+d 8+d 2+d 6
  ring
def p20 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 7
 | 1 => d 8
 | 2 => d 1
 | 3 => d 4
 | 4 => d 9
 | 5 => d 2
 | 6 => d 5
 | 7 => d 3
 | 8 => d 6
 | 9 => d 0
theorem mp20 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p20 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 7
    · exact h.box 8
    · exact h.box 1
    · exact h.box 4
    · exact h.box 9
    · exact h.box 2
    · exact h.box 5
    · exact h.box 3
    · exact h.box 6
    · exact h.box 0
  · change d 9 ≤ d 7+d 8
    simpa only [add_comm] using h.tri324
  · change d 2 ≤ d 7+d 1
    simpa only [add_comm] using h.tri023
  · change d 5 ≤ d 7+d 4
    simpa only [add_comm] using h.tri123
  · change d 3 ≤ d 8+d 1
    simpa only [add_comm] using h.tri024
  · change d 6 ≤ d 8+d 4
    simpa only [add_comm] using h.tri124
  · change d 0 ≤ d 1+d 4
    simpa only [add_comm] using h.tri021
  · change d 8 ≤ d 7+d 9
    simpa only [add_comm] using h.tri234
  · change d 1 ≤ d 7+d 2
    simpa only [add_comm] using h.tri032
  · change d 4 ≤ d 7+d 5
    simpa only [add_comm] using h.tri132
  · change d 3 ≤ d 9+d 2
    simpa only [add_comm] using h.tri034
  · change d 6 ≤ d 9+d 5
    simpa only [add_comm] using h.tri134
  · change d 0 ≤ d 2+d 5
    simpa only [add_comm] using h.tri031
  · change d 7 ≤ d 8+d 9
    simpa only [add_comm] using h.tri243
  · change d 1 ≤ d 8+d 3
    simpa only [add_comm] using h.tri042
  · change d 4 ≤ d 8+d 6
    simpa only [add_comm] using h.tri142
  · change d 2 ≤ d 9+d 3
    simpa only [add_comm] using h.tri043
  · change d 5 ≤ d 9+d 6
    simpa only [add_comm] using h.tri143
  · change d 0 ≤ d 3+d 6
    simpa only [add_comm] using h.tri041
  · change d 7 ≤ d 1+d 2
    simpa only [add_comm] using h.tri203
  · change d 8 ≤ d 1+d 3
    simpa only [add_comm] using h.tri204
  · change d 4 ≤ d 1+d 0
    simpa only [add_comm] using h.tri102
  · change d 9 ≤ d 2+d 3
    simpa only [add_comm] using h.tri304
  · change d 5 ≤ d 2+d 0
    simpa only [add_comm] using h.tri103
  · change d 6 ≤ d 3+d 0
    simpa only [add_comm] using h.tri104
  · change d 7 ≤ d 4+d 5
    simpa only [add_comm] using h.tri213
  · change d 8 ≤ d 4+d 6
    simpa only [add_comm] using h.tri214
  · change d 1 ≤ d 4+d 0
    simpa only [add_comm] using h.tri012
  · change d 9 ≤ d 5+d 6
    simpa only [add_comm] using h.tri314
  · change d 2 ≤ d 5+d 0
    simpa only [add_comm] using h.tri013
  · change d 3 ≤ d 6+d 0
    simpa only [add_comm] using h.tri014
  · change d 7*d 3 ≤ d 8*d 2+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 8*d 2 ≤ d 7*d 3+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 1*d 9 ≤ d 7*d 3+d 8*d 2
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 7*d 6 ≤ d 8*d 5+d 4*d 9
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 8*d 5 ≤ d 7*d 6+d 4*d 9
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 4*d 9 ≤ d 7*d 6+d 8*d 5
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 7*d 0 ≤ d 1*d 5+d 4*d 2
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 1*d 5 ≤ d 7*d 0+d 4*d 2
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 4*d 2 ≤ d 7*d 0+d 1*d 5
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 8*d 0 ≤ d 1*d 6+d 4*d 3
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 1*d 6 ≤ d 8*d 0+d 4*d 3
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 4*d 3 ≤ d 8*d 0+d 1*d 6
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 9*d 0 ≤ d 2*d 6+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 2*d 6 ≤ d 9*d 0+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 5*d 3 ≤ d 9*d 0+d 2*d 6
    simpa only [mul_comm,add_comm] using h.pt8
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a3 a4 a0 a1 a2 h3 h4 h0 h1 h2
    change 4*a0*a1*d 7+4*a0*a2*d 8+4*a0*a3*d 1+4*a0*a4*d 4+4*a1*a2*d 9+4*a1*a3*d 2+4*a1*a4*d 5+4*a2*a3*d 3+4*a2*a4*d 6+4*a3*a4*d 0 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op20 (d:Fin 10→ℝ) : objective (p20 d)=objective d := by
  change d 8+d 2+d 6+d 1+d 5=d 1+d 5+d 8+d 2+d 6
  ring
def p21 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 7
 | 1 => d 5
 | 2 => d 2
 | 3 => d 9
 | 4 => d 4
 | 5 => d 1
 | 6 => d 8
 | 7 => d 0
 | 8 => d 6
 | 9 => d 3
theorem mp21 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p21 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 7
    · exact h.box 5
    · exact h.box 2
    · exact h.box 9
    · exact h.box 4
    · exact h.box 1
    · exact h.box 8
    · exact h.box 0
    · exact h.box 6
    · exact h.box 3
  · change d 4 ≤ d 7+d 5
    simpa only [add_comm] using h.tri132
  · change d 1 ≤ d 7+d 2
    simpa only [add_comm] using h.tri032
  · change d 8 ≤ d 7+d 9
    simpa only [add_comm] using h.tri234
  · change d 0 ≤ d 5+d 2
    simpa only [add_comm] using h.tri031
  · change d 6 ≤ d 5+d 9
    simpa only [add_comm] using h.tri134
  · change d 3 ≤ d 2+d 9
    simpa only [add_comm] using h.tri034
  · change d 5 ≤ d 7+d 4
    simpa only [add_comm] using h.tri123
  · change d 2 ≤ d 7+d 1
    simpa only [add_comm] using h.tri023
  · change d 9 ≤ d 7+d 8
    simpa only [add_comm] using h.tri324
  · change d 0 ≤ d 4+d 1
    simpa only [add_comm] using h.tri021
  · change d 6 ≤ d 4+d 8
    simpa only [add_comm] using h.tri124
  · change d 3 ≤ d 1+d 8
    simpa only [add_comm] using h.tri024
  · change d 7 ≤ d 5+d 4
    simpa only [add_comm] using h.tri213
  · change d 2 ≤ d 5+d 0
    simpa only [add_comm] using h.tri013
  · change d 9 ≤ d 5+d 6
    simpa only [add_comm] using h.tri314
  · change d 1 ≤ d 4+d 0
    simpa only [add_comm] using h.tri012
  · change d 8 ≤ d 4+d 6
    simpa only [add_comm] using h.tri214
  · change d 3 ≤ d 0+d 6
    simpa only [add_comm] using h.tri014
  · change d 7 ≤ d 2+d 1
    simpa only [add_comm] using h.tri203
  · change d 5 ≤ d 2+d 0
    simpa only [add_comm] using h.tri103
  · change d 9 ≤ d 2+d 3
    simpa only [add_comm] using h.tri304
  · change d 4 ≤ d 1+d 0
    simpa only [add_comm] using h.tri102
  · change d 8 ≤ d 1+d 3
    simpa only [add_comm] using h.tri204
  · change d 6 ≤ d 0+d 3
    simpa only [add_comm] using h.tri104
  · change d 7 ≤ d 9+d 8
    simpa only [add_comm] using h.tri243
  · change d 5 ≤ d 9+d 6
    simpa only [add_comm] using h.tri143
  · change d 2 ≤ d 9+d 3
    simpa only [add_comm] using h.tri043
  · change d 4 ≤ d 8+d 6
    simpa only [add_comm] using h.tri142
  · change d 1 ≤ d 8+d 3
    simpa only [add_comm] using h.tri042
  · change d 0 ≤ d 6+d 3
    simpa only [add_comm] using h.tri041
  · change d 7*d 0 ≤ d 5*d 1+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 5*d 1 ≤ d 7*d 0+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 2*d 4 ≤ d 7*d 0+d 5*d 1
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 7*d 6 ≤ d 5*d 8+d 9*d 4
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 5*d 8 ≤ d 7*d 6+d 9*d 4
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 9*d 4 ≤ d 7*d 6+d 5*d 8
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 7*d 3 ≤ d 2*d 8+d 9*d 1
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 2*d 8 ≤ d 7*d 3+d 9*d 1
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 9*d 1 ≤ d 7*d 3+d 2*d 8
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 5*d 3 ≤ d 2*d 6+d 9*d 0
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 2*d 6 ≤ d 5*d 3+d 9*d 0
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 9*d 0 ≤ d 5*d 3+d 2*d 6
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 4*d 3 ≤ d 1*d 6+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 1*d 6 ≤ d 4*d 3+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 8*d 0 ≤ d 4*d 3+d 1*d 6
    simpa only [mul_comm,add_comm] using h.pt3
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a3 a2 a1 a0 a4 h3 h2 h1 h0 h4
    change 4*a0*a1*d 7+4*a0*a2*d 5+4*a0*a3*d 2+4*a0*a4*d 9+4*a1*a2*d 4+4*a1*a3*d 1+4*a1*a4*d 8+4*a2*a3*d 0+4*a2*a4*d 6+4*a3*a4*d 3 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op21 (d:Fin 10→ℝ) : objective (p21 d)=objective d := by
  change d 5+d 1+d 6+d 2+d 8=d 1+d 5+d 8+d 2+d 6
  ring
def p30 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 9
 | 1 => d 2
 | 2 => d 5
 | 3 => d 7
 | 4 => d 3
 | 5 => d 6
 | 6 => d 8
 | 7 => d 0
 | 8 => d 1
 | 9 => d 4
theorem mp30 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p30 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 9
    · exact h.box 2
    · exact h.box 5
    · exact h.box 7
    · exact h.box 3
    · exact h.box 6
    · exact h.box 8
    · exact h.box 0
    · exact h.box 1
    · exact h.box 4
  · change d 3 ≤ d 9+d 2
    simpa only [add_comm] using h.tri034
  · change d 6 ≤ d 9+d 5
    simpa only [add_comm] using h.tri134
  · change d 8 ≤ d 9+d 7
    simpa only [add_comm] using h.tri234
  · change d 0 ≤ d 2+d 5
    simpa only [add_comm] using h.tri031
  · change d 1 ≤ d 2+d 7
    simpa only [add_comm] using h.tri032
  · change d 4 ≤ d 5+d 7
    simpa only [add_comm] using h.tri132
  · change d 2 ≤ d 9+d 3
    simpa only [add_comm] using h.tri043
  · change d 5 ≤ d 9+d 6
    simpa only [add_comm] using h.tri143
  · change d 7 ≤ d 9+d 8
    simpa only [add_comm] using h.tri243
  · change d 0 ≤ d 3+d 6
    simpa only [add_comm] using h.tri041
  · change d 1 ≤ d 3+d 8
    simpa only [add_comm] using h.tri042
  · change d 4 ≤ d 6+d 8
    simpa only [add_comm] using h.tri142
  · change d 9 ≤ d 2+d 3
    simpa only [add_comm] using h.tri304
  · change d 5 ≤ d 2+d 0
    simpa only [add_comm] using h.tri103
  · change d 7 ≤ d 2+d 1
    simpa only [add_comm] using h.tri203
  · change d 6 ≤ d 3+d 0
    simpa only [add_comm] using h.tri104
  · change d 8 ≤ d 3+d 1
    simpa only [add_comm] using h.tri204
  · change d 4 ≤ d 0+d 1
    simpa only [add_comm] using h.tri102
  · change d 9 ≤ d 5+d 6
    simpa only [add_comm] using h.tri314
  · change d 2 ≤ d 5+d 0
    simpa only [add_comm] using h.tri013
  · change d 7 ≤ d 5+d 4
    simpa only [add_comm] using h.tri213
  · change d 3 ≤ d 6+d 0
    simpa only [add_comm] using h.tri014
  · change d 8 ≤ d 6+d 4
    simpa only [add_comm] using h.tri214
  · change d 1 ≤ d 0+d 4
    simpa only [add_comm] using h.tri012
  · change d 9 ≤ d 7+d 8
    simpa only [add_comm] using h.tri324
  · change d 2 ≤ d 7+d 1
    simpa only [add_comm] using h.tri023
  · change d 5 ≤ d 7+d 4
    simpa only [add_comm] using h.tri123
  · change d 3 ≤ d 8+d 1
    simpa only [add_comm] using h.tri024
  · change d 6 ≤ d 8+d 4
    simpa only [add_comm] using h.tri124
  · change d 0 ≤ d 1+d 4
    simpa only [add_comm] using h.tri021
  · change d 9*d 0 ≤ d 2*d 6+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 2*d 6 ≤ d 9*d 0+d 5*d 3
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 5*d 3 ≤ d 9*d 0+d 2*d 6
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 9*d 1 ≤ d 2*d 8+d 7*d 3
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 2*d 8 ≤ d 9*d 1+d 7*d 3
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 7*d 3 ≤ d 9*d 1+d 2*d 8
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 9*d 4 ≤ d 5*d 8+d 7*d 6
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 5*d 8 ≤ d 9*d 4+d 7*d 6
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 7*d 6 ≤ d 9*d 4+d 5*d 8
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 2*d 4 ≤ d 5*d 1+d 7*d 0
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 5*d 1 ≤ d 2*d 4+d 7*d 0
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 7*d 0 ≤ d 2*d 4+d 5*d 1
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 3*d 4 ≤ d 6*d 1+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 6*d 1 ≤ d 3*d 4+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 8*d 0 ≤ d 3*d 4+d 6*d 1
    simpa only [mul_comm,add_comm] using h.pt3
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a2 a3 a4 a0 a1 h2 h3 h4 h0 h1
    change 4*a0*a1*d 9+4*a0*a2*d 2+4*a0*a3*d 5+4*a0*a4*d 7+4*a1*a2*d 3+4*a1*a3*d 6+4*a1*a4*d 8+4*a2*a3*d 0+4*a2*a4*d 1+4*a3*a4*d 4 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op30 (d:Fin 10→ℝ) : objective (p30 d)=objective d := by
  change d 2+d 6+d 1+d 5+d 8=d 1+d 5+d 8+d 2+d 6
  ring
def p31 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 9
 | 1 => d 8
 | 2 => d 6
 | 3 => d 3
 | 4 => d 7
 | 5 => d 5
 | 6 => d 2
 | 7 => d 4
 | 8 => d 1
 | 9 => d 0
theorem mp31 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p31 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 9
    · exact h.box 8
    · exact h.box 6
    · exact h.box 3
    · exact h.box 7
    · exact h.box 5
    · exact h.box 2
    · exact h.box 4
    · exact h.box 1
    · exact h.box 0
  · change d 7 ≤ d 9+d 8
    simpa only [add_comm] using h.tri243
  · change d 5 ≤ d 9+d 6
    simpa only [add_comm] using h.tri143
  · change d 2 ≤ d 9+d 3
    simpa only [add_comm] using h.tri043
  · change d 4 ≤ d 8+d 6
    simpa only [add_comm] using h.tri142
  · change d 1 ≤ d 8+d 3
    simpa only [add_comm] using h.tri042
  · change d 0 ≤ d 6+d 3
    simpa only [add_comm] using h.tri041
  · change d 8 ≤ d 9+d 7
    simpa only [add_comm] using h.tri234
  · change d 6 ≤ d 9+d 5
    simpa only [add_comm] using h.tri134
  · change d 3 ≤ d 9+d 2
    simpa only [add_comm] using h.tri034
  · change d 4 ≤ d 7+d 5
    simpa only [add_comm] using h.tri132
  · change d 1 ≤ d 7+d 2
    simpa only [add_comm] using h.tri032
  · change d 0 ≤ d 5+d 2
    simpa only [add_comm] using h.tri031
  · change d 9 ≤ d 8+d 7
    simpa only [add_comm] using h.tri324
  · change d 6 ≤ d 8+d 4
    simpa only [add_comm] using h.tri124
  · change d 3 ≤ d 8+d 1
    simpa only [add_comm] using h.tri024
  · change d 5 ≤ d 7+d 4
    simpa only [add_comm] using h.tri123
  · change d 2 ≤ d 7+d 1
    simpa only [add_comm] using h.tri023
  · change d 0 ≤ d 4+d 1
    simpa only [add_comm] using h.tri021
  · change d 9 ≤ d 6+d 5
    simpa only [add_comm] using h.tri314
  · change d 8 ≤ d 6+d 4
    simpa only [add_comm] using h.tri214
  · change d 3 ≤ d 6+d 0
    simpa only [add_comm] using h.tri014
  · change d 7 ≤ d 5+d 4
    simpa only [add_comm] using h.tri213
  · change d 2 ≤ d 5+d 0
    simpa only [add_comm] using h.tri013
  · change d 1 ≤ d 4+d 0
    simpa only [add_comm] using h.tri012
  · change d 9 ≤ d 3+d 2
    simpa only [add_comm] using h.tri304
  · change d 8 ≤ d 3+d 1
    simpa only [add_comm] using h.tri204
  · change d 6 ≤ d 3+d 0
    simpa only [add_comm] using h.tri104
  · change d 7 ≤ d 2+d 1
    simpa only [add_comm] using h.tri203
  · change d 5 ≤ d 2+d 0
    simpa only [add_comm] using h.tri103
  · change d 4 ≤ d 1+d 0
    simpa only [add_comm] using h.tri102
  · change d 9*d 4 ≤ d 8*d 5+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 8*d 5 ≤ d 9*d 4+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 6*d 7 ≤ d 9*d 4+d 8*d 5
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 9*d 1 ≤ d 8*d 2+d 3*d 7
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 8*d 2 ≤ d 9*d 1+d 3*d 7
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 3*d 7 ≤ d 9*d 1+d 8*d 2
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 9*d 0 ≤ d 6*d 2+d 3*d 5
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 6*d 2 ≤ d 9*d 0+d 3*d 5
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 3*d 5 ≤ d 9*d 0+d 6*d 2
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 8*d 0 ≤ d 6*d 1+d 3*d 4
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 6*d 1 ≤ d 8*d 0+d 3*d 4
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 3*d 4 ≤ d 8*d 0+d 6*d 1
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 7*d 0 ≤ d 5*d 1+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 5*d 1 ≤ d 7*d 0+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 2*d 4 ≤ d 7*d 0+d 5*d 1
    simpa only [mul_comm,add_comm] using h.pt2
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a4 a3 a2 a1 a0 h4 h3 h2 h1 h0
    change 4*a0*a1*d 9+4*a0*a2*d 8+4*a0*a3*d 6+4*a0*a4*d 3+4*a1*a2*d 7+4*a1*a3*d 5+4*a1*a4*d 2+4*a2*a3*d 4+4*a2*a4*d 1+4*a3*a4*d 0 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op31 (d:Fin 10→ℝ) : objective (p31 d)=objective d := by
  change d 8+d 5+d 1+d 6+d 2=d 1+d 5+d 8+d 2+d 6
  ring
def p40 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 3
 | 1 => d 6
 | 2 => d 8
 | 3 => d 9
 | 4 => d 0
 | 5 => d 1
 | 6 => d 2
 | 7 => d 4
 | 8 => d 5
 | 9 => d 7
theorem mp40 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p40 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 3
    · exact h.box 6
    · exact h.box 8
    · exact h.box 9
    · exact h.box 0
    · exact h.box 1
    · exact h.box 2
    · exact h.box 4
    · exact h.box 5
    · exact h.box 7
  · change d 0 ≤ d 3+d 6
    simpa only [add_comm] using h.tri041
  · change d 1 ≤ d 3+d 8
    simpa only [add_comm] using h.tri042
  · change d 2 ≤ d 3+d 9
    simpa only [add_comm] using h.tri043
  · change d 4 ≤ d 6+d 8
    simpa only [add_comm] using h.tri142
  · change d 5 ≤ d 6+d 9
    simpa only [add_comm] using h.tri143
  · change d 7 ≤ d 8+d 9
    simpa only [add_comm] using h.tri243
  · change d 6 ≤ d 3+d 0
    simpa only [add_comm] using h.tri104
  · change d 8 ≤ d 3+d 1
    simpa only [add_comm] using h.tri204
  · change d 9 ≤ d 3+d 2
    simpa only [add_comm] using h.tri304
  · change d 4 ≤ d 0+d 1
    simpa only [add_comm] using h.tri102
  · change d 5 ≤ d 0+d 2
    simpa only [add_comm] using h.tri103
  · change d 7 ≤ d 1+d 2
    simpa only [add_comm] using h.tri203
  · change d 3 ≤ d 6+d 0
    simpa only [add_comm] using h.tri014
  · change d 8 ≤ d 6+d 4
    simpa only [add_comm] using h.tri214
  · change d 9 ≤ d 6+d 5
    simpa only [add_comm] using h.tri314
  · change d 1 ≤ d 0+d 4
    simpa only [add_comm] using h.tri012
  · change d 2 ≤ d 0+d 5
    simpa only [add_comm] using h.tri013
  · change d 7 ≤ d 4+d 5
    simpa only [add_comm] using h.tri213
  · change d 3 ≤ d 8+d 1
    simpa only [add_comm] using h.tri024
  · change d 6 ≤ d 8+d 4
    simpa only [add_comm] using h.tri124
  · change d 9 ≤ d 8+d 7
    simpa only [add_comm] using h.tri324
  · change d 0 ≤ d 1+d 4
    simpa only [add_comm] using h.tri021
  · change d 2 ≤ d 1+d 7
    simpa only [add_comm] using h.tri023
  · change d 5 ≤ d 4+d 7
    simpa only [add_comm] using h.tri123
  · change d 3 ≤ d 9+d 2
    simpa only [add_comm] using h.tri034
  · change d 6 ≤ d 9+d 5
    simpa only [add_comm] using h.tri134
  · change d 8 ≤ d 9+d 7
    simpa only [add_comm] using h.tri234
  · change d 0 ≤ d 2+d 5
    simpa only [add_comm] using h.tri031
  · change d 1 ≤ d 2+d 7
    simpa only [add_comm] using h.tri032
  · change d 4 ≤ d 5+d 7
    simpa only [add_comm] using h.tri132
  · change d 3*d 4 ≤ d 6*d 1+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 6*d 1 ≤ d 3*d 4+d 8*d 0
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 8*d 0 ≤ d 3*d 4+d 6*d 1
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 3*d 5 ≤ d 6*d 2+d 9*d 0
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 6*d 2 ≤ d 3*d 5+d 9*d 0
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 9*d 0 ≤ d 3*d 5+d 6*d 2
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 3*d 7 ≤ d 8*d 2+d 9*d 1
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 8*d 2 ≤ d 3*d 7+d 9*d 1
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 9*d 1 ≤ d 3*d 7+d 8*d 2
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 6*d 7 ≤ d 8*d 5+d 9*d 4
    simpa only [mul_comm,add_comm] using h.pt14
  · change d 8*d 5 ≤ d 6*d 7+d 9*d 4
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 9*d 4 ≤ d 6*d 7+d 8*d 5
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 0*d 7 ≤ d 1*d 5+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 1*d 5 ≤ d 0*d 7+d 2*d 4
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 2*d 4 ≤ d 0*d 7+d 1*d 5
    simpa only [mul_comm,add_comm] using h.pt2
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a1 a2 a3 a4 a0 h1 h2 h3 h4 h0
    change 4*a0*a1*d 3+4*a0*a2*d 6+4*a0*a3*d 8+4*a0*a4*d 9+4*a1*a2*d 0+4*a1*a3*d 1+4*a1*a4*d 2+4*a2*a3*d 4+4*a2*a4*d 5+4*a3*a4*d 7 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op40 (d:Fin 10→ℝ) : objective (p40 d)=objective d := by
  change d 6+d 1+d 5+d 8+d 2=d 1+d 5+d 8+d 2+d 6
  ring
def p41 (d:Fin 10→ℝ) : Fin 10→ℝ
 | 0 => d 3
 | 1 => d 2
 | 2 => d 1
 | 3 => d 0
 | 4 => d 9
 | 5 => d 8
 | 6 => d 6
 | 7 => d 7
 | 8 => d 5
 | 9 => d 4
theorem mp41 (d:Fin 10→ℝ) (h:MetricRows d) : MetricRows (p41 d) := by
  constructor
  · intro j
    fin_cases j
    · exact h.box 3
    · exact h.box 2
    · exact h.box 1
    · exact h.box 0
    · exact h.box 9
    · exact h.box 8
    · exact h.box 6
    · exact h.box 7
    · exact h.box 5
    · exact h.box 4
  · change d 9 ≤ d 3+d 2
    simpa only [add_comm] using h.tri304
  · change d 8 ≤ d 3+d 1
    simpa only [add_comm] using h.tri204
  · change d 6 ≤ d 3+d 0
    simpa only [add_comm] using h.tri104
  · change d 7 ≤ d 2+d 1
    simpa only [add_comm] using h.tri203
  · change d 5 ≤ d 2+d 0
    simpa only [add_comm] using h.tri103
  · change d 4 ≤ d 1+d 0
    simpa only [add_comm] using h.tri102
  · change d 2 ≤ d 3+d 9
    simpa only [add_comm] using h.tri043
  · change d 1 ≤ d 3+d 8
    simpa only [add_comm] using h.tri042
  · change d 0 ≤ d 3+d 6
    simpa only [add_comm] using h.tri041
  · change d 7 ≤ d 9+d 8
    simpa only [add_comm] using h.tri243
  · change d 5 ≤ d 9+d 6
    simpa only [add_comm] using h.tri143
  · change d 4 ≤ d 8+d 6
    simpa only [add_comm] using h.tri142
  · change d 3 ≤ d 2+d 9
    simpa only [add_comm] using h.tri034
  · change d 1 ≤ d 2+d 7
    simpa only [add_comm] using h.tri032
  · change d 0 ≤ d 2+d 5
    simpa only [add_comm] using h.tri031
  · change d 8 ≤ d 9+d 7
    simpa only [add_comm] using h.tri234
  · change d 6 ≤ d 9+d 5
    simpa only [add_comm] using h.tri134
  · change d 4 ≤ d 7+d 5
    simpa only [add_comm] using h.tri132
  · change d 3 ≤ d 1+d 8
    simpa only [add_comm] using h.tri024
  · change d 2 ≤ d 1+d 7
    simpa only [add_comm] using h.tri023
  · change d 0 ≤ d 1+d 4
    simpa only [add_comm] using h.tri021
  · change d 9 ≤ d 8+d 7
    simpa only [add_comm] using h.tri324
  · change d 6 ≤ d 8+d 4
    simpa only [add_comm] using h.tri124
  · change d 5 ≤ d 7+d 4
    simpa only [add_comm] using h.tri123
  · change d 3 ≤ d 0+d 6
    simpa only [add_comm] using h.tri014
  · change d 2 ≤ d 0+d 5
    simpa only [add_comm] using h.tri013
  · change d 1 ≤ d 0+d 4
    simpa only [add_comm] using h.tri012
  · change d 9 ≤ d 6+d 5
    simpa only [add_comm] using h.tri314
  · change d 8 ≤ d 6+d 4
    simpa only [add_comm] using h.tri214
  · change d 7 ≤ d 5+d 4
    simpa only [add_comm] using h.tri213
  · change d 3*d 7 ≤ d 2*d 8+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt11
  · change d 2*d 8 ≤ d 3*d 7+d 1*d 9
    simpa only [mul_comm,add_comm] using h.pt10
  · change d 1*d 9 ≤ d 3*d 7+d 2*d 8
    simpa only [mul_comm,add_comm] using h.pt9
  · change d 3*d 5 ≤ d 2*d 6+d 0*d 9
    simpa only [mul_comm,add_comm] using h.pt8
  · change d 2*d 6 ≤ d 3*d 5+d 0*d 9
    simpa only [mul_comm,add_comm] using h.pt7
  · change d 0*d 9 ≤ d 3*d 5+d 2*d 6
    simpa only [mul_comm,add_comm] using h.pt6
  · change d 3*d 4 ≤ d 1*d 6+d 0*d 8
    simpa only [mul_comm,add_comm] using h.pt5
  · change d 1*d 6 ≤ d 3*d 4+d 0*d 8
    simpa only [mul_comm,add_comm] using h.pt4
  · change d 0*d 8 ≤ d 3*d 4+d 1*d 6
    simpa only [mul_comm,add_comm] using h.pt3
  · change d 2*d 4 ≤ d 1*d 5+d 0*d 7
    simpa only [mul_comm,add_comm] using h.pt2
  · change d 1*d 5 ≤ d 2*d 4+d 0*d 7
    simpa only [mul_comm,add_comm] using h.pt1
  · change d 0*d 7 ≤ d 2*d 4+d 1*d 5
    simpa only [mul_comm,add_comm] using h.pt0
  · change d 9*d 4 ≤ d 8*d 5+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt12
  · change d 8*d 5 ≤ d 9*d 4+d 6*d 7
    simpa only [mul_comm,add_comm] using h.pt13
  · change d 6*d 7 ≤ d 9*d 4+d 8*d 5
    simpa only [mul_comm,add_comm] using h.pt14
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    have pr := h.cp a0 a4 a3 a2 a1 h0 h4 h3 h2 h1
    change 4*a0*a1*d 3+4*a0*a2*d 2+4*a0*a3*d 1+4*a0*a4*d 0+4*a1*a2*d 9+4*a1*a3*d 8+4*a1*a4*d 6+4*a2*a3*d 7+4*a2*a4*d 5+4*a3*a4*d 4 ≤ (a0+a1+a2+a3+a4)^2
    convert pr using 1 <;> ring
theorem op41 (d:Fin 10→ℝ) : objective (p41 d)=objective d := by
  change d 2+d 8+d 5+d 1+d 6=d 1+d 5+d 8+d 2+d 6
  ring
def dihedralMap : Fin 10 → (Fin 10→ℝ) → Fin 10→ℝ
 | 0 => p00
 | 1 => p01
 | 2 => p10
 | 3 => p11
 | 4 => p20
 | 5 => p21
 | 6 => p30
 | 7 => p31
 | 8 => p40
 | 9 => p41
def Dihedral (d e : Fin 10→ℝ) : Prop := ∃ k, e=dihedralMap k d
theorem normalization_exists (d:Fin 10→ℝ) (h:MetricRows d) :
 ∃ e, Dihedral d e ∧ MetricRows e ∧ Normalization e ∧ objective e=objective d := by
  rcases least5 (d 0) (d 4) (d 7) (d 9) (d 3) with q0|q1|q2|q3|q4
  · rcases q0 with ⟨m1, m2, m3, m4⟩
    rcases le_total (d 4) (d 3) with ord|ord
    · have hN : Normalization (p00 d) := ⟨m1, m2, m3, m4, ord⟩
      exact ⟨p00 d,⟨0,rfl⟩,mp00 d h,hN,op00 d⟩
    · have hN : Normalization (p01 d) := ⟨m4, m3, m2, m1, ord⟩
      exact ⟨p01 d,⟨1,rfl⟩,mp01 d h,hN,op01 d⟩
  · rcases q1 with ⟨m0, m2, m3, m4⟩
    rcases le_total (d 7) (d 0) with ord|ord
    · have hN : Normalization (p10 d) := ⟨m2, m3, m4, m0, ord⟩
      exact ⟨p10 d,⟨2,rfl⟩,mp10 d h,hN,op10 d⟩
    · have hN : Normalization (p11 d) := ⟨m0, m4, m3, m2, ord⟩
      exact ⟨p11 d,⟨3,rfl⟩,mp11 d h,hN,op11 d⟩
  · rcases q2 with ⟨m0, m1, m3, m4⟩
    rcases le_total (d 9) (d 4) with ord|ord
    · have hN : Normalization (p20 d) := ⟨m3, m4, m0, m1, ord⟩
      exact ⟨p20 d,⟨4,rfl⟩,mp20 d h,hN,op20 d⟩
    · have hN : Normalization (p21 d) := ⟨m1, m0, m4, m3, ord⟩
      exact ⟨p21 d,⟨5,rfl⟩,mp21 d h,hN,op21 d⟩
  · rcases q3 with ⟨m0, m1, m2, m4⟩
    rcases le_total (d 3) (d 7) with ord|ord
    · have hN : Normalization (p30 d) := ⟨m4, m0, m1, m2, ord⟩
      exact ⟨p30 d,⟨6,rfl⟩,mp30 d h,hN,op30 d⟩
    · have hN : Normalization (p31 d) := ⟨m2, m1, m0, m4, ord⟩
      exact ⟨p31 d,⟨7,rfl⟩,mp31 d h,hN,op31 d⟩
  · rcases q4 with ⟨m0, m1, m2, m3⟩
    rcases le_total (d 0) (d 9) with ord|ord
    · have hN : Normalization (p40 d) := ⟨m0, m1, m2, m3, ord⟩
      exact ⟨p40 d,⟨8,rfl⟩,mp40 d h,hN,op40 d⟩
    · have hN : Normalization (p41 d) := ⟨m3, m2, m1, m0, ord⟩
      exact ⟨p41 d,⟨9,rfl⟩,mp41 d h,hN,op41 d⟩
theorem objective_le (d:Fin 10→ℝ) (h:MetricRows d) : objective d ≤ (49:ℝ)/12 := by
  obtain ⟨e,_,he,nn,eq⟩ := normalization_exists d h
  rw [← eq]
  exact objective_le_normalized e he nn
theorem collapse_at_equality (d:Fin 10→ℝ) (h:MetricRows d) (eq : objective d=(49:ℝ)/12) :
 ∃ e f, Dihedral d e ∧ Dihedral e f ∧ MetricRows f ∧ objective f=(49:ℝ)/12 ∧ f 4=0 ∧ f 9=0 := by
  obtain ⟨e,de,he,nn,eqe⟩ := normalization_exists d h
  have maximal := eqe.trans eq
  obtain ⟨c,hc⟩ := finite_cover_normalized e he nn (le_of_eq maximal.symm)
  fin_cases c
  · obtain ⟨s,t⟩ := (local0 e he hc).2 (le_of_eq maximal.symm)
    exact ⟨e,p00 e,de,⟨0,rfl⟩,mp00 e he,(op00 e).trans maximal,s,t⟩
  · obtain ⟨s,t⟩ := (local1 e he hc).2 (le_of_eq maximal.symm)
    exact ⟨e,p10 e,de,⟨2,rfl⟩,mp10 e he,(op10 e).trans maximal,s,t⟩
  · obtain ⟨s,t⟩ := (local2 e he hc).2 (le_of_eq maximal.symm)
    exact ⟨e,p20 e,de,⟨4,rfl⟩,mp20 e he,(op20 e).trans maximal,s,t⟩
  · obtain ⟨s,t⟩ := (local3 e he hc).2 (le_of_eq maximal.symm)
    exact ⟨e,p30 e,de,⟨6,rfl⟩,mp30 e he,(op30 e).trans maximal,s,t⟩
  · obtain ⟨s,t⟩ := (local4 e he hc).2 (le_of_eq maximal.symm)
    exact ⟨e,p40 e,de,⟨8,rfl⟩,mp40 e he,(op40 e).trans maximal,s,t⟩
#print axioms objective_le
end C5Certificate
