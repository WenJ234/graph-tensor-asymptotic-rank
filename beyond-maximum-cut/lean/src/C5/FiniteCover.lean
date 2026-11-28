import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace C5Certificate
set_option maxHeartbeats 0
set_option maxRecDepth 4096
private theorem plane_ll {x y u v : ℝ} (hx : u ≤ x) (hy : v ≤ y) :
  v*x+u*y-u*v ≤ x*y := by
  have p := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  nlinarith only [p]
private theorem plane_hh {x y u v : ℝ} (hx : x ≤ u) (hy : y ≤ v) :
  v*x+u*y-u*v ≤ x*y := by
  have p := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  nlinarith only [p]
private theorem plane_lh {x y u v : ℝ} (hx : u ≤ x) (hy : y ≤ v) :
  x*y ≤ v*x+u*y-u*v := by
  have p := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  nlinarith only [p]
private theorem plane_hl {x y u v : ℝ} (hx : x ≤ u) (hy : v ≤ y) :
  x*y ≤ v*x+u*y-u*v := by
  have p := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  nlinarith only [p]
def objective (d : Fin 10 → ℝ) : ℝ := d 1 + d 5 + d 8 + d 2 + d 6
structure MetricRows (d : Fin 10 → ℝ) : Prop where
  box : ∀ i, 0 ≤ d i ∧ d i ≤ 1
  tri102 : d 4 ≤ d 0 + d 1
  tri103 : d 5 ≤ d 0 + d 2
  tri104 : d 6 ≤ d 0 + d 3
  tri203 : d 7 ≤ d 1 + d 2
  tri204 : d 8 ≤ d 1 + d 3
  tri304 : d 9 ≤ d 2 + d 3
  tri012 : d 1 ≤ d 0 + d 4
  tri013 : d 2 ≤ d 0 + d 5
  tri014 : d 3 ≤ d 0 + d 6
  tri213 : d 7 ≤ d 4 + d 5
  tri214 : d 8 ≤ d 4 + d 6
  tri314 : d 9 ≤ d 5 + d 6
  tri021 : d 0 ≤ d 1 + d 4
  tri023 : d 2 ≤ d 1 + d 7
  tri024 : d 3 ≤ d 1 + d 8
  tri123 : d 5 ≤ d 4 + d 7
  tri124 : d 6 ≤ d 4 + d 8
  tri324 : d 9 ≤ d 7 + d 8
  tri031 : d 0 ≤ d 2 + d 5
  tri032 : d 1 ≤ d 2 + d 7
  tri034 : d 3 ≤ d 2 + d 9
  tri132 : d 4 ≤ d 5 + d 7
  tri134 : d 6 ≤ d 5 + d 9
  tri234 : d 8 ≤ d 7 + d 9
  tri041 : d 0 ≤ d 3 + d 6
  tri042 : d 1 ≤ d 3 + d 8
  tri043 : d 2 ≤ d 3 + d 9
  tri142 : d 4 ≤ d 6 + d 8
  tri143 : d 5 ≤ d 6 + d 9
  tri243 : d 7 ≤ d 8 + d 9
  pt0 : d 0*d 7 ≤ d 1*d 5+d 2*d 4
  pt1 : d 1*d 5 ≤ d 0*d 7+d 2*d 4
  pt2 : d 2*d 4 ≤ d 0*d 7+d 1*d 5
  pt3 : d 0*d 8 ≤ d 1*d 6+d 3*d 4
  pt4 : d 1*d 6 ≤ d 0*d 8+d 3*d 4
  pt5 : d 3*d 4 ≤ d 0*d 8+d 1*d 6
  pt6 : d 0*d 9 ≤ d 2*d 6+d 3*d 5
  pt7 : d 2*d 6 ≤ d 0*d 9+d 3*d 5
  pt8 : d 3*d 5 ≤ d 0*d 9+d 2*d 6
  pt9 : d 1*d 9 ≤ d 2*d 8+d 3*d 7
  pt10 : d 2*d 8 ≤ d 1*d 9+d 3*d 7
  pt11 : d 3*d 7 ≤ d 1*d 9+d 2*d 8
  pt12 : d 4*d 9 ≤ d 5*d 8+d 6*d 7
  pt13 : d 5*d 8 ≤ d 4*d 9+d 6*d 7
  pt14 : d 6*d 7 ≤ d 4*d 9+d 5*d 8
  cp : ∀ a0 a1 a2 a3 a4 : ℝ, 0≤a0 → 0≤a1 → 0≤a2 → 0≤a3 → 0≤a4 →
    4*a0*a1*d 0 + 4*a0*a2*d 1 + 4*a0*a3*d 2 + 4*a0*a4*d 3 + 4*a1*a2*d 4 + 4*a1*a3*d 5 + 4*a1*a4*d 6 + 4*a2*a3*d 7 + 4*a2*a4*d 8 + 4*a3*a4*d 9 ≤ (a0+a1+a2+a3+a4)^2
structure Normalization (d : Fin 10 → ℝ) : Prop where
  s01 : d 0 ≤ d 4
  s02 : d 0 ≤ d 7
  s03 : d 0 ≤ d 9
  s04 : d 0 ≤ d 3
  s14 : d 4 ≤ d 3
def LocalAt (d : Fin 10 → ℝ) : Fin 5 → Prop
  | 0 => (4*d 2<3*(d 0+d 1)) ∧ (4*d 2<3*(d 5+d 7)) ∧ (4*d 3<3*(d 0+d 1)) ∧ (4*d 3<3*(d 6+d 8)) ∧ (4*d 1<3*(d 3+d 2)) ∧ (4*d 1<3*(d 8+d 7))
  | 1 => (4*d 6<3*(d 4+d 5)) ∧ (4*d 6<3*(d 8+d 9)) ∧ (4*d 0<3*(d 4+d 5)) ∧ (4*d 0<3*(d 1+d 2)) ∧ (4*d 5<3*(d 0+d 6)) ∧ (4*d 5<3*(d 2+d 9))
  | 2 => (4*d 1<3*(d 7+d 8)) ∧ (4*d 1<3*(d 2+d 3)) ∧ (4*d 4<3*(d 7+d 8)) ∧ (4*d 4<3*(d 5+d 6)) ∧ (4*d 8<3*(d 4+d 1)) ∧ (4*d 8<3*(d 6+d 3))
  | 3 => (4*d 5<3*(d 9+d 2)) ∧ (4*d 5<3*(d 6+d 0)) ∧ (4*d 7<3*(d 9+d 2)) ∧ (4*d 7<3*(d 8+d 1)) ∧ (4*d 2<3*(d 7+d 5)) ∧ (4*d 2<3*(d 1+d 0))
  | 4 => (4*d 8<3*(d 3+d 6)) ∧ (4*d 8<3*(d 1+d 4)) ∧ (4*d 9<3*(d 3+d 6)) ∧ (4*d 9<3*(d 2+d 5)) ∧ (4*d 6<3*(d 9+d 8)) ∧ (4*d 6<3*(d 5+d 4))
theorem finite_cover_normalized (d : Fin 10 → ℝ) (h : MetricRows d) (hN : Normalization d)
    (large : (49:ℝ)/12 ≤ objective d) : ∃ c : Fin 5, LocalAt d c := by
  have target := large
  unfold objective at target
  have b0_0 := (h.box 0).1
  have b1_0 := (h.box 0).2
  have b0_1 := (h.box 1).1
  have b1_1 := (h.box 1).2
  have b0_2 := (h.box 2).1
  have b1_2 := (h.box 2).2
  have b0_3 := (h.box 3).1
  have b1_3 := (h.box 3).2
  have b0_4 := (h.box 4).1
  have b1_4 := (h.box 4).2
  have b0_5 := (h.box 5).1
  have b1_5 := (h.box 5).2
  have b0_6 := (h.box 6).1
  have b1_6 := (h.box 6).2
  have b0_7 := (h.box 7).1
  have b1_7 := (h.box 7).2
  have b0_8 := (h.box 8).1
  have b1_8 := (h.box 8).2
  have b0_9 := (h.box 9).1
  have b1_9 := (h.box 9).2
  by_cases m1 : d 0 ≤ ((1:ℝ)/2)
  ·
    by_cases m2 : d 3 ≤ ((1:ℝ)/2)
    ·
      by_cases m3 : d 9 ≤ ((1:ℝ)/2)
      ·
        by_cases m4 : d 7 ≤ ((1:ℝ)/2)
        ·
          have tst0 : 4*d 2<3*(d 0+d 1) := by
            apply lt_of_not_ge
            intro outside
            have r0 : ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [h.tri123]
            have r1 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
            have r2cp := h.cp 2 3 1 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r2 : 24 * d 0 + 8 * d 1 + 24 * d 2 + 8 * d 3 + 12 * d 4 + 36 * d 5 + 12 * d 6 + 12 * d 7 + 4 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r2cp]
            have r3cp := h.cp 2164 2164 1374 2923 1374 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r3 : 18731584 * d 0 + 11893344 * d 1 + 25301488 * d 2 + 11893344 * d 3 + 11893344 * d 4 + 25301488 * d 5 + 11893344 * d 6 + 16064808 * d 7 + 7551504 * d 8 + 16064808 * d 9 ≤ 99980001 := by linarith only [r3cp]
            have r4pt0 := plane_hh b1_1 b1_5
            have r4pt1 := plane_lh b0_0 m4
            have r4pt2 := plane_hl b1_2 b0_4
            have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ 1 := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
            have r5pt0 := plane_hh b1_2 b1_6
            have r5pt1 := plane_lh b0_0 m3
            have r5pt2 := plane_hl m2 b0_5
            have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/2) * d 5 + 1 * d 6 ≤ 1 := by linarith only [h.pt7, r5pt0, r5pt1, r5pt2]
            have r6pt0 := plane_hh b1_2 b1_8
            have r6pt1 := plane_hl b1_1 b0_9
            have r6pt2 := plane_hl m2 b0_7
            have r6 : 1 * d 2 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 1 := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
            have r7pt0 := plane_hh b1_5 b1_8
            have r7pt1 := plane_lh b0_4 m3
            have r7pt2 := plane_lh b0_6 m4
            have r7 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + 1 * d 8 ≤ 1 := by linarith only [h.pt13, r7pt0, r7pt1, r7pt2]
            have r8 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have r9 : 3 * d 0 + 3 * d 1 + ((-4:ℝ)/1) * d 2 ≤ 0 := by linarith only [outside]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤84781151705799128514560 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤716763302564402982551552 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤9038944846695979024384 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤3803031150527695 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤378768336229686919036928 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤1301474323383054564851712 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤169562303411598257029120 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤813823821010420711292928 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤87355042396178124636160 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤183983285344980357349376 by norm_num)))
            have aggregated : ((-10092096:ℝ)/1) * d 0 + ((-14191712:ℝ)/1) * d 1 + 62144784 * d 2 + ((-599220986074893492194400:ℝ)/1) * d 3 + ((-14191712:ℝ)/1) * d 4 + ((-105627376:ℝ)/1) * d 5 + 120026016 * d 6 + 10121048 * d 7 + ((-120311056:ℝ)/1) * d 8 + 10121048 * d 9 ≤ ((-332646750475579655895057:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, m1, b1_1, b0_2, m2, b1_4, b1_5, b0_6, b0_7, b1_8, b0_9]
          have tst1 : 4*d 2<3*(d 5+d 7) := by
            apply lt_of_not_ge
            intro outside
            have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
            have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
            have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
            have r3cp := h.cp 3 1 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r3 : 12 * d 0 + 36 * d 1 + 24 * d 2 + 12 * d 3 + 12 * d 4 + 8 * d 5 + 4 * d 6 + 24 * d 7 + 12 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r3cp]
            have r4pt0 := plane_hh b1_1 b1_5
            have r4pt1 := plane_hl m1 b0_7
            have r4pt2 := plane_hl b1_2 b0_4
            have r4 : 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ 1 := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
            have r5pt0 := plane_hh b1_2 b1_6
            have r5pt1 := plane_lh b0_0 m3
            have r5pt2 := plane_hl m2 b0_5
            have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/2) * d 5 + 1 * d 6 ≤ 1 := by linarith only [h.pt7, r5pt0, r5pt1, r5pt2]
            have r6pt0 := plane_hh b1_2 b1_8
            have r6pt1 := plane_lh b0_1 m3
            have r6pt2 := plane_hl m2 b0_7
            have r6 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-1:ℝ)/2) * d 7 + 1 * d 8 ≤ 1 := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
            have r7pt0 := plane_hh b1_2 b1_8
            have r7pt1 := plane_hl b1_1 b0_9
            have r7pt2 := plane_hl m2 b0_7
            have r7 : 1 * d 2 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 1 := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
            have r8 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have r9 : ((-4:ℝ)/1) * d 2 + 3 * d 5 + 3 * d 7 ≤ 0 := by linarith only [outside]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤125227637024989712 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤250455274049979328 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤264369455941644736 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤6957090945832757 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤222626910266648096 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤417425456749965440 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤306112001616641344 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤55656727566662064 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤37104485044441376 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤125227637024989632 by norm_num)))
            have aggregated : ((-20:ℝ)/1) * d 0 + ((-124:ℝ)/1) * d 1 + ((-24:ℝ)/1) * d 2 + ((-180884364591651652:ℝ)/1) * d 3 + 12 * d 4 + ((-184:ℝ)/1) * d 5 + ((-44:ℝ)/1) * d 6 + ((-16:ℝ)/1) * d 7 + ((-20:ℝ)/1) * d 8 + ((-8:ℝ)/1) * d 9 ≤ ((-120589576394434780:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, m1, b1_1, b1_2, m2, b0_4, b1_5, b1_6, m4, b1_8, m3]
          have tst2 : 4*d 3<3*(d 0+d 1) := by
            apply lt_of_not_ge
            intro outside
            have r0 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
            have r1 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
            have r2pt0 := plane_hh b1_2 b1_6
            have r2pt1 := plane_lh b0_0 m3
            have r2pt2 := plane_lh b0_3 b1_5
            have r2 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 1 := by linarith only [h.pt7, r2pt0, r2pt1, r2pt2]
            have r3pt0 := plane_hh b1_5 b1_8
            have r3pt1 := plane_lh b0_4 m3
            have r3pt2 := plane_lh b0_6 m4
            have r3 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + 1 * d 8 ≤ 1 := by linarith only [h.pt13, r3pt0, r3pt1, r3pt2]
            have r4 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have r5 : 3 * d 0 + 3 * d 1 + ((-4:ℝ)/1) * d 3 ≤ 0 := by linarith only [outside]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤4322351057930747 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤4322351057930748 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤8644702115861496 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤8644702115861496 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤720391842988458 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤2881567371953832 by norm_num)))
            have aggregated : 1 * d 0 + ((-28815673719538319:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 6 ≤ ((-18009796074711450:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, b0_0, m2, b1_6]
          have tst3 : 4*d 3<3*(d 6+d 8) := by
            apply lt_of_not_ge
            intro outside
            have r0 : 1 * d 1 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 8 ≤ 0 := by linarith only [h.tri042]
            have r1 : 1 * d 5 + ((-1:ℝ)/1) * d 6 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri143]
            have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
            have r3cp := h.cp 3 0 1 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r3 : 12 * d 1 + 36 * d 2 + 12 * d 7 ≤ 49 := by linarith only [r3cp]
            have r4cp := h.cp 3 2 1 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r4 : 24 * d 0 + 12 * d 1 + 36 * d 2 + 12 * d 3 + 8 * d 4 + 24 * d 5 + 8 * d 6 + 12 * d 7 + 4 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r4cp]
            have r5pt0 := plane_hh b1_1 b1_5
            have r5pt1 := plane_lh b0_0 m4
            have r5pt2 := plane_hl b1_2 b0_4
            have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ 1 := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
            have r6pt0 := plane_hh b1_1 b1_5
            have r6pt1 := plane_hl m1 b0_7
            have r6pt2 := plane_hl b1_2 b0_4
            have r6 : 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ 1 := by linarith only [h.pt1, r6pt0, r6pt1, r6pt2]
            have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have r8 : ((-4:ℝ)/1) * d 3 + 3 * d 6 + 3 * d 8 ≤ 0 := by linarith only [outside]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤32422021744664172 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤48633032616996256 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤389064260935970112 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤5403670290777363 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤4052752718083022 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤194532130467985024 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤226954152212649248 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤47282115044301920 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤194532130467985024 by norm_num)))
            have aggregated : 16 * d 0 + 24 * d 1 + ((-226954152212649180:ℝ)/1) * d 2 + ((-1150981771935578116:ℝ)/1) * d 3 + 16 * d 4 + 16 * d 5 + ((-48:ℝ)/1) * d 6 + ((-4:ℝ)/1) * d 7 + ((-52:ℝ)/1) * d 8 + 8 * d 9 ≤ ((-1225282238433766821:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, b0_0, b0_1, b1_2, m2, b0_4, b0_5, b1_6, m4, b1_8, b0_9]
          have tst4 : 4*d 1<3*(d 3+d 2) := by
            apply lt_of_not_ge
            intro outside
            have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
            have r1 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
            have r2 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
            have r3 : 1 * d 0 + ((-1:ℝ)/1) * d 3 ≤ 0 := by linarith only [hN.s04]
            have r4 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
            have r5cp := h.cp 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r5 : 12 * d 0 + 36 * d 1 + 12 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 8 * d 6 + 12 * d 7 + 24 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r5cp]
            have r6pt0 := plane_hh b1_1 b1_6
            have r6pt1 := plane_lh b0_0 b1_8
            have r6pt2 := plane_hl m2 b0_4
            have r6 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ 1 := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
            have r7pt0 := plane_hh b1_1 b1_6
            have r7pt1 := plane_hl m1 b0_8
            have r7pt2 := plane_hl m2 b0_4
            have r7 : 1 * d 1 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ 1 := by linarith only [h.pt4, r7pt0, r7pt1, r7pt2]
            have r8pt0 := plane_hh b1_5 b1_8
            have r8pt1 := plane_lh b0_4 m3
            have r8pt2 := plane_lh b0_6 m4
            have r8 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + 1 * d 8 ≤ 1 := by linarith only [h.pt13, r8pt0, r8pt1, r8pt2]
            have r9 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have r10 : ((-4:ℝ)/1) * d 1 + 3 * d 2 + 3 * d 3 ≤ 0 := by linarith only [outside]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤45861561992104944 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤60655614247622600 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤30327807123811296 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤79887882179795616 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤448259783342186624 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤7581951780952825 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤155337548682935840 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤424589299733358272 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤406836437026737024 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤36430353679212360 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤115393607593038144 by norm_num)))
            have aggregated : 28 * d 0 + ((-140:ℝ)/1) * d 1 + 12 * d 2 + ((-8:ℝ)/1) * d 3 + 12 * d 4 + 4 * d 5 + ((-120:ℝ)/1) * d 6 + 4 * d 7 + ((-32:ℝ)/1) * d 8 ≤ ((-40128866743092004:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, b0_0, b1_1, b0_2, m2, b0_4, b0_5, b1_6, b0_7, b1_8]
          have tst5 : 4*d 1<3*(d 8+d 7) := by
            apply lt_of_not_ge
            intro outside
            have r0 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
            have r1 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
            have r2cp := h.cp 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r2 : 4 * d 0 + 4 * d 1 + 4 * d 2 + 4 * d 3 + 4 * d 4 + 4 * d 5 + 4 * d 6 + 4 * d 7 + 4 * d 8 + 4 * d 9 ≤ 25 := by linarith only [r2cp]
            have r3pt0 := plane_hh b1_1 b1_5
            have r3pt1 := plane_hl m1 b0_7
            have r3pt2 := plane_hl b1_2 b0_4
            have r3 : 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ 1 := by linarith only [h.pt1, r3pt0, r3pt1, r3pt2]
            have r4pt0 := plane_hh b1_1 b1_6
            have r4pt1 := plane_lh b0_0 b1_8
            have r4pt2 := plane_hl m2 b0_4
            have r4 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ 1 := by linarith only [h.pt4, r4pt0, r4pt1, r4pt2]
            have r5pt0 := plane_hh b1_1 b1_6
            have r5pt1 := plane_hl m1 b0_8
            have r5pt2 := plane_hl m2 b0_4
            have r5 : 1 * d 1 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ 1 := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
            have r6pt0 := plane_hh b1_2 b1_6
            have r6pt1 := plane_lh b0_0 m3
            have r6pt2 := plane_hl m2 b0_5
            have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/2) * d 5 + 1 * d 6 ≤ 1 := by linarith only [h.pt7, r6pt0, r6pt1, r6pt2]
            have r7pt0 := plane_hh b1_2 b1_8
            have r7pt1 := plane_hl b1_1 b0_9
            have r7pt2 := plane_hl m2 b0_7
            have r7 : 1 * d 2 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 1 := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
            have r8 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have r9 : ((-4:ℝ)/1) * d 1 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤7244514409282032 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤42863376921585320 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤5131531039908104 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤53126439001401528 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤16903866954991406 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤3622257204641009 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤21733543227846080 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤20526124159632416 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤5232149295592576 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤7848223943388863 by norm_num)))
            have aggregated : 2 * d 0 + ((-5:ℝ)/1) * d 1 + ((-22337252761952904:ℝ)/1) * d 3 + ((1:ℝ)/2) * d 4 + ((-8:ℝ)/1) * d 5 + ((-1:ℝ)/1) * d 6 + 1 * d 7 + ((9:ℝ)/2) * d 8 ≤ ((-12174808937821185:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, b0_0, b1_1, m2, b0_4, b1_5, b1_6, b0_7, b0_8]
          exact ⟨0, tst0,tst1,tst2,tst3,tst4,tst5⟩
        · have lom4 : ((1:ℝ)/2) ≤ d 7 := le_of_lt (lt_of_not_ge m4)
          exfalso
          have r0 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
          have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
          have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
          have r3cp := h.cp 1790 2103 1977 2314 1815 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          have r3 : 15057480 * d 0 + 14155320 * d 1 + 16568240 * d 2 + 12995400 * d 3 + 16630524 * d 4 + 19465368 * d 5 + 15267780 * d 6 + 18299112 * d 7 + 14353020 * d 8 + 16799640 * d 9 ≤ 99980001 := by linarith only [r3cp]
          have r4pt0 := plane_hh b1_1 b1_5
          have r4pt1 := plane_hl m1 lom4
          have r4pt2 := plane_hl b1_2 b0_4
          have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((3:ℝ)/4) := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
          have r5pt0 := plane_hh b1_1 b1_6
          have r5pt1 := plane_lh b0_0 b1_8
          have r5pt2 := plane_hl m2 b0_4
          have r5 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ 1 := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
          have r6pt0 := plane_hh b1_2 b1_6
          have r6pt1 := plane_hl m1 b0_9
          have r6pt2 := plane_lh b0_3 b1_5
          have r6 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + 1 * d 6 + ((-1:ℝ)/2) * d 9 ≤ 1 := by linarith only [h.pt7, r6pt0, r6pt1, r6pt2]
          have r7pt0 := plane_hh b1_2 b1_6
          have r7pt1 := plane_hl m1 b0_9
          have r7pt2 := plane_hl m2 b0_5
          have r7 : 1 * d 2 + ((-1:ℝ)/2) * d 5 + 1 * d 6 + ((-1:ℝ)/2) * d 9 ≤ 1 := by linarith only [h.pt7, r7pt0, r7pt1, r7pt2]
          have r8pt0 := plane_hh b1_2 b1_8
          have r8pt1 := plane_hl b1_1 b0_9
          have r8pt2 := plane_hl m2 lom4
          have r8 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
          have r9pt0 := plane_hh b1_5 b1_8
          have r9pt1 := plane_lh b0_4 m3
          have r9pt2 := plane_hl b1_6 lom4
          have r9 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r9pt0, r9pt1, r9pt2]
          have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
          have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤3352117902439882424320 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤14026721419440831856640 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤7288254017178542538752 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤4123626411324491 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤21878889595620810555392 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤61826580935180843745280 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤24576829905999585345536 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤12436714304172411846656 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤36741945680216553684992 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤46148283909066251567104 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤11839726828629287501824 by norm_num)))
          have aggregated : ((-2847976:ℝ)/1) * d 0 + ((-1779096:ℝ)/1) * d 1 + ((-14378864:ℝ)/1) * d 2 + 3190296 * d 3 + 3690452 * d 4 + ((-9095032:ℝ)/1) * d 5 + ((-15243668:ℝ)/1) * d 6 + ((-4535304:ℝ)/1) * d 7 + 1043028 * d 8 + ((-12154488:ℝ)/1) * d 9 ≤ ((-1986548318222076183573:ℝ)/1) := by convert combined using 1 <;> ring
          linarith only [aggregated, m1, b1_1, b1_2, b0_3, b0_4, b1_5, b1_6, b1_7, b0_8, m3]
      · have lom3 : ((1:ℝ)/2) ≤ d 9 := le_of_lt (lt_of_not_ge m3)
        exfalso
        have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
        have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
        have r2 : 1 * d 0 + ((-1:ℝ)/1) * d 3 ≤ 0 := by linarith only [hN.s04]
        have r3 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
        have r4cp := h.cp 1712 2146 1834 2182 2126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        have r4 : 14695808 * d 0 + 12559232 * d 1 + 14942336 * d 2 + 14558848 * d 3 + 15743056 * d 4 + 18730288 * d 5 + 18249584 * d 6 + 16007152 * d 7 + 15596336 * d 8 + 18555728 * d 9 ≤ 100000000 := by linarith only [r4cp]
        have r5pt0 := plane_hh b1_1 b1_5
        have r5pt1 := plane_hl m1 b0_7
        have r5pt2 := plane_hl b1_2 b0_4
        have r5 : 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ 1 := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
        have r6pt0 := plane_hh b1_1 b1_6
        have r6pt1 := plane_lh b0_0 b1_8
        have r6pt2 := plane_hl m2 b0_4
        have r6 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ 1 := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
        have r7pt0 := plane_hh b1_2 b1_6
        have r7pt1 := plane_hl m1 lom3
        have r7pt2 := plane_lh b0_3 b1_5
        have r7 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + 1 * d 6 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt7, r7pt0, r7pt1, r7pt2]
        have r8pt0 := plane_hh b1_2 b1_8
        have r8pt1 := plane_hl b1_1 lom3
        have r8pt2 := plane_hl m2 b0_7
        have r8 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
        have r9pt0 := plane_hh b1_5 b1_8
        have r9pt1 := plane_hl b1_4 lom3
        have r9pt2 := plane_hl b1_6 b0_7
        have r9 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r9pt0, r9pt1, r9pt2]
        have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤8369464172059250655232 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤2900738251941956550656 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤6811203549660157313024 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤16231978703653282250752 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤2059752741999095 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤27046563821124302405632 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤23788878658004865515520 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤4043706583092643758080 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤33501730046417840373760 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤2696628289825226096640 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤5693579514781855907840 by norm_num)))
        have aggregated : ((-993664:ℝ)/1) * d 0 + 5390464 * d 1 + 2423680 * d 2 + 370048 * d 3 + ((-12081872:ℝ)/1) * d 4 + 2697552 * d 5 + 7056656 * d 6 + 41104 * d 7 + ((-7107760:ℝ)/1) * d 8 + ((-5283280:ℝ)/1) * d 9 ≤ ((-1042720439831255509248:ℝ)/1) := by convert combined using 1 <;> ring
        linarith only [aggregated, m1, b0_1, b0_2, b0_3, b1_4, b0_5, b0_6, b0_7, b1_8, b1_9]
    · have lom2 : ((1:ℝ)/2) ≤ d 3 := le_of_lt (lt_of_not_ge m2)
      by_cases m5 : d 4 ≤ ((1:ℝ)/2)
      ·
        by_cases m6 : d 1 ≤ ((1:ℝ)/2)
        ·
          by_cases m7 : d 7 ≤ ((1:ℝ)/2)
          ·
            exfalso
            have r0cp := h.cp 1 3 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r0 : 12 * d 0 + 4 * d 1 + 8 * d 2 + 12 * d 3 + 12 * d 4 + 24 * d 5 + 36 * d 6 + 8 * d 7 + 12 * d 8 + 24 * d 9 ≤ 100 := by linarith only [r0cp]
            have r1cp := h.cp 3 1 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r1 : 12 * d 0 + 12 * d 1 + 24 * d 2 + 36 * d 3 + 4 * d 4 + 8 * d 5 + 12 * d 6 + 8 * d 7 + 12 * d 8 + 24 * d 9 ≤ 100 := by linarith only [r1cp]
            have r2pt0 := plane_hh m6 b1_5
            have r2pt1 := plane_lh b0_0 m7
            have r2pt2 := plane_hl b1_2 b0_4
            have r2 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 + ((1:ℝ)/2) * d 5 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r2pt0, r2pt1, r2pt2]
            have r3pt0 := plane_hh b1_2 b1_8
            have r3pt1 := plane_hl m6 b0_9
            have r3pt2 := plane_lh lom2 m7
            have r3 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt10, r3pt0, r3pt1, r3pt2]
            have r4pt0 := plane_hh b1_5 b1_8
            have r4pt1 := plane_hl m5 b0_9
            have r4pt2 := plane_lh b0_6 m7
            have r4 : 1 * d 5 + ((-1:ℝ)/2) * d 6 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ 1 := by linarith only [h.pt13, r4pt0, r4pt1, r4pt2]
            have r5 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤6523897238122125 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤5074142296317209 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤98583336042734336 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤521911779049770112 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤34794118603318024 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤57990197672196664 by norm_num)))
            have aggregated : 89884806391904840 * d 0 + ((-510313739515330624:ℝ)/1) * d 1 + 160 * d 2 + ((-32:ℝ)/1) * d 3 + ((-414629913356206104:ℝ)/1) * d 5 + ((-417529423239815972:ℝ)/1) * d 6 + ((-168171573249370384:ℝ)/1) * d 7 + 176 * d 8 + ((-52:ℝ)/1) * d 9 ≤ ((-1206196111581690360:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, b0_0, m6, b0_2, b1_3, b1_5, b1_6, m7, b0_8, b1_9]
          · have lom7 : ((1:ℝ)/2) ≤ d 7 := le_of_lt (lt_of_not_ge m7)
            have tst0 : 4*d 1<3*(d 7+d 8) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 4 + 1 * d 6 + ((-1:ℝ)/1) * d 8 ≤ 0 := by linarith only [h.tri124]
              have r1 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r2 : ((-4:ℝ)/1) * d 1 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤12 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤1 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤8 by norm_num)))
              have aggregated : ((-44:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 4 + ((-12:ℝ)/1) * d 5 + 24 * d 7 ≤ ((-49:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m6, b1_2, m5, b1_5, lom7]
            have tst1 : 4*d 1<3*(d 2+d 3) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 2 + 1 * d 5 ≤ 0 := by linarith only [h.tri103]
              have r1 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r2 : ((-4:ℝ)/1) * d 1 + 3 * d 2 + 3 * d 3 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤9388332405397968 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤782361033783164 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤6258888270265313 by norm_num)))
              have aggregated : ((-9388332405397968:ℝ)/1) * d 0 + ((-34423885486459220:ℝ)/1) * d 1 + 3 * d 2 + 18776664810795939 * d 3 + ((-9388332405397968:ℝ)/1) * d 6 + ((-9388332405397968:ℝ)/1) * d 8 ≤ ((-38335690655375036:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m1, m6, b0_2, lom2, b1_6, b1_8]
            have tst2 : 4*d 4<3*(d 7+d 8) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 4 + 1 * d 6 + ((-1:ℝ)/1) * d 8 ≤ 0 := by linarith only [h.tri124]
              have r1 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r2 : ((-4:ℝ)/1) * d 4 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤12 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤1 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤8 by norm_num)))
              have aggregated : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-44:ℝ)/1) * d 4 + ((-12:ℝ)/1) * d 5 + 24 * d 7 ≤ ((-49:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m6, b1_2, m5, b1_5, lom7]
            have tst3 : 4*d 4<3*(d 5+d 6) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r1 : ((-4:ℝ)/1) * d 4 + 3 * d 5 + 3 * d 6 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤2238756188979516 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤8955024755918059 by norm_num)))
              have aggregated : ((-26865074267754192:ℝ)/1) * d 1 + ((-26865074267754192:ℝ)/1) * d 2 + ((-35820099023672236:ℝ)/1) * d 4 + ((-15:ℝ)/1) * d 5 + ((-15:ℝ)/1) * d 6 + ((-26865074267754192:ℝ)/1) * d 8 ≤ ((-109699053259996284:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m6, b1_2, m5, b1_5, b1_6, b1_8]
            have tst4 : 4*d 8<3*(d 4+d 1) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
              have r1 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri043]
              have r2 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
              have r3 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
              have r4 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
              have r5cp := h.cp 1614 2463 1527 2463 1931 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r5 : 15901128 * d 0 + 9858312 * d 1 + 15901128 * d 2 + 12466536 * d 3 + 15044004 * d 4 + 24265476 * d 5 + 19024212 * d 6 + 15044004 * d 7 + 11794548 * d 8 + 19024212 * d 9 ≤ 99960004 := by linarith only [r5cp]
              have r6cp := h.cp 1521 2606 1459 2606 1809 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r6 : 15854904 * d 0 + 8876556 * d 1 + 15854904 * d 2 + 11005956 * d 3 + 15208616 * d 4 + 27164944 * d 5 + 18857016 * d 6 + 15208616 * d 7 + 10557324 * d 8 + 18857016 * d 9 ≤ 100020001 := by linarith only [r6cp]
              have r7cp := h.cp 1689 2432 1469 2432 1977 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r7 : 16430592 * d 0 + 9924564 * d 1 + 16430592 * d 2 + 13356612 * d 3 + 14290432 * d 4 + 23658496 * d 5 + 19232256 * d 6 + 14290432 * d 7 + 11616852 * d 8 + 19232256 * d 9 ≤ 99980001 := by linarith only [r7cp]
              have r8pt0 := plane_hh b1_2 b1_8
              have r8pt1 := plane_hl m6 b0_9
              have r8pt2 := plane_hl b1_3 lom7
              have r8 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
              have r9 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r10 : 3 * d 1 + 3 * d 4 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤302707459175552328400896 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤39293097022813699571712 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤125239924380320126730240 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤148031752126637820346368 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤113428290290080922206208 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤5245275759448956 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤8791280234429100 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤5582780454016847 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤144361747062494387503104 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤41514494779258298171392 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤3437986662140041756672 by norm_num)))
              have aggregated : ((-24612736:ℝ)/1) * d 0 + ((-78754212:ℝ)/1) * d 1 + 17330304 * d 2 + ((-43355124:ℝ)/1) * d 3 + ((-31237552:ℝ)/1) * d 4 + ((-30861136:ℝ)/1) * d 5 + 10178640 * d 6 + ((-35956144:ℝ)/1) * d 7 + 108692012 * d 8 + ((-174370736:ℝ)/1) * d 9 ≤ ((-241331542525103584885:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m1, m6, b0_2, b1_3, m5, b1_5, b0_6, b1_7, b0_8, b1_9]
            have tst5 : 4*d 8<3*(d 6+d 3) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
              have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 2 + 1 * d 5 ≤ 0 := by linarith only [h.tri103]
              have r2 : 1 * d 0 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [hN.s01]
              have r3cp := h.cp 0 3 0 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r3 : 36 * d 5 + 12 * d 6 + 12 * d 9 ≤ 49 := by linarith only [r3cp]
              have r4cp := h.cp 1 1 3 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r4 : 4 * d 0 + 12 * d 1 + 8 * d 2 + 12 * d 3 + 12 * d 4 + 8 * d 5 + 12 * d 6 + 24 * d 7 + 36 * d 8 + 24 * d 9 ≤ 100 := by linarith only [r4cp]
              have r5cp := h.cp 1 1 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r5 : 4 * d 0 + 12 * d 1 + 12 * d 2 + 8 * d 3 + 12 * d 4 + 12 * d 5 + 8 * d 6 + 36 * d 7 + 24 * d 8 + 24 * d 9 ≤ 100 := by linarith only [r5cp]
              have r6pt0 := plane_hh b1_2 b1_8
              have r6pt1 := plane_hl m6 b0_9
              have r6pt2 := plane_lh lom2 b1_7
              have r6 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
              have r7pt0 := plane_hh b1_5 b1_8
              have r7pt1 := plane_hl m5 b0_9
              have r7pt2 := plane_hl b1_6 lom7
              have r7 : 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r7pt0, r7pt1, r7pt2]
              have r8 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r9 : 3 * d 3 + 3 * d 6 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤15885205552237764 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤162823356910437664 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤130060120458947104 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤1709865875414481 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤5501907131374034 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤6660203369558040 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤506009985195241920 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤118808099859445248 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤38927027147541088 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤128901824220763040 by norm_num)))
              have aggregated : ((-28:ℝ)/1) * d 0 + ((-305293794207070404:ℝ)/1) * d 1 + ((-48:ℝ)/1) * d 2 + ((-72:ℝ)/1) * d 3 + 20 * d 4 + ((-76:ℝ)/1) * d 5 + ((-60:ℝ)/1) * d 6 + 48 * d 7 + 136 * d 8 + ((-36:ℝ)/1) * d 9 ≤ ((-295020809713652759:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m1, m6, b1_2, b1_3, b0_4, b1_5, b1_6, lom7, b0_8, b1_9]
            exact ⟨2, tst0,tst1,tst2,tst3,tst4,tst5⟩
        · have lom6 : ((1:ℝ)/2) ≤ d 1 := le_of_lt (lt_of_not_ge m6)
          by_cases m8 : d 7 ≤ ((1:ℝ)/2)
          ·
            exfalso
            have r0 : ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [h.tri123]
            have r1cp := h.cp 3 3 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r1 : 36 * d 0 + 24 * d 1 + 36 * d 2 + 36 * d 3 + 24 * d 4 + 36 * d 5 + 36 * d 6 + 24 * d 7 + 24 * d 8 + 36 * d 9 ≤ 196 := by linarith only [r1cp]
            have r2cp := h.cp 1819 2084 1677 2225 2196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r2 : 15163184 * d 0 + 12201852 * d 1 + 16189100 * d 2 + 15978096 * d 3 + 13979472 * d 4 + 18547600 * d 5 + 18305856 * d 6 + 14925300 * d 7 + 14730768 * d 8 + 19544400 * d 9 ≤ 100020001 := by linarith only [r2cp]
            have r3cp := h.cp 2136 1973 1410 2850 1631 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            have r3 : 16857312 * d 0 + 12047040 * d 1 + 24350400 * d 2 + 13935264 * d 3 + 11127720 * d 4 + 22492200 * d 5 + 12871852 * d 6 + 16074000 * d 7 + 9198840 * d 8 + 18593400 * d 9 ≤ 100000000 := by linarith only [r3cp]
            have r4pt0 := plane_hh b1_1 b1_5
            have r4pt1 := plane_lh b0_0 m8
            have r4pt2 := plane_lh b0_2 m5
            have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + 1 * d 5 ≤ 1 := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
            have r5pt0 := plane_hh b1_1 b1_5
            have r5pt1 := plane_lh b0_0 m8
            have r5pt2 := plane_hl b1_2 b0_4
            have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ 1 := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
            have r6pt0 := plane_hh b1_1 b1_6
            have r6pt1 := plane_lh b0_0 b1_8
            have r6pt2 := plane_lh lom2 m5
            have r6 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ ((3:ℝ)/4) := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
            have r7pt0 := plane_hh b1_2 b1_6
            have r7pt1 := plane_hl m1 b0_9
            have r7pt2 := plane_lh lom2 b1_5
            have r7 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 5 + 1 * d 6 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt7, r7pt0, r7pt1, r7pt2]
            have r8pt0 := plane_hh b1_2 b1_8
            have r8pt1 := plane_hl b1_1 b0_9
            have r8pt2 := plane_lh lom2 m8
            have r8 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
            have r9pt0 := plane_hh b1_5 b1_8
            have r9pt1 := plane_hl m5 b0_9
            have r9pt2 := plane_hl b1_6 b0_7
            have r9 : 1 * d 5 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ 1 := by linarith only [h.pt13, r9pt0, r9pt1, r9pt2]
            have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
            have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤6324169084374069805056 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤1651055002865305649152 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤4994538140990877 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤362288944164464 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤28428915196009142812672 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤58162248613460105494528 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤97982716791209943105536 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤35993002715710526324736 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤118610841930924696797184 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤54364142623161652871168 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤24125527106339947413504 by norm_num)))
            have aggregated : ((-4656528:ℝ)/1) * d 0 + 36921100 * d 1 + 57149308 * d 2 + ((-9817936:ℝ)/1) * d 3 + ((-4653680:ℝ)/1) * d 4 + ((-310345520:ℝ)/1) * d 5 + 39780736 * d 6 + ((-4671068:ℝ)/1) * d 7 + 53511248 * d 8 + ((-141649264:ℝ)/1) * d 9 ≤ ((-1364466544078313229251:ℝ)/1) := by convert combined using 1 <;> ring
            linarith only [aggregated, m1, lom6, b0_2, b1_3, m5, b1_5, b0_6, m8, b0_8, b1_9]
          · have lom8 : ((1:ℝ)/2) ≤ d 7 := le_of_lt (lt_of_not_ge m8)
            by_cases m9 : d 8 ≤ ((1:ℝ)/2)
            ·
              exfalso
              have r0 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
              have r1cp := h.cp 1686 2724 1189 2908 1492 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r1 : 18370656 * d 0 + 8018616 * d 1 + 19611552 * d 2 + 10062048 * d 3 + 12955344 * d 4 + 31685568 * d 5 + 16256832 * d 6 + 13830448 * d 7 + 7095952 * d 8 + 17354944 * d 9 ≤ 99980001 := by linarith only [r1cp]
              have r2pt0 := plane_hh b1_1 b1_5
              have r2pt1 := plane_hl m1 lom8
              have r2pt2 := plane_lh b0_2 m5
              have r2 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((3:ℝ)/4) := by linarith only [h.pt1, r2pt0, r2pt1, r2pt2]
              have r3pt0 := plane_hh b1_1 b1_6
              have r3pt1 := plane_lh b0_0 m9
              have r3pt2 := plane_lh lom2 m5
              have r3 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ ((3:ℝ)/4) := by linarith only [h.pt4, r3pt0, r3pt1, r3pt2]
              have r4 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤322449926438691274752 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤18579715753545 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤513931585168369975296 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤813611401081324830720 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤123043882688876904448 by norm_num)))
              have aggregated : ((-152736:ℝ)/1) * d 0 + ((-53640:ℝ)/1) * d 1 + ((-1369115323204840889184:ℝ)/1) * d 2 + ((-219855708802136455200:ℝ)/1) * d 3 + ((-166099091531267720880:ℝ)/1) * d 4 + ((-373886160168531539520:ℝ)/1) * d 5 + ((-360867873572063553216:ℝ)/1) * d 6 + ((-49488:ℝ)/1) * d 7 + ((-1344685821105723703536:ℝ)/1) * d 8 + 1728 * d 9 ≤ ((-3175893012448552359895:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, m1, b1_1, b1_2, b1_3, m5, b1_5, b1_6, b1_7, m9, b0_9]
            · have lom9 : ((1:ℝ)/2) ≤ d 8 := le_of_lt (lt_of_not_ge m9)
              by_cases m10 : d 8 ≤ ((3:ℝ)/4)
              ·
                have tst0 : 4*d 1<3*(d 7+d 8) := by
                  apply lt_of_not_ge
                  intro outside
                  have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                  have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
                  have r2cp := h.cp 3 1 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r2 : 12 * d 0 + 24 * d 1 + 36 * d 2 + 12 * d 3 + 8 * d 4 + 12 * d 5 + 4 * d 6 + 24 * d 7 + 8 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r2cp]
                  have r3pt0 := plane_hh b1_1 b1_5
                  have r3pt1 := plane_hl m1 lom8
                  have r3pt2 := plane_lh b0_2 m5
                  have r3 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((3:ℝ)/4) := by linarith only [h.pt1, r3pt0, r3pt1, r3pt2]
                  have r4pt0 := plane_hh b1_1 b1_6
                  have r4pt1 := plane_lh b0_0 m10
                  have r4pt2 := plane_lh lom2 m5
                  have r4 : ((-3:ℝ)/4) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ ((3:ℝ)/4) := by linarith only [h.pt4, r4pt0, r4pt1, r4pt2]
                  have r5pt0 := plane_hh b1_1 b1_6
                  have r5pt1 := plane_hl m1 lom9
                  have r5pt2 := plane_lh lom2 m5
                  have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ ((1:ℝ)/2) := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
                  have r6 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have r7 : ((-4:ℝ)/1) * d 1 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
                  have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤18193842351941180 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤90969211759705936 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤7580767646642161 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤121292282346274576 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤48516912938509904 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤133421510580901984 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤17688457842165044 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤72775369407764736 by norm_num)))
                  have aggregated : ((-20:ℝ)/1) * d 0 + 36 * d 1 + ((-20:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 3 + ((-48516912938509836:ℝ)/1) * d 4 + ((-20:ℝ)/1) * d 5 + 4 * d 6 + 339618390569568784 * d 7 + ((-24:ℝ)/1) * d 8 + ((-4:ℝ)/1) * d 9 ≤ 85409982152168296 := by convert combined using 1 <;> ring
                  linarith only [aggregated, m1, lom6, b1_2, b1_3, m5, b1_5, b0_6, lom8, m10, b1_9]
                have tst1 : 4*d 1<3*(d 2+d 3) := by
                  apply lt_of_not_ge
                  intro outside
                  have r0 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
                  have r1cp := h.cp 3 3 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r1 : 36 * d 0 + 36 * d 1 + 36 * d 2 + 24 * d 3 + 36 * d 4 + 36 * d 5 + 24 * d 6 + 36 * d 7 + 24 * d 8 + 24 * d 9 ≤ 196 := by linarith only [r1cp]
                  have r2cp := h.cp 2 1 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r2 : 8 * d 0 + 16 * d 1 + 8 * d 2 + 8 * d 3 + 8 * d 4 + 4 * d 5 + 4 * d 6 + 8 * d 7 + 8 * d 8 + 4 * d 9 ≤ 49 := by linarith only [r2cp]
                  have r3pt0 := plane_hh b1_1 b1_5
                  have r3pt1 := plane_hl m1 lom8
                  have r3pt2 := plane_lh b0_2 m5
                  have r3 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((3:ℝ)/4) := by linarith only [h.pt1, r3pt0, r3pt1, r3pt2]
                  have r4pt0 := plane_hh b1_1 b1_6
                  have r4pt1 := plane_lh b0_0 m10
                  have r4pt2 := plane_lh lom2 m5
                  have r4 : ((-3:ℝ)/4) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ ((3:ℝ)/4) := by linarith only [h.pt4, r4pt0, r4pt1, r4pt2]
                  have r5 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have r6 : ((-4:ℝ)/1) * d 1 + 3 * d 2 + 3 * d 3 ≤ 0 := by linarith only [outside]
                  have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤1573251673504255232 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤7712018007373793 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤347040810331821056 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤6107918261840050176 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤6200462477928535040 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤647809512619399168 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤2591238050477596672 by norm_num)))
                  have aggregated : ((-3077095184942146140:ℝ)/1) * d 0 + 1956 * d 1 + ((-92:ℝ)/1) * d 2 + 7634897827300061976 * d 3 + ((-46272108044242524:ℝ)/1) * d 4 + 932 * d 5 + 280 * d 6 + ((-92:ℝ)/1) * d 7 + ((-4812299236601250536:ℝ)/1) * d 8 + 24 * d 9 ≤ ((-3994825327819625148:ℝ)/1) := by convert combined using 1 <;> ring
                  linarith only [aggregated, m1, lom6, b1_2, lom2, m5, b0_5, b0_6, b1_7, m10, b0_9]
                have tst2 : 4*d 4<3*(d 7+d 8) := by
                  apply lt_of_not_ge
                  intro outside
                  have r0 : ((-4:ℝ)/1) * d 4 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
                  have combined := (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤1 by norm_num))
                  have aggregated : ((-4:ℝ)/1) * d 4 + 3 * d 7 + 3 * d 8 ≤ 0 := by convert combined using 1 <;> ring
                  linarith only [aggregated, m5, lom8, lom9]
                have tst3 : 4*d 4<3*(d 5+d 6) := by
                  apply lt_of_not_ge
                  intro outside
                  have r0 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have r1 : ((-4:ℝ)/1) * d 4 + 3 * d 5 + 3 * d 6 ≤ 0 := by linarith only [outside]
                  have combined := (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤4477512377959031 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤17910049511836126 by norm_num)))
                  have aggregated : ((-53730148535508372:ℝ)/1) * d 1 + ((-53730148535508372:ℝ)/1) * d 2 + ((-71640198047344504:ℝ)/1) * d 4 + 6 * d 5 + 6 * d 6 + ((-53730148535508372:ℝ)/1) * d 8 ≤ ((-219398106519992519:ℝ)/1) := by convert combined using 1 <;> ring
                  linarith only [aggregated, b1_1, b1_2, m5, b0_5, b0_6, m10]
                have tst4 : 4*d 8<3*(d 4+d 1) := by
                  apply lt_of_not_ge
                  intro outside
                  have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                  have r1 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri043]
                  have r2 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
                  have r3cp := h.cp 1795 2129 1815 2341 1920 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r3 : 15286220 * d 0 + 13031700 * d 1 + 16808380 * d 2 + 13785600 * d 3 + 15456540 * d 4 + 19935956 * d 5 + 16350720 * d 6 + 16995660 * d 7 + 13939200 * d 8 + 17978880 * d 9 ≤ 100000000 := by linarith only [r3cp]
                  have r4cp := h.cp 1712 2146 1834 2182 2126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r4 : 14695808 * d 0 + 12559232 * d 1 + 14942336 * d 2 + 14558848 * d 3 + 15743056 * d 4 + 18730288 * d 5 + 18249584 * d 6 + 16007152 * d 7 + 15596336 * d 8 + 18555728 * d 9 ≤ 100000000 := by linarith only [r4cp]
                  have r5pt0 := plane_ll lom6 b0_6
                  have r5pt1 := plane_lh b0_0 m10
                  have r5pt2 := plane_lh lom2 m5
                  have r5 : ((-3:ℝ)/4) * d 0 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + ((1:ℝ)/2) * d 6 ≤ ((-1:ℝ)/4) := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
                  have r6pt0 := plane_hh b1_1 b1_6
                  have r6pt1 := plane_lh b0_0 m10
                  have r6pt2 := plane_lh lom2 m5
                  have r6 : ((-3:ℝ)/4) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ ((3:ℝ)/4) := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
                  have r7pt0 := plane_hh b1_2 m10
                  have r7pt1 := plane_lh lom6 b1_9
                  have r7pt2 := plane_hl b1_3 lom8
                  have r7 : ((-1:ℝ)/1) * d 1 + ((3:ℝ)/4) * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((-1:ℝ)/4) := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
                  have r8pt0 := plane_hh b1_5 m10
                  have r8pt1 := plane_hl m5 b0_9
                  have r8pt2 := plane_hl b1_6 lom8
                  have r8 : ((3:ℝ)/4) * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt13, r8pt0, r8pt1, r8pt2]
                  have r9 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have r10 : 3 * d 1 + 3 * d 4 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
                  have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤221845000427673395134464 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤4323437381487272394752 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤175630083831331322593280 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤15545984714911360 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤3085746190114427 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤218253616938314866098176 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤97442328953796295655424 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤194128452613588192854016 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤119479826264824731402240 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤38110904315625827467264 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤30275587905184971358208 by norm_num)))
                  have aggregated : 2824832 * d 0 + 47755392 * d 1 + ((-60693632:ℝ)/1) * d 2 + 140017536 * d 3 + 41026672 * d 4 + 6469648 * d 5 + 110723792 * d 6 + 10823248 * d 7 + 20467728 * d 8 + 91248496 * d 9 ≤ ((-4405035069509206041856:ℝ)/1) := by convert combined using 1 <;> ring
                  linarith only [aggregated, b0_0, lom6, b1_2, lom2, b0_4, b0_5, b0_6, lom8, lom9, b0_9]
                have tst5 : 4*d 8<3*(d 6+d 3) := by
                  apply lt_of_not_ge
                  intro outside
                  have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                  have r1cp := h.cp 3 1 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r1 : 12 * d 0 + 24 * d 1 + 36 * d 2 + 12 * d 3 + 8 * d 4 + 12 * d 5 + 4 * d 6 + 24 * d 7 + 8 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r1cp]
                  have r2pt0 := plane_hh b1_1 b1_5
                  have r2pt1 := plane_lh b0_0 b1_7
                  have r2pt2 := plane_hl b1_2 b0_4
                  have r2 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ 1 := by linarith only [h.pt1, r2pt0, r2pt1, r2pt2]
                  have r3pt0 := plane_hh b1_5 m10
                  have r3pt1 := plane_hl m5 b0_9
                  have r3pt2 := plane_hl b1_6 lom8
                  have r3 : ((3:ℝ)/4) * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt13, r3pt0, r3pt1, r3pt2]
                  have r4 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have r5 : 3 * d 3 + 3 * d 6 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
                  have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤2555458284005886 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤425909714000981 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤2555458284005886 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤10221833136023544 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤1277729142002943 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤6246675805347721 by norm_num)))
                  have aggregated : 23850943984054935 * d 3 + ((-1703638856003924:ℝ)/1) * d 4 + ((-1:ℝ)/1) * d 6 + ((-26690342077394808:ℝ)/1) * d 8 ≤ ((-14906839990034335:ℝ)/1) := by convert combined using 1 <;> ring
                  linarith only [aggregated, lom2, m5, b1_6, m10]
                exact ⟨2, tst0,tst1,tst2,tst3,tst4,tst5⟩
              · have lom10 : ((3:ℝ)/4) ≤ d 8 := le_of_lt (lt_of_not_ge m10)
                exfalso
                have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                have r2 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
                have r3cp := h.cp 1620 2181 1936 2056 2207 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                have r3 : 14132880 * d 0 + 12545280 * d 1 + 13322880 * d 2 + 14301360 * d 3 + 16889664 * d 4 + 17936544 * d 5 + 19253868 * d 6 + 15921664 * d 7 + 17091008 * d 8 + 18150368 * d 9 ≤ 100000000 := by linarith only [r3cp]
                have r4cp := h.cp 1712 2146 1834 2182 2126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                have r4 : 14695808 * d 0 + 12559232 * d 1 + 14942336 * d 2 + 14558848 * d 3 + 15743056 * d 4 + 18730288 * d 5 + 18249584 * d 6 + 16007152 * d 7 + 15596336 * d 8 + 18555728 * d 9 ≤ 100000000 := by linarith only [r4cp]
                have r5pt0 := plane_hh b1_1 b1_6
                have r5pt1 := plane_hl m1 lom10
                have r5pt2 := plane_lh lom2 m5
                have r5 : ((-3:ℝ)/4) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ ((3:ℝ)/8) := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
                have r6pt0 := plane_hh b1_2 b1_6
                have r6pt1 := plane_hl m1 b0_9
                have r6pt2 := plane_lh lom2 b1_5
                have r6 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 5 + 1 * d 6 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt7, r6pt0, r6pt1, r6pt2]
                have r7pt0 := plane_ll b0_2 lom10
                have r7pt1 := plane_lh lom6 b1_9
                have r7pt2 := plane_hl b1_3 lom8
                have r7 : ((-1:ℝ)/1) * d 1 + ((3:ℝ)/4) * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 7 + ((-1:ℝ)/2) * d 9 ≤ ((-1:ℝ)/1) := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
                have r8pt0 := plane_ll b0_5 lom10
                have r8pt1 := plane_hl m5 b0_9
                have r8pt2 := plane_hl b1_6 lom8
                have r8 : ((3:ℝ)/4) * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + ((-1:ℝ)/2) * d 9 ≤ ((-1:ℝ)/2) := by linarith only [h.pt13, r8pt0, r8pt1, r8pt2]
                have r9pt0 := plane_hh b1_5 b1_8
                have r9pt1 := plane_hl m5 b0_9
                have r9pt2 := plane_hl b1_6 lom8
                have r9 : 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r9pt0, r9pt1, r9pt2]
                have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤315072935811237181128704 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤74862930921102560460800 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤115618214544939474223104 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤11877302618973202 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤7315663996485999 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤1403245246806152970240 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤165203973091659972870144 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤71201388181250283405312 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤65240982882767113027584 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤169766996034272846938112 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤40513166770205007806464 by norm_num)))
                have aggregated : 20979872 * d 0 + ((-65204608:ℝ)/1) * d 1 + ((-98438016:ℝ)/1) * d 2 + 34205152 * d 3 + 34643248 * d 4 + ((-76672240:ℝ)/1) * d 5 + ((-116939480:ℝ)/1) * d 6 + ((-44258032:ℝ)/1) * d 7 + 83642704 * d 8 + ((-30653072:ℝ)/1) * d 9 ≤ ((-1658688286240405167872:ℝ)/1) := by convert combined using 1 <;> ring
                linarith only [aggregated, b0_0, b1_1, b1_2, lom2, b0_4, b1_5, b1_6, b1_7, lom10, b1_9]
      · have lom5 : ((1:ℝ)/2) ≤ d 4 := le_of_lt (lt_of_not_ge m5)
        by_cases m11 : d 9 ≤ ((1:ℝ)/2)
        ·
          by_cases m12 : d 7 ≤ ((1:ℝ)/2)
          ·
            by_cases m13 : d 8 ≤ ((1:ℝ)/2)
            ·
              by_cases m14 : d 1 ≤ ((1:ℝ)/2)
              ·
                exfalso
                have r0 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                have combined := (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤1 by norm_num))
                have aggregated : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by convert combined using 1 <;> ring
                linarith only [aggregated, m14, b1_2, b1_5, b1_6, m13]
              · have lom14 : ((1:ℝ)/2) ≤ d 1 := le_of_lt (lt_of_not_ge m14)
                by_cases m15 : d 6 ≤ ((1:ℝ)/2)
                ·
                  exfalso
                  have r0 : 1 * d 5 + ((-1:ℝ)/1) * d 6 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri143]
                  have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
                  have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
                  have r3cp := h.cp 3 1 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r3 : 12 * d 0 + 24 * d 1 + 36 * d 2 + 12 * d 3 + 8 * d 4 + 12 * d 5 + 4 * d 6 + 24 * d 7 + 8 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r3cp]
                  have r4pt0 := plane_hh b1_1 b1_5
                  have r4pt1 := plane_hl m1 b0_7
                  have r4pt2 := plane_hl b1_2 lom5
                  have r4 : 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
                  have r5pt0 := plane_hh b1_3 b1_5
                  have r5pt1 := plane_lh b0_0 m11
                  have r5pt2 := plane_lh b0_2 m15
                  have r5 : ((-1:ℝ)/2) * d 0 + ((-1:ℝ)/2) * d 2 + 1 * d 3 + 1 * d 5 ≤ 1 := by linarith only [h.pt8, r5pt0, r5pt1, r5pt2]
                  have r6 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤90860738986875968 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤7571728248906357 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤287725673458440512 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤7571728248906330 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤348299499449691136 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤196864934471564576 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤60573825991250640 by norm_num)))
                  have aggregated : 29 * d 0 + ((-196864934471564624:ℝ)/1) * d 1 + ((-726885911895007656:ℝ)/1) * d 2 + 24 * d 3 + 16 * d 4 + ((-40:ℝ)/1) * d 5 + ((-787459737886258328:ℝ)/1) * d 6 + ((-5:ℝ)/1) * d 7 + ((-666312085903757040:ℝ)/1) * d 8 + ((-8:ℝ)/1) * d 9 ≤ ((-1839929964484238216:ℝ)/1) := by convert combined using 1 <;> ring
                  linarith only [aggregated, b0_0, b1_1, b1_2, lom2, lom5, b1_5, m15, m12, m13, m11]
                · have lom15 : ((1:ℝ)/2) ≤ d 6 := le_of_lt (lt_of_not_ge m15)
                  by_cases m16 : d 1 ≤ ((3:ℝ)/4)
                  ·
                    exfalso
                    have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                    have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                    have r2 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                    have r3cp := h.cp 2244 2200 1444 2712 1400 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    have r3 : 19747200 * d 0 + 12961344 * d 1 + 24342912 * d 2 + 12566400 * d 3 + 12707200 * d 4 + 23865600 * d 5 + 12320000 * d 6 + 15664512 * d 7 + 8086400 * d 8 + 15187200 * d 9 ≤ 100000000 := by linarith only [r3cp]
                    have r4cp := h.cp 2175 2264 1422 2627 1511 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    have r4 : 19696800 * d 0 + 12371400 * d 1 + 22854900 * d 2 + 13145700 * d 3 + 12877632 * d 4 + 23790112 * d 5 + 13683616 * d 6 + 14942376 * d 7 + 8594568 * d 8 + 15877588 * d 9 ≤ 99980001 := by linarith only [r4cp]
                    have r5cp := h.cp 2215 2235 1400 2746 1404 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    have r5 : 19802100 * d 0 + 12404000 * d 1 + 24329560 * d 2 + 12439440 * d 3 + 12516000 * d 4 + 24549240 * d 5 + 12551760 * d 6 + 15377600 * d 7 + 7862400 * d 8 + 15421536 * d 9 ≤ 100000000 := by linarith only [r5cp]
                    have r6pt0 := plane_hh m16 b1_5
                    have r6pt1 := plane_lh b0_0 m12
                    have r6pt2 := plane_hl b1_2 lom5
                    have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 5 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r6pt0, r6pt1, r6pt2]
                    have r7pt0 := plane_hh m16 b1_6
                    have r7pt1 := plane_lh b0_0 m13
                    have r7pt2 := plane_hl b1_3 lom5
                    have r7 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 6 ≤ ((1:ℝ)/4) := by linarith only [h.pt4, r7pt0, r7pt1, r7pt2]
                    have r8pt0 := plane_hh b1_2 m13
                    have r8pt1 := plane_hl m16 b0_9
                    have r8pt2 := plane_lh lom2 m12
                    have r8 : ((1:ℝ)/2) * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                    have r9pt0 := plane_hh b1_2 m13
                    have r9pt1 := plane_hl m16 b0_9
                    have r9pt2 := plane_hl b1_3 b0_7
                    have r9 : ((1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r9pt0, r9pt1, r9pt2]
                    have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                    have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤317824561130941389471744 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤381079569070515290112000 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤486735154371394491383808 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤3084725198496351 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤23024883428737612 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤14280220768994432 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤59263445829925554094080 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤137347431864382261297152 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤138653530526988690784256 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤55900783699314945818624 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤84699960378109963796480 by norm_num)))
                    have aggregated : 193136640 * d 0 + 554985760 * d 1 + 101919472 * d 2 + ((-97679824:ℝ)/1) * d 3 + ((-870628992:ℝ)/1) * d 4 + ((-207637376:ℝ)/1) * d 5 + ((-135987584:ℝ)/1) * d 6 + 70970464 * d 7 + ((-162196256:ℝ)/1) * d 8 + 43398640 * d 9 ≤ ((-9099643258450076724:ℝ)/1) := by convert combined using 1 <;> ring
                    linarith only [aggregated, b0_0, lom14, b0_2, b1_3, b1_4, b1_5, b1_6, b0_7, m13, b0_9]
                  · have lom16 : ((3:ℝ)/4) ≤ d 1 := le_of_lt (lt_of_not_ge m16)
                    by_cases m17 : d 7 ≤ ((1:ℝ)/4)
                    ·
                      exfalso
                      have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                      have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                      have r2 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                      have r3 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
                      have r4cp := h.cp 2175 2264 1422 2627 1511 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r4 : 19696800 * d 0 + 12371400 * d 1 + 22854900 * d 2 + 13145700 * d 3 + 12877632 * d 4 + 23790112 * d 5 + 13683616 * d 6 + 14942376 * d 7 + 8594568 * d 8 + 15877588 * d 9 ≤ 99980001 := by linarith only [r4cp]
                      have r5cp := h.cp 2163 2267 1473 2520 1577 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r5 : 19614084 * d 0 + 12744396 * d 1 + 21803040 * d 2 + 13644204 * d 3 + 13357164 * d 4 + 22851360 * d 5 + 14300236 * d 6 + 14847840 * d 7 + 9291684 * d 8 + 15896160 * d 9 ≤ 100000000 := by linarith only [r5cp]
                      have r6pt0 := plane_hh b1_1 b1_5
                      have r6pt1 := plane_lh b0_0 m17
                      have r6pt2 := plane_hl b1_2 lom5
                      have r6 : ((-1:ℝ)/4) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r6pt0, r6pt1, r6pt2]
                      have r7pt0 := plane_hh b1_2 b1_6
                      have r7pt1 := plane_lh b0_0 m11
                      have r7pt2 := plane_lh lom2 b1_5
                      have r7 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 5 + 1 * d 6 ≤ ((1:ℝ)/2) := by linarith only [h.pt7, r7pt0, r7pt1, r7pt2]
                      have r8pt0 := plane_hh b1_2 m13
                      have r8pt1 := plane_lh lom16 m11
                      have r8pt2 := plane_lh lom2 m17
                      have r8 : ((-1:ℝ)/2) * d 1 + ((1:ℝ)/2) * d 2 + ((-1:ℝ)/4) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ 0 := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                      have r9pt0 := plane_hh b1_2 m13
                      have r9pt1 := plane_hl b1_1 b0_9
                      have r9pt2 := plane_lh lom2 m17
                      have r9 : ((1:ℝ)/2) * d 2 + ((-1:ℝ)/4) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((3:ℝ)/8) := by linarith only [h.pt10, r9pt0, r9pt1, r9pt2]
                      have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                      have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤717250539548755695239168 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤524653578618365471096832 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤1028443882860111619686400 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤91634274822034645057536 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤6119440958139089 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤72238685937612912 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤418091619191110848479232 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤382004071458666144858112 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤216525286394670939635712 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤54641824521587588595712 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤168618665626718741463040 by norm_num)))
                      have aggregated : 472782944 * d 0 + ((-1652760184:ℝ)/1) * d 1 + ((-22783692:ℝ)/1) * d 2 + ((-26440988:ℝ)/1) * d 3 + 128397952 * d 4 + ((-689858016:ℝ)/1) * d 5 + 5111520 * d 6 + 143643432 * d 7 + ((-303146296:ℝ)/1) * d 8 + 156046356 * d 9 ≤ ((-6085779313256212937807:ℝ)/1) := by convert combined using 1 <;> ring
                      linarith only [aggregated, b0_0, b1_1, b1_2, b1_3, lom5, b1_5, lom15, b0_7, m13, b0_9]
                    · have lom17 : ((1:ℝ)/4) ≤ d 7 := le_of_lt (lt_of_not_ge m17)
                      exfalso
                      have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                      have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                      have r2 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                      have r3cp := h.cp 1899 2528 1534 2593 1445 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r3 : 19202688 * d 0 + 11652264 * d 1 + 19696428 * d 2 + 10976220 * d 3 + 15511808 * d 4 + 26220416 * d 5 + 14611840 * d 6 + 15910648 * d 7 + 8866520 * d 8 + 14987540 * d 9 ≤ 99980001 := by linarith only [r3cp]
                      have r4cp := h.cp 2221 2176 1670 2310 1624 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r4 : 19331584 * d 0 + 14836280 * d 1 + 20522040 * d 2 + 14427616 * d 3 + 14535680 * d 4 + 20106240 * d 5 + 14135296 * d 6 + 15430800 * d 7 + 10848320 * d 8 + 15005760 * d 9 ≤ 100020001 := by linarith only [r4cp]
                      have r5pt0 := plane_hh b1_1 b1_5
                      have r5pt1 := plane_lh b0_0 m12
                      have r5pt2 := plane_hl b1_2 lom5
                      have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
                      have r6pt0 := plane_ll lom16 lom15
                      have r6pt1 := plane_lh b0_0 m13
                      have r6pt2 := plane_hl b1_3 lom5
                      have r6 : ((-1:ℝ)/2) * d 0 + ((1:ℝ)/2) * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 6 ≤ ((-1:ℝ)/8) := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
                      have r7pt0 := plane_hh b1_1 b1_6
                      have r7pt1 := plane_lh b0_0 m13
                      have r7pt2 := plane_hl b1_3 lom5
                      have r7 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 4 + 1 * d 6 ≤ ((1:ℝ)/2) := by linarith only [h.pt4, r7pt0, r7pt1, r7pt2]
                      have r8pt0 := plane_hh b1_2 m13
                      have r8pt1 := plane_lh lom16 m11
                      have r8pt2 := plane_hl b1_3 lom17
                      have r8 : ((-1:ℝ)/2) * d 1 + ((1:ℝ)/2) * d 2 + ((-1:ℝ)/4) * d 3 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((-1:ℝ)/8) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                      have r9pt0 := plane_hh b1_2 m13
                      have r9pt1 := plane_hl b1_1 b0_9
                      have r9pt2 := plane_hl b1_3 lom17
                      have r9 : ((1:ℝ)/2) * d 2 + ((-1:ℝ)/4) * d 3 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt10, r9pt0, r9pt1, r9pt2]
                      have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                      have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤23606054217122794438656 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤17721962117335879778304 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤9418455207863403937792 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤1600769511669047 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤928511612318383 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤3421283365270566469632 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤5895891138736995434496 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤5404148269077731737600 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤7489350872310388621312 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤22889151136486811238400 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤5338583600117516861440 by norm_num)))
                      have aggregated : 3469184 * d 0 + ((-10677152:ℝ)/1) * d 1 + 7083196 * d 2 + ((-16602012:ℝ)/1) * d 3 + 1932032 * d 4 + ((-4194176:ℝ)/1) * d 5 + ((-6582656:ℝ)/1) * d 6 + ((-88648:ℝ)/1) * d 7 + 733224 * d 8 + 918284 * d 9 ≤ ((-214078285806286596890:ℝ)/1) := by convert combined using 1 <;> ring
                      linarith only [aggregated, b0_0, b1_1, b0_2, b1_3, lom5, b1_5, b1_6, m12, b0_8, b0_9]
            · have lom13 : ((1:ℝ)/2) ≤ d 8 := le_of_lt (lt_of_not_ge m13)
              by_cases m18 : d 1 ≤ ((1:ℝ)/2)
              ·
                exfalso
                have r0cp := h.cp 1 3 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                have r0 : 12 * d 0 + 4 * d 1 + 8 * d 2 + 12 * d 3 + 12 * d 4 + 24 * d 5 + 36 * d 6 + 8 * d 7 + 12 * d 8 + 24 * d 9 ≤ 100 := by linarith only [r0cp]
                have r1pt0 := plane_hh b1_2 b1_8
                have r1pt1 := plane_hl m18 b0_9
                have r1pt2 := plane_lh lom2 m12
                have r1 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt10, r1pt0, r1pt1, r1pt2]
                have r2pt0 := plane_hh b1_5 b1_8
                have r2pt1 := plane_lh lom5 m11
                have r2pt2 := plane_lh b0_6 m12
                have r2 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt13, r2pt0, r2pt1, r2pt2]
                have r3 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                have combined := (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤2962221929438545 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤71093326306525064 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤71093326306525064 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤14811109647192722 by norm_num)))
                have aggregated : 35546663153262540 * d 0 + ((-165884428048558484:ℝ)/1) * d 1 + ((-82942214024279240:ℝ)/1) * d 2 + 8 * d 3 + 8 * d 4 + ((-35546663153262520:ℝ)/1) * d 5 + ((-106639989459787576:ℝ)/1) * d 6 + ((-11848887717754172:ℝ)/1) * d 7 + 4 * d 8 + 16 * d 9 ≤ ((-322882190308801282:ℝ)/1) := by convert combined using 1 <;> ring
                linarith only [aggregated, b0_0, m18, b1_2, lom2, lom5, b1_5, b1_6, m12, lom13, b0_9]
              · have lom18 : ((1:ℝ)/2) ≤ d 1 := le_of_lt (lt_of_not_ge m18)
                by_cases m19 : d 6 ≤ ((1:ℝ)/2)
                ·
                  exfalso
                  have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                  have r1 : ((-1:ℝ)/1) * d 0 + 1 * d 3 + ((-1:ℝ)/1) * d 6 ≤ 0 := by linarith only [h.tri014]
                  have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
                  have r3cp := h.cp 2 1 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r3 : 8 * d 0 + 8 * d 1 + 16 * d 2 + 8 * d 3 + 4 * d 4 + 8 * d 5 + 4 * d 6 + 8 * d 7 + 4 * d 8 + 8 * d 9 ≤ 49 := by linarith only [r3cp]
                  have r4cp := h.cp 3 0 3 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r4 : 36 * d 1 + 12 * d 3 + 12 * d 8 ≤ 49 := by linarith only [r4cp]
                  have r5cp := h.cp 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  have r5 : 12 * d 0 + 36 * d 1 + 12 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 8 * d 6 + 12 * d 7 + 24 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r5cp]
                  have r6pt0 := plane_hh b1_5 b1_8
                  have r6pt1 := plane_lh lom5 m11
                  have r6pt2 := plane_hl m19 b0_7
                  have r6 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt13, r6pt0, r6pt1, r6pt2]
                  have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                  have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤754701467330494720 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤31445894472103848 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤1100606306523638144 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤86476209798285840 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤15722947236051970 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤7861473618025993 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤1572294723605197312 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤191295858038632320 by norm_num)))
                  have aggregated : 68 * d 0 + 268 * d 1 + ((-817593256274702484:ℝ)/1) * d 2 + ((-104:ℝ)/1) * d 3 + 44 * d 4 + 164 * d 5 + ((-1918199562798340384:ℝ)/1) * d 6 + ((-20:ℝ)/1) * d 7 + 304 * d 8 + ((-31445894472103992:ℝ)/1) * d 9 ≤ ((-2400369944703933706:ℝ)/1) := by convert combined using 1 <;> ring
                  linarith only [aggregated, b0_0, lom18, b1_2, b1_3, lom5, b0_5, m19, m12, lom13, m11]
                · have lom19 : ((1:ℝ)/2) ≤ d 6 := le_of_lt (lt_of_not_ge m19)
                  by_cases m20 : d 3 ≤ ((3:ℝ)/4)
                  ·
                    by_cases m21 : d 2 ≤ ((1:ℝ)/2)
                    ·
                      exfalso
                      have r0 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                      have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
                      have r2cp := h.cp 0 1 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r2 : 4 * d 4 + 4 * d 6 + 4 * d 8 ≤ 9 := by linarith only [r2cp]
                      have r3cp := h.cp 1 2 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r3 : 8 * d 0 + 12 * d 1 + 4 * d 2 + 12 * d 3 + 24 * d 4 + 8 * d 5 + 24 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r3cp]
                      have r4cp := h.cp 1 3 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r4 : 12 * d 0 + 8 * d 1 + 4 * d 2 + 12 * d 3 + 24 * d 4 + 12 * d 5 + 36 * d 6 + 8 * d 7 + 24 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r4cp]
                      have r5pt0 := plane_hh b1_1 b1_5
                      have r5pt1 := plane_lh b0_0 m12
                      have r5pt2 := plane_hl m21 lom5
                      have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/2) * d 4 + 1 * d 5 ≤ ((3:ℝ)/4) := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
                      have r6pt0 := plane_hh b1_1 b1_6
                      have r6pt1 := plane_hl m1 lom13
                      have r6pt2 := plane_lh lom2 b1_4
                      have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ ((1:ℝ)/4) := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
                      have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                      have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤141785788072274640 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤47261929357424888 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤7876988226237515 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤3938494113118738 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤11815482339356224 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤409603387764349056 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤31507952904949896 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤48574760728464472 by norm_num)))
                      have aggregated : 4 * d 0 + ((-64:ℝ)/1) * d 1 + ((-724682916813848344:ℝ)/1) * d 2 + 157539764524749648 * d 3 + 189047717429699672 * d 4 + ((-16:ℝ)/1) * d 5 + 68 * d 6 + 8 * d 7 + 32 * d 8 + 16 * d 9 ≤ ((-418793207361626027:ℝ)/1) := by convert combined using 1 <;> ring
                      linarith only [aggregated, b0_0, b1_1, m21, lom2, lom5, b1_5, lom19, b0_7, lom13, b0_9]
                    · have lom21 : ((1:ℝ)/2) ≤ d 2 := le_of_lt (lt_of_not_ge m21)
                      by_cases m22 : d 5 ≤ ((1:ℝ)/2)
                      ·
                        exfalso
                        have r0 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                        have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
                        have r2cp := h.cp 1 0 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r2 : 4 * d 1 + 4 * d 3 + 4 * d 8 ≤ 9 := by linarith only [r2cp]
                        have r3cp := h.cp 2 1 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r3 : 8 * d 0 + 24 * d 1 + 8 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 12 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r3cp]
                        have r4cp := h.cp 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r4 : 12 * d 0 + 36 * d 1 + 12 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 8 * d 6 + 12 * d 7 + 24 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r4cp]
                        have r5pt0 := plane_hh b1_1 b1_6
                        have r5pt1 := plane_hl m1 lom13
                        have r5pt2 := plane_lh lom2 b1_4
                        have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ ((1:ℝ)/4) := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
                        have r6pt0 := plane_hh b1_2 b1_6
                        have r6pt1 := plane_lh b0_0 m11
                        have r6pt2 := plane_lh lom2 m22
                        have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/2) * d 5 + 1 * d 6 ≤ ((3:ℝ)/4) := by linarith only [h.pt7, r6pt0, r6pt1, r6pt2]
                        have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤141785788072274640 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤47261929357424904 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤7876988226237530 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤3938494113118735 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤11815482339356228 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤31507952904949832 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤409603387764349248 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤48574760728464480 by norm_num)))
                        have aggregated : ((-20:ℝ)/1) * d 0 + 40 * d 1 + 104 * d 2 + 173293740977224776 * d 3 + 173293740977224640 * d 4 + ((-724682916813848532:ℝ)/1) * d 5 + ((-36:ℝ)/1) * d 6 + 12 * d 7 + 16 * d 8 + 4 * d 9 ≤ ((-418793207361626056:ℝ)/1) := by convert combined using 1 <;> ring
                        linarith only [aggregated, m1, lom18, lom21, lom2, lom5, m22, b1_6, b0_7, lom13, b0_9]
                      · have lom22 : ((1:ℝ)/2) ≤ d 5 := le_of_lt (lt_of_not_ge m22)
                        by_cases m23 : d 4 ≤ ((3:ℝ)/4)
                        ·
                          exfalso
                          have r0 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                          have r1 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
                          have r2cp := h.cp 1975 2248 1757 2230 1790 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                          have r2 : 17759200 * d 0 + 13880300 * d 1 + 17617000 * d 2 + 14141000 * d 3 + 15798944 * d 4 + 20052160 * d 5 + 16095680 * d 6 + 15672440 * d 7 + 12580120 * d 8 + 15966800 * d 9 ≤ 100000000 := by linarith only [r2cp]
                          have r3pt0 := plane_hh b1_1 b1_5
                          have r3pt1 := plane_lh b0_0 m12
                          have r3pt2 := plane_lh lom21 m23
                          have r3 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-3:ℝ)/4) * d 2 + ((-1:ℝ)/2) * d 4 + 1 * d 5 ≤ ((5:ℝ)/8) := by linarith only [h.pt1, r3pt0, r3pt1, r3pt2]
                          have r4pt0 := plane_hh b1_1 b1_5
                          have r4pt1 := plane_lh b0_0 m12
                          have r4pt2 := plane_hl b1_2 lom5
                          have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
                          have r5pt0 := plane_hh b1_2 b1_6
                          have r5pt1 := plane_lh b0_0 m11
                          have r5pt2 := plane_lh lom2 b1_5
                          have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 5 + 1 * d 6 ≤ ((1:ℝ)/2) := by linarith only [h.pt7, r5pt0, r5pt1, r5pt2]
                          have r6pt0 := plane_hh b1_2 b1_6
                          have r6pt1 := plane_lh b0_0 m11
                          have r6pt2 := plane_hl m20 lom22
                          have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 5 + 1 * d 6 ≤ ((5:ℝ)/8) := by linarith only [h.pt7, r6pt0, r6pt1, r6pt2]
                          have r7pt0 := plane_hh b1_2 b1_8
                          have r7pt1 := plane_lh lom18 m11
                          have r7pt2 := plane_hl m20 b0_7
                          have r7 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
                          have r8pt0 := plane_hh b1_2 b1_8
                          have r8pt1 := plane_hl b1_1 b0_9
                          have r8pt2 := plane_hl m20 b0_7
                          have r8 : 1 * d 2 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 1 := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                          have r9pt0 := plane_hh b1_5 b1_8
                          have r9pt1 := plane_hl m23 b0_9
                          have r9pt2 := plane_lh lom19 m12
                          have r9 : 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt13, r9pt0, r9pt1, r9pt2]
                          have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                          have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤76312943028104964603904 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤22158906594192670064640 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤8595883866901773 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤18232031775510210019328 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤148848778550122144333824 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤60559743122799020998656 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤77671488089732576968704 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤36729170433340392603648 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤29733997324332714426368 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤17116310609252472324096 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤22335805995559912734720 by norm_num)))
                          have aggregated : ((-9098656:ℝ)/1) * d 0 + ((-114993412:ℝ)/1) * d 1 + 557440328 * d 2 + ((-7554648:ℝ)/1) * d 3 + ((-14151136:ℝ)/1) * d 4 + ((-12885568:ℝ)/1) * d 5 + ((-61370688:ℝ)/1) * d 6 + ((-7802344:ℝ)/1) * d 7 + ((-76305864:ℝ)/1) * d 8 + ((-438768:ℝ)/1) * d 9 ≤ ((-104038233743736345344:ℝ)/1) := by convert combined using 1 <;> ring
                          linarith only [aggregated, m1, b1_1, lom21, m20, m23, b1_5, b1_6, m12, b1_8, m11]
                        · have lom23 : ((3:ℝ)/4) ≤ d 4 := le_of_lt (lt_of_not_ge m23)
                          exfalso
                          have r0 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
                          have r1cp := h.cp 2218 2022 1733 2192 1835 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                          have r1 : 17939184 * d 0 + 15375176 * d 1 + 19447424 * d 2 + 16280120 * d 3 + 14016504 * d 4 + 17728896 * d 5 + 14841480 * d 6 + 15194944 * d 7 + 12720220 * d 8 + 16089280 * d 9 ≤ 100000000 := by linarith only [r1cp]
                          have r2cp := h.cp 1975 2248 1757 2230 1790 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                          have r2 : 17759200 * d 0 + 13880300 * d 1 + 17617000 * d 2 + 14141000 * d 3 + 15798944 * d 4 + 20052160 * d 5 + 16095680 * d 6 + 15672440 * d 7 + 12580120 * d 8 + 15966800 * d 9 ≤ 100000000 := by linarith only [r2cp]
                          have r3cp := h.cp 1966 2215 1834 2164 1821 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                          have r3 : 17418760 * d 0 + 14422576 * d 1 + 17017696 * d 2 + 14320344 * d 3 + 16249240 * d 4 + 19173040 * d 5 + 16134060 * d 6 + 15875104 * d 7 + 13358856 * d 8 + 15762576 * d 9 ≤ 100000000 := by linarith only [r3cp]
                          have r4pt0 := plane_hh b1_1 b1_5
                          have r4pt1 := plane_lh b0_0 m12
                          have r4pt2 := plane_hl b1_2 lom23
                          have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-3:ℝ)/4) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
                          have r5pt0 := plane_hh b1_2 b1_6
                          have r5pt1 := plane_lh b0_0 m11
                          have r5pt2 := plane_hl m20 lom22
                          have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 5 + 1 * d 6 ≤ ((5:ℝ)/8) := by linarith only [h.pt7, r5pt0, r5pt1, r5pt2]
                          have r6pt0 := plane_hh b1_2 b1_8
                          have r6pt1 := plane_lh lom18 m11
                          have r6pt2 := plane_hl m20 b0_7
                          have r6 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/4) := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
                          have r7pt0 := plane_hh b1_2 b1_8
                          have r7pt1 := plane_hl b1_1 b0_9
                          have r7pt2 := plane_hl m20 b0_7
                          have r7 : 1 * d 2 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 1 := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
                          have r8pt0 := plane_hh b1_5 b1_8
                          have r8pt1 := plane_lh lom23 m11
                          have r8pt2 := plane_hl b1_6 b0_7
                          have r8 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((5:ℝ)/8) := by linarith only [h.pt13, r8pt0, r8pt1, r8pt2]
                          have r9 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                          have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤886120611582755483942912 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤26485007975732256 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤7522662402219369 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤100032759032634096 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤2534445066139146878189568 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤2167879972218668354371584 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤385660028688512011206656 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤1293348383513766956892160 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤849110832068137865707520 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤357997799280212908703744 by norm_num)))
                          have aggregated : 562824288 * d 0 + 370300364 * d 1 + ((-1099072344:ℝ)/1) * d 2 + 132300040 * d 3 + 42653781048431286685984 * d 4 + ((-1765598272:ℝ)/1) * d 5 + ((-1071158784:ℝ)/1) * d 6 + 2492568376 * d 7 + ((-2995723816:ℝ)/1) * d 8 + 749380048 * d 9 ≤ ((-36025299427668854089472:ℝ)/1) := by convert combined using 1 <;> ring
                          linarith only [aggregated, b0_0, lom18, b1_2, lom2, lom23, b1_5, b1_6, b0_7, b1_8, b0_9]
                  · have lom20 : ((3:ℝ)/4) ≤ d 3 := le_of_lt (lt_of_not_ge m20)
                    by_cases m24 : d 1 ≤ ((3:ℝ)/4)
                    ·
                      have tst0 : 4*d 1<3*(d 7+d 8) := by
                        apply lt_of_not_ge
                        intro outside
                        have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                        have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                        have r2 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                        have r3cp := h.cp 3 3 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r3 : 36 * d 0 + 24 * d 1 + 36 * d 2 + 36 * d 3 + 24 * d 4 + 36 * d 5 + 36 * d 6 + 24 * d 7 + 24 * d 8 + 36 * d 9 ≤ 196 := by linarith only [r3cp]
                        have r4cp := h.cp 1755 2480 1661 2248 1855 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r4 : 17409600 * d 0 + 11660220 * d 1 + 15780960 * d 2 + 13022100 * d 3 + 16477120 * d 4 + 22300160 * d 5 + 18401600 * d 6 + 14935712 * d 7 + 12324620 * d 8 + 16680160 * d 9 ≤ 99980001 := by linarith only [r4cp]
                        have r5pt0 := plane_hh m24 b1_5
                        have r5pt1 := plane_lh b0_0 m12
                        have r5pt2 := plane_hl b1_2 lom5
                        have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 5 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
                        have r6pt0 := plane_hh b1_2 b1_6
                        have r6pt1 := plane_lh b0_0 m11
                        have r6pt2 := plane_lh lom20 b1_5
                        have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-3:ℝ)/4) * d 5 + 1 * d 6 ≤ ((1:ℝ)/4) := by linarith only [h.pt7, r6pt0, r6pt1, r6pt2]
                        have r7pt0 := plane_ll b0_2 lom13
                        have r7pt1 := plane_hl m24 b0_9
                        have r7pt2 := plane_lh lom20 m12
                        have r7 : ((1:ℝ)/2) * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + ((-3:ℝ)/4) * d 9 ≤ ((-3:ℝ)/8) := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
                        have r8pt0 := plane_hh b1_2 b1_8
                        have r8pt1 := plane_hl m24 b0_9
                        have r8pt2 := plane_lh lom20 m12
                        have r8 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((5:ℝ)/8) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                        have r9 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have r10 : ((-4:ℝ)/1) * d 1 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤90091017278399243616256 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤33853292670424073633792 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤60601348552331945312256 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤522386731203082911744 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤8852707994264445 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤68313396216929330397184 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤29654038725938571640832 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤99898255882281671458816 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤41260623515836942909440 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤20434770428910855258112 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤7237243176538615054336 by norm_num)))
                        have aggregated : ((-1774272:ℝ)/1) * d 0 + 7458508 * d 1 + ((-157226272:ℝ)/1) * d 2 + 61598532 * d 3 + ((-12133184:ℝ)/1) * d 4 + ((-3396096:ℝ)/1) * d 5 + ((-21887936:ℝ)/1) * d 6 + 331316256 * d 7 + ((-75694884:ℝ)/1) * d 8 + 103645536 * d 9 ≤ ((-1004295104301013550371:ℝ)/1) := by convert combined using 1 <;> ring
                        linarith only [aggregated, m1, lom18, b1_2, lom20, b1_4, b1_5, b1_6, b0_7, b1_8, b0_9]
                      have tst1 : 4*d 1<3*(d 2+d 3) := by
                        apply lt_of_not_ge
                        intro outside
                        have r0 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                        have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
                        have r2cp := h.cp 1 2 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r2 : 8 * d 0 + 12 * d 1 + 4 * d 2 + 12 * d 3 + 24 * d 4 + 8 * d 5 + 24 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r2cp]
                        have r3cp := h.cp 1 3 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r3 : 12 * d 0 + 8 * d 1 + 4 * d 2 + 12 * d 3 + 24 * d 4 + 12 * d 5 + 36 * d 6 + 8 * d 7 + 24 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r3cp]
                        have r4pt0 := plane_hh m24 b1_5
                        have r4pt1 := plane_lh b0_0 m12
                        have r4pt2 := plane_hl b1_2 lom5
                        have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 5 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
                        have r5pt0 := plane_hh m24 b1_5
                        have r5pt1 := plane_hl m1 b0_7
                        have r5pt2 := plane_hl b1_2 lom5
                        have r5 : 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
                        have r6pt0 := plane_ll lom20 b0_5
                        have r6pt1 := plane_hl m1 b0_9
                        have r6pt2 := plane_lh b0_2 b1_6
                        have r6 : ((-1:ℝ)/1) * d 2 + ((3:ℝ)/4) * d 5 + ((-1:ℝ)/2) * d 9 ≤ 0 := by linarith only [h.pt8, r6pt0, r6pt1, r6pt2]
                        have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have r8 : ((-4:ℝ)/1) * d 1 + 3 * d 2 + 3 * d 3 ≤ 0 := by linarith only [outside]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤227647595715699840 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤10840361700747328 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤4065135637780341 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤23035768614088660 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤639581340344108800 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤10840361700747134 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤173445787211961728 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤77237577117826672 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤439034648880277824 by norm_num)))
                        have aggregated : ((-424:ℝ)/1) * d 0 + ((-1799500042324102054:ℝ)/1) * d 1 + ((-283:ℝ)/1) * d 2 + 1642314797663261484 * d 3 + 90 * d 4 + ((-339:ℝ)/2) * d 5 + ((-120:ℝ)/1) * d 6 + ((-35:ℝ)/1) * d 7 + ((-108:ℝ)/1) * d 8 + ((-20:ℝ)/1) * d 9 ≤ ((-1823890856150785689:ℝ)/2) := by convert combined using 1 <;> ring
                        linarith only [aggregated, m1, m24, b1_2, lom20, lom5, b1_5, b1_6, m12, b1_8, m11]
                      have tst2 : 4*d 4<3*(d 7+d 8) := by
                        apply lt_of_not_ge
                        intro outside
                        have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                        have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                        have r2 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                        have r3cp := h.cp 1914 2388 1436 2388 1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r3 : 18282528 * d 0 + 10994016 * d 1 + 18282528 * d 2 + 14347344 * d 3 + 13716672 * d 4 + 22810176 * d 5 + 17900448 * d 6 + 13716672 * d 7 + 10764256 * d 8 + 17900448 * d 9 ≤ 100000000 := by linarith only [r3cp]
                        have r4cp := h.cp 1755 2480 1661 2248 1855 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r4 : 17409600 * d 0 + 11660220 * d 1 + 15780960 * d 2 + 13022100 * d 3 + 16477120 * d 4 + 22300160 * d 5 + 18401600 * d 6 + 14935712 * d 7 + 12324620 * d 8 + 16680160 * d 9 ≤ 99980001 := by linarith only [r4cp]
                        have r5cp := h.cp 1805 2510 1522 2421 1742 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r5 : 18122200 * d 0 + 10988840 * d 1 + 17479620 * d 2 + 12577240 * d 3 + 15280880 * d 4 + 24306840 * d 5 + 17489680 * d 6 + 14739048 * d 7 + 10605296 * d 8 + 16869528 * d 9 ≤ 100000000 := by linarith only [r5cp]
                        have r6pt0 := plane_hh m24 b1_5
                        have r6pt1 := plane_lh b0_0 m12
                        have r6pt2 := plane_hl b1_2 lom5
                        have r6 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 5 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r6pt0, r6pt1, r6pt2]
                        have r7pt0 := plane_ll b0_2 lom13
                        have r7pt1 := plane_hl m24 b0_9
                        have r7pt2 := plane_lh lom20 m12
                        have r7 : ((1:ℝ)/2) * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + ((-3:ℝ)/4) * d 9 ≤ ((-3:ℝ)/8) := by linarith only [h.pt10, r7pt0, r7pt1, r7pt2]
                        have r8pt0 := plane_hh b1_2 b1_8
                        have r8pt1 := plane_hl m24 b0_9
                        have r8pt2 := plane_lh lom20 m12
                        have r8 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((5:ℝ)/8) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                        have r9 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have r10 : ((-4:ℝ)/1) * d 4 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤6643353999428682743021568 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤3909448481579885393870848 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤3917523344123285523660800 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤140793204538385184 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤499857148357515904 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤5415212291791847 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤1643403586827012903272448 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤6776720768842342009405440 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤2598995737289485008764928 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤1310215962458648322506752 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤490853011444058900398080 by norm_num)))
                        have aggregated : ((-1295281688:ℝ)/1) * d 0 + 3117398296 * d 1 + ((-1321938468:ℝ)/1) * d 2 + ((-1520364056:ℝ)/1) * d 3 + ((-1618196848:ℝ)/1) * d 4 + 4210283816 * d 5 + 4203637616 * d 6 + 2508998616 * d 7 + 5879300240 * d 8 + 1417276712 * d 9 ≤ ((-110069340617673160625792:ℝ)/1) := by convert combined using 1 <;> ring
                        linarith only [aggregated, m1, lom18, b1_2, b1_3, b1_4, b0_5, lom19, b0_7, lom13, b0_9]
                      have tst3 : 4*d 4<3*(d 5+d 6) := by
                        apply lt_of_not_ge
                        intro outside
                        have r0 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
                        have r1cp := h.cp 2 1 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r1 : 8 * d 0 + 24 * d 1 + 8 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 12 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r1cp]
                        have r2cp := h.cp 3 1 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r2 : 12 * d 0 + 24 * d 1 + 12 * d 2 + 36 * d 3 + 8 * d 4 + 4 * d 5 + 12 * d 6 + 8 * d 7 + 24 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r2cp]
                        have r3cp := h.cp 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r3 : 12 * d 0 + 36 * d 1 + 12 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 8 * d 6 + 12 * d 7 + 24 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r3cp]
                        have r4pt0 := plane_hh b1_2 b1_4
                        have r4pt1 := plane_lh b0_0 m12
                        have r4pt2 := plane_hl m24 b0_5
                        have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + 1 * d 4 + ((-3:ℝ)/4) * d 5 ≤ 1 := by linarith only [h.pt2, r4pt0, r4pt1, r4pt2]
                        have r5pt0 := plane_hh b1_3 b1_4
                        have r5pt1 := plane_lh b0_0 b1_8
                        have r5pt2 := plane_hl m24 lom19
                        have r5 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/2) * d 1 + 1 * d 3 + 1 * d 4 + ((-3:ℝ)/4) * d 6 ≤ ((5:ℝ)/8) := by linarith only [h.pt5, r5pt0, r5pt1, r5pt2]
                        have r6pt0 := plane_hh b1_2 b1_8
                        have r6pt1 := plane_hl m24 b0_9
                        have r6pt2 := plane_lh lom20 m12
                        have r6 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((5:ℝ)/8) := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
                        have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have r8 : ((-4:ℝ)/1) * d 4 + 3 * d 5 + 3 * d 6 ≤ 0 := by linarith only [outside]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤11638603973700196352 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤7301508139083991 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤197140719755273312 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤197140719755273312 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤4935819502020926464 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤2321879588228767232 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤5373909990365965312 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤1258293235968842496 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤5731683889181091840 by norm_num)))
                        have aggregated : 952 * d 0 + ((-4256779245086079064:ℝ)/1) * d 1 + 13240 * d 2 + 2728 * d 3 + ((-3180:ℝ)/1) * d 4 + ((-6820:ℝ)/1) * d 5 + 4384555637520064276 * d 6 + 148 * d 7 + ((-1988:ℝ)/1) * d 8 + 148 * d 9 ≤ ((-11752385808867586500:ℝ)/1) := by convert combined using 1 <;> ring
                        linarith only [aggregated, b0_0, m24, b0_2, lom20, b1_4, b1_5, lom19, b0_7, b1_8, b0_9]
                      have tst4 : 4*d 8<3*(d 4+d 1) := by
                        apply lt_of_not_ge
                        intro outside
                        have r0cp := h.cp 1 3 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r0 : 12 * d 0 + 4 * d 1 + 8 * d 2 + 12 * d 3 + 12 * d 4 + 24 * d 5 + 36 * d 6 + 8 * d 7 + 12 * d 8 + 24 * d 9 ≤ 100 := by linarith only [r0cp]
                        have r1cp := h.cp 1 3 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r1 : 12 * d 0 + 8 * d 1 + 4 * d 2 + 12 * d 3 + 24 * d 4 + 12 * d 5 + 36 * d 6 + 8 * d 7 + 24 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r1cp]
                        have r2cp := h.cp 3 1 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r2 : 12 * d 0 + 24 * d 1 + 12 * d 2 + 36 * d 3 + 8 * d 4 + 4 * d 5 + 12 * d 6 + 8 * d 7 + 24 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r2cp]
                        have r3cp := h.cp 1560 2624 1413 1926 2476 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r3 : 16373760 * d 0 + 8817120 * d 1 + 12018240 * d 2 + 15450240 * d 3 + 14830848 * d 4 + 20215296 * d 5 + 25988096 * d 6 + 10885752 * d 7 + 13994352 * d 8 + 19075104 * d 9 ≤ 99980001 := by linarith only [r3cp]
                        have r4pt0 := plane_hh m24 b1_6
                        have r4pt1 := plane_lh b0_0 b1_8
                        have r4pt2 := plane_hl b1_3 lom5
                        have r4 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 4 + ((3:ℝ)/4) * d 6 ≤ ((1:ℝ)/4) := by linarith only [h.pt4, r4pt0, r4pt1, r4pt2]
                        have r5pt0 := plane_hh b1_2 b1_8
                        have r5pt1 := plane_lh lom18 m11
                        have r5pt2 := plane_lh lom20 m12
                        have r5 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((3:ℝ)/8) := by linarith only [h.pt10, r5pt0, r5pt1, r5pt2]
                        have r6pt0 := plane_hh b1_5 b1_8
                        have r6pt1 := plane_lh lom5 m11
                        have r6pt2 := plane_lh lom19 m12
                        have r6 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r6pt0, r6pt1, r6pt2]
                        have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have r8 : 3 * d 1 + 3 * d 4 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤268837335139213901824 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤764286918575972941824 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤582941442463444434944 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤2530274464573123 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤60822895171192395661312 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤84130566262392568676352 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤57637603609788970696704 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤10561929642373562761216 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤21498523591040785448960 by norm_num)))
                        have aggregated : ((-1865728:ℝ)/1) * d 0 + ((-5618272:ℝ)/1) * d 1 + 41506496 * d 2 + 7512448 * d 3 + 38612455386602320340736 * d 4 + ((-663040:ℝ)/1) * d 5 + 37397504 * d 6 + ((-51444260618984058783384:ℝ)/1) * d 7 + 41308240 * d 8 + 9308256 * d 9 ≤ ((-27377651414056347809949:ℝ)/1) := by convert combined using 1 <;> ring
                        linarith only [aggregated, m1, m24, b0_2, lom20, lom5, b1_5, lom19, m12, lom13, b0_9]
                      have tst5 : 4*d 8<3*(d 6+d 3) := by
                        apply lt_of_not_ge
                        intro outside
                        have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 3 + ((-1:ℝ)/1) * d 6 ≤ 0 := by linarith only [h.tri014]
                        have r1cp := h.cp 2 1 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                        have r1 : 8 * d 0 + 24 * d 1 + 8 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 12 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r1cp]
                        have r2pt0 := plane_hh b1_2 b1_8
                        have r2pt1 := plane_hl m24 b0_9
                        have r2pt2 := plane_lh lom20 m12
                        have r2 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((5:ℝ)/8) := by linarith only [h.pt10, r2pt0, r2pt1, r2pt2]
                        have r3pt0 := plane_hh b1_5 b1_8
                        have r3pt1 := plane_lh lom5 m11
                        have r3pt2 := plane_lh lom19 m12
                        have r3 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r3pt0, r3pt1, r3pt2]
                        have r4 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                        have r5 : 3 * d 3 + 3 * d 6 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
                        have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤29256206532423416 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤3657025816552927 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤73140516331058512 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤87768619597270256 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤8533060238623495 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤47541335615188040 by norm_num)))
                        have aggregated : ((-14628103266211692:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + 223078574809728528 * d 3 + ((-4:ℝ)/1) * d 4 + 24 * d 5 + 10971077449658760 * d 6 + ((-54855387248293888:ℝ)/1) * d 7 + 40 * d 8 + ((-54855387248293888:ℝ)/1) * d 9 ≤ 37179762468288143 := by convert combined using 1 <;> ring
                        linarith only [aggregated, m24, b1_2, lom20, b1_4, b0_5, lom19, m12, lom13, m11]
                      exact ⟨2, tst0,tst1,tst2,tst3,tst4,tst5⟩
                    · have lom24 : ((3:ℝ)/4) ≤ d 1 := le_of_lt (lt_of_not_ge m24)
                      exfalso
                      have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
                      have r1 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
                      have r2 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
                      have r3cp := h.cp 1921 2258 1803 2127 1892 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r3 : 17350472 * d 0 + 13854252 * d 1 + 16343868 * d 2 + 14538128 * d 3 + 16284696 * d 4 + 19211064 * d 5 + 17088544 * d 6 + 15339924 * d 7 + 13645104 * d 8 + 16097136 * d 9 ≤ 100020001 := by linarith only [r3cp]
                      have r4cp := h.cp 1966 2215 1834 2164 1821 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                      have r4 : 17418760 * d 0 + 14422576 * d 1 + 17017696 * d 2 + 14320344 * d 3 + 16249240 * d 4 + 19173040 * d 5 + 16134060 * d 6 + 15875104 * d 7 + 13358856 * d 8 + 15762576 * d 9 ≤ 100000000 := by linarith only [r4cp]
                      have r5pt0 := plane_hh b1_1 b1_5
                      have r5pt1 := plane_lh b0_0 m12
                      have r5pt2 := plane_hl b1_2 lom5
                      have r5 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r5pt0, r5pt1, r5pt2]
                      have r6pt0 := plane_ll lom24 lom19
                      have r6pt1 := plane_hl m1 lom13
                      have r6pt2 := plane_lh lom20 b1_4
                      have r6 : ((-1:ℝ)/2) * d 0 + ((1:ℝ)/2) * d 1 + ((-1:ℝ)/1) * d 3 + ((-3:ℝ)/4) * d 4 + ((3:ℝ)/4) * d 6 + ((-1:ℝ)/2) * d 8 ≤ ((-5:ℝ)/8) := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
                      have r7pt0 := plane_hh b1_1 b1_6
                      have r7pt1 := plane_hl m1 lom13
                      have r7pt2 := plane_lh lom20 b1_4
                      have r7 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 3 + ((-3:ℝ)/4) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ 0 := by linarith only [h.pt4, r7pt0, r7pt1, r7pt2]
                      have r8pt0 := plane_ll b0_2 lom13
                      have r8pt1 := plane_lh lom24 m11
                      have r8pt2 := plane_lh lom20 m12
                      have r8 : ((-1:ℝ)/2) * d 1 + ((1:ℝ)/2) * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + ((-3:ℝ)/4) * d 9 ≤ ((-3:ℝ)/4) := by linarith only [h.pt10, r8pt0, r8pt1, r8pt2]
                      have r9pt0 := plane_hh b1_2 b1_8
                      have r9pt1 := plane_lh lom24 m11
                      have r9pt2 := plane_lh lom20 m12
                      have r9 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-3:ℝ)/4) * d 7 + 1 * d 8 + ((-3:ℝ)/4) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt10, r9pt0, r9pt1, r9pt2]
                      have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
                      have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤184331369368923238563840 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤89275693871643356037120 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤138023234478407067631616 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤2670657115220565 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤17971114882788140 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤90117902676407263166464 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤81147109363609254232064 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤264258628750414348288 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤138831189127578574127104 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤112152491484881690296320 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤40498747660938101391360 by norm_num)))
                      have aggregated : ((-132111288:ℝ)/1) * d 0 + ((-21572388:ℝ)/1) * d 1 + 33251180 * d 2 + 9293296 * d 3 + ((-23178728:ℝ)/1) * d 4 + 14546904 * d 5 + 7118896 * d 6 + ((-23145564:ℝ)/1) * d 7 + ((-59926960:ℝ)/1) * d 8 + ((-12498704:ℝ)/1) * d 9 ≤ ((-1951280760650601989131:ℝ)/1) := by convert combined using 1 <;> ring
                      linarith only [aggregated, m1, b1_1, b0_2, lom20, b1_4, b0_5, lom19, m12, b1_8, m11]
          · have lom12 : ((1:ℝ)/2) ≤ d 7 := le_of_lt (lt_of_not_ge m12)
            have tst0 : 4*d 1<3*(d 7+d 8) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
              have r1 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri043]
              have r2 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 2 + 1 * d 5 ≤ 0 := by linarith only [h.tri103]
              have r3 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
              have r4 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
              have r5cp := h.cp 3 3 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r5 : 36 * d 0 + 36 * d 1 + 36 * d 2 + 24 * d 3 + 36 * d 4 + 36 * d 5 + 24 * d 6 + 36 * d 7 + 24 * d 8 + 24 * d 9 ≤ 196 := by linarith only [r5cp]
              have r6cp := h.cp 1929 2347 1833 2459 1432 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r6 : 18109452 * d 0 + 14143428 * d 1 + 18973644 * d 2 + 11049312 * d 3 + 17208204 * d 4 + 23085092 * d 5 + 13443616 * d 6 + 18029388 * d 7 + 10499424 * d 8 + 14085152 * d 9 ≤ 100000000 := by linarith only [r6cp]
              have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r8 : ((-4:ℝ)/1) * d 1 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤11404496449591576625152 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤2089567091121734287360 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤441277408346081001472 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤5389300610605293502464 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤5565995468398599864320 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤176461760415959515136 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤293573523106597 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤1130922714416711729152 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤2084545809582517125120 by norm_num)))
              have aggregated : 534972 * d 0 + 914260 * d 1 + 610428 * d 2 + 84704 * d 3 + 841532 * d 4 + 348468 * d 5 + ((-1749344:ℝ)/1) * d 6 + 17899211758337896592892 * d 7 + ((-1911072:ℝ)/1) * d 8 + 714547386594625159328 * d 9 ≤ 8528644345768890238208 := by convert combined using 1 <;> ring
              linarith only [aggregated, b0_0, b0_1, b0_2, lom2, lom5, b0_5, b1_6, lom12, b1_8, b0_9]
            have tst1 : 4*d 1<3*(d 2+d 3) := by
              apply lt_of_not_ge
              intro outside
              have r0 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
              have r1 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
              have r2cp := h.cp 2 1 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r2 : 8 * d 0 + 24 * d 1 + 8 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 12 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r2cp]
              have r3cp := h.cp 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r3 : 12 * d 0 + 36 * d 1 + 12 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 8 * d 6 + 12 * d 7 + 24 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r3cp]
              have r4pt0 := plane_hh b1_1 b1_5
              have r4pt1 := plane_hl m1 lom12
              have r4pt2 := plane_hl b1_2 lom5
              have r4 : ((-1:ℝ)/2) * d 0 + 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((1:ℝ)/4) := by linarith only [h.pt1, r4pt0, r4pt1, r4pt2]
              have r5pt0 := plane_hh b1_1 b1_6
              have r5pt1 := plane_lh b0_0 b1_8
              have r5pt2 := plane_lh lom2 b1_4
              have r5 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 ≤ ((1:ℝ)/2) := by linarith only [h.pt4, r5pt0, r5pt1, r5pt2]
              have r6pt0 := plane_hh b1_1 b1_6
              have r6pt1 := plane_hl m1 b0_8
              have r6pt2 := plane_lh lom2 b1_4
              have r6 : 1 * d 1 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 4 + 1 * d 6 + ((-1:ℝ)/2) * d 8 ≤ ((1:ℝ)/2) := by linarith only [h.pt4, r6pt0, r6pt1, r6pt2]
              have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r8 : ((-4:ℝ)/1) * d 1 + 3 * d 2 + 3 * d 3 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤153740649623605504 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤290625396698116928 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤9909788861280592 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤4352897911029801 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤340081726155349120 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤115212872368533280 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤128178951252451680 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤33094372770382564 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤145220083499887648 by norm_num)))
              have aggregated : 12 * d 0 + ((-236:ℝ)/1) * d 1 + ((-36:ℝ)/1) * d 2 + 243947512716010488 * d 3 + 44 * d 4 + ((-76:ℝ)/1) * d 5 + ((-296:ℝ)/1) * d 6 + 1111378190050156 * d 7 + ((-72:ℝ)/1) * d 8 + 8 * d 9 ≤ 11360754831623424 := by convert combined using 1 <;> ring
              linarith only [aggregated, b0_0, b1_1, b1_2, lom2, lom5, b1_5, b1_6, lom12, b1_8, b0_9]
            have tst2 : 4*d 4<3*(d 7+d 8) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
              have r1 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri043]
              have r2 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 2 + 1 * d 5 ≤ 0 := by linarith only [h.tri103]
              have r3 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
              have r4 : 1 * d 7 + ((-1:ℝ)/1) * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri243]
              have r5cp := h.cp 3 3 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r5 : 36 * d 0 + 36 * d 1 + 36 * d 2 + 24 * d 3 + 36 * d 4 + 36 * d 5 + 24 * d 6 + 36 * d 7 + 24 * d 8 + 24 * d 9 ≤ 196 := by linarith only [r5cp]
              have r6 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r7 : ((-4:ℝ)/1) * d 4 + 3 * d 7 + 3 * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤21591713476402156 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤43183426952804376 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤21591713476402156 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤86366853905608560 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤43183426952804184 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤5397928369100531 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤17993094563668440 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤43183426952804248 by norm_num)))
              have aggregated : 64775140429206244 * d 0 + ((-8:ℝ)/1) * d 1 + 56 * d 2 + ((-192:ℝ)/1) * d 3 + ((-32:ℝ)/1) * d 4 + ((-8:ℝ)/1) * d 5 + 24 * d 6 + 367059129098836044 * d 7 + 24 * d 8 + 43183426952804184 * d 9 ≤ 176332326723950516 := by convert combined using 1 <;> ring
              linarith only [aggregated, b0_0, b1_1, b0_2, b1_3, b1_4, b1_5, b0_6, lom12, b0_8, b0_9]
            have tst3 : 4*d 4<3*(d 5+d 6) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 5 ≤ 0 := by linarith only [h.tri013]
              have r1 : ((-1:ℝ)/1) * d 0 + 1 * d 3 + ((-1:ℝ)/1) * d 6 ≤ 0 := by linarith only [h.tri014]
              have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
              have r3cp := h.cp 2 1 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r3 : 8 * d 0 + 24 * d 1 + 8 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 12 * d 6 + 12 * d 7 + 36 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r3cp]
              have r4cp := h.cp 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r4 : 12 * d 0 + 36 * d 1 + 12 * d 2 + 24 * d 3 + 12 * d 4 + 4 * d 5 + 8 * d 6 + 12 * d 7 + 24 * d 8 + 8 * d 9 ≤ 100 := by linarith only [r4cp]
              have r5pt0 := plane_hh b1_2 b1_4
              have r5pt1 := plane_hl m1 lom12
              have r5pt2 := plane_lh b0_1 b1_5
              have r5 : ((-1:ℝ)/2) * d 0 + ((-1:ℝ)/1) * d 1 + 1 * d 2 + 1 * d 4 + ((-1:ℝ)/2) * d 7 ≤ ((3:ℝ)/4) := by linarith only [h.pt2, r5pt0, r5pt1, r5pt2]
              have r6pt0 := plane_hh b1_2 b1_8
              have r6pt1 := plane_hl b1_1 b0_9
              have r6pt2 := plane_hl b1_3 lom12
              have r6 : 1 * d 2 + ((-1:ℝ)/2) * d 3 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
              have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r8 : ((-4:ℝ)/1) * d 4 + 3 * d 5 + 3 * d 6 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤178515614898608224 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤416536434763418304 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤1563003383778922752 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤1983506832206743 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤55538191301789168 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤174548601234194720 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤468107612400794240 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤156035870800264768 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤606953090655266944 by norm_num)))
              have aggregated : 72 * d 0 + ((-56:ℝ)/1) * d 1 + ((-368932270790456072:ℝ)/1) * d 2 + 296 * d 3 + 628 * d 4 + ((-964:ℝ)/1) * d 5 + ((-428:ℝ)/1) * d 6 + 134878464590059332 * d 7 + ((-196:ℝ)/1) * d 8 + 20 * d 9 ≤ ((-1528622598687339372:ℝ)/1) := by convert combined using 1 <;> ring
              linarith only [aggregated, b0_0, b1_1, b1_2, lom2, lom5, b1_5, b1_6, lom12, b1_8, b0_9]
            have tst4 : 4*d 8<3*(d 4+d 1) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
              have r1 : ((-1:ℝ)/1) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 5 ≤ 0 := by linarith only [h.tri013]
              have r2 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri043]
              have r3 : ((-1:ℝ)/1) * d 0 + ((-1:ℝ)/1) * d 3 + 1 * d 6 ≤ 0 := by linarith only [h.tri104]
              have r4 : ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [h.tri234]
              have r5cp := h.cp 1781 2025 1965 2173 2056 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r5 : 14426100 * d 0 + 13998660 * d 1 + 15480452 * d 2 + 14646944 * d 3 + 15916500 * d 4 + 17601300 * d 5 + 16653600 * d 6 + 17079780 * d 7 + 16160160 * d 8 + 17870752 * d 9 ≤ 100000000 := by linarith only [r5cp]
              have r6pt0 := plane_hh b1_5 b1_8
              have r6pt1 := plane_lh lom5 m11
              have r6pt2 := plane_hl b1_6 lom12
              have r6 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt13, r6pt0, r6pt1, r6pt2]
              have r7 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r8 : 3 * d 1 + 3 * d 4 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤4552631580636139225088 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤13321227778226208636928 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤23885561871661824737280 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤51044420861968223567872 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤47697436599350544302080 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤5115741736544501 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤39678306797647493595136 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤9700065337238496477184 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤13411541082843264319488 by norm_num)))
              have aggregated : 4881921644734054446212 * d 0 + 18826004 * d 1 + ((-130757548:ℝ)/1) * d 2 + 11349792 * d 3 + 97267541618780457102308 * d 4 + 52683300 * d 5 + 20897696 * d 6 + ((-607436:ℝ)/1) * d 7 + 6173216 * d 8 + ((-1502176:ℝ)/1) * d 9 ≤ 46190548829175646016768 := by convert combined using 1 <;> ring
              linarith only [aggregated, b0_0, b0_1, b1_2, lom2, lom5, b0_5, b0_6, b1_7, b0_8, m11]
            have tst5 : 4*d 8<3*(d 6+d 3) := by
              apply lt_of_not_ge
              intro outside
              have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
              have r1 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
              have r2cp := h.cp 3 2 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r2 : 24 * d 0 + 36 * d 1 + 36 * d 2 + 36 * d 3 + 24 * d 4 + 24 * d 5 + 24 * d 6 + 36 * d 7 + 36 * d 8 + 36 * d 9 ≤ 196 := by linarith only [r2cp]
              have r3cp := h.cp 1 1 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r3 : 4 * d 0 + 8 * d 1 + 4 * d 2 + 8 * d 3 + 8 * d 4 + 4 * d 5 + 8 * d 6 + 8 * d 7 + 16 * d 8 + 8 * d 9 ≤ 49 := by linarith only [r3cp]
              have r4cp := h.cp 2 1 3 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              have r4 : 8 * d 0 + 24 * d 1 + 24 * d 2 + 8 * d 3 + 12 * d 4 + 12 * d 5 + 4 * d 6 + 36 * d 7 + 12 * d 8 + 12 * d 9 ≤ 100 := by linarith only [r4cp]
              have r5pt0 := plane_hh b1_2 b1_8
              have r5pt1 := plane_lh b0_1 m11
              have r5pt2 := plane_lh lom2 b1_7
              have r5 : ((-1:ℝ)/2) * d 1 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r5pt0, r5pt1, r5pt2]
              have r6pt0 := plane_hh b1_2 b1_8
              have r6pt1 := plane_hl b1_1 b0_9
              have r6pt2 := plane_lh lom2 b1_7
              have r6 : 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt10, r6pt0, r6pt1, r6pt2]
              have r7pt0 := plane_hh b1_5 b1_8
              have r7pt1 := plane_lh lom5 m11
              have r7pt2 := plane_hl b1_6 lom12
              have r7 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 6 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt13, r7pt0, r7pt1, r7pt2]
              have r8 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
              have r9 : 3 * d 3 + 3 * d 6 + ((-4:ℝ)/1) * d 8 ≤ 0 := by linarith only [outside]
              have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤607934953511463808 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤135096656335881088 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤5629027347328369 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤84435410209925520 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤16887082041985112 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤270193312671761664 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤540386625343523520 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤1080773250687047040 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤146354711030537600 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤472838297175583104 by norm_num)))
              have aggregated : 24 * d 0 + ((-92:ℝ)/1) * d 1 + 36 * d 2 + 1486063219694689380 * d 3 + 120 * d 4 + 120 * d 5 + 56 * d 6 + ((-156:ℝ)/1) * d 7 + ((-444:ℝ)/1) * d 8 + ((-252:ℝ)/1) * d 9 ≤ 433435105744283956 := by convert combined using 1 <;> ring
              linarith only [aggregated, b0_0, b1_1, b0_2, lom2, lom5, b0_5, b0_6, b1_7, b1_8, m11]
            exact ⟨2, tst0,tst1,tst2,tst3,tst4,tst5⟩
        · have lom11 : ((1:ℝ)/2) ≤ d 9 := le_of_lt (lt_of_not_ge m11)
          exfalso
          have r0 : ((-1:ℝ)/1) * d 0 + 1 * d 1 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [h.tri012]
          have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
          have r2 : ((-1:ℝ)/1) * d 3 + 1 * d 4 ≤ 0 := by linarith only [hN.s14]
          have r3cp := h.cp 3 3 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          have r3 : 36 * d 0 + 24 * d 1 + 36 * d 2 + 36 * d 3 + 24 * d 4 + 36 * d 5 + 36 * d 6 + 24 * d 7 + 24 * d 8 + 36 * d 9 ≤ 196 := by linarith only [r3cp]
          have r4cp := h.cp 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          have r4 : 4 * d 0 + 4 * d 1 + 4 * d 2 + 4 * d 3 + 4 * d 4 + 4 * d 5 + 4 * d 6 + 4 * d 7 + 4 * d 8 + 4 * d 9 ≤ 25 := by linarith only [r4cp]
          have r5cp := h.cp 1819 2084 1677 2225 2196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          have r5 : 15163184 * d 0 + 12201852 * d 1 + 16189100 * d 2 + 15978096 * d 3 + 13979472 * d 4 + 18547600 * d 5 + 18305856 * d 6 + 14925300 * d 7 + 14730768 * d 8 + 19544400 * d 9 ≤ 100020001 := by linarith only [r5cp]
          have r6cp := h.cp 2218 2022 1733 2192 1835 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          have r6 : 17939184 * d 0 + 15375176 * d 1 + 19447424 * d 2 + 16280120 * d 3 + 14016504 * d 4 + 17728896 * d 5 + 14841480 * d 6 + 15194944 * d 7 + 12720220 * d 8 + 16089280 * d 9 ≤ 100000000 := by linarith only [r6cp]
          have r7pt0 := plane_hh b1_1 b1_5
          have r7pt1 := plane_hl m1 b0_7
          have r7pt2 := plane_hl b1_2 lom5
          have r7 : 1 * d 1 + ((-1:ℝ)/2) * d 2 + ((-1:ℝ)/1) * d 4 + 1 * d 5 + ((-1:ℝ)/2) * d 7 ≤ ((1:ℝ)/2) := by linarith only [h.pt1, r7pt0, r7pt1, r7pt2]
          have r8pt0 := plane_hh b1_2 b1_6
          have r8pt1 := plane_hl m1 lom11
          have r8pt2 := plane_lh lom2 b1_5
          have r8 : ((-1:ℝ)/2) * d 0 + 1 * d 2 + ((-1:ℝ)/1) * d 3 + ((-1:ℝ)/2) * d 5 + 1 * d 6 + ((-1:ℝ)/2) * d 9 ≤ ((1:ℝ)/4) := by linarith only [h.pt7, r8pt0, r8pt1, r8pt2]
          have r9pt0 := plane_hh b1_5 b1_8
          have r9pt1 := plane_hl b1_4 lom11
          have r9pt2 := plane_hl b1_6 b0_7
          have r9 : ((-1:ℝ)/2) * d 4 + 1 * d 5 + ((-1:ℝ)/1) * d 7 + 1 * d 8 + ((-1:ℝ)/1) * d 9 ≤ ((1:ℝ)/2) := by linarith only [h.pt13, r9pt0, r9pt1, r9pt2]
          have r10 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
          have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤243543333054533012029440 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤27460685264588877332480 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤117138588924890388103168 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤408197725645619593216 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤3286254968715464409088 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤10783636586188058 by norm_num))) (mul_le_mul_of_nonneg_left r6 (show (0:ℝ)≤6758768323021323 by norm_num))) (mul_le_mul_of_nonneg_left r7 (show (0:ℝ)≤16608361918354199412736 by norm_num))) (mul_le_mul_of_nonneg_left r8 (show (0:ℝ)≤193037089027424790773760 by norm_num))) (mul_le_mul_of_nonneg_left r9 (show (0:ℝ)≤250825016383706205519872 by norm_num))) (mul_le_mul_of_nonneg_left r10 (show (0:ℝ)≤43215920868281129369600 by norm_num)))
          have aggregated : ((-35814608:ℝ)/1) * d 0 + 7641776 * d 1 + 20814072 * d 2 + ((-50108472:ℝ)/1) * d 3 + 11234760 * d 4 + ((-314087136:ℝ)/1) * d 5 + 84876376 * d 6 + 81173128 * d 7 + ((-39022188:ℝ)/1) * d 8 + ((-45421984:ℝ)/1) * d 9 ≤ ((-18984858257162441105062:ℝ)/1) := by convert combined using 1 <;> ring
          linarith only [aggregated, m1, b0_1, b0_2, b1_3, lom5, b1_5, b0_6, b0_7, b1_8, b1_9]
  · have lom1 : ((1:ℝ)/2) ≤ d 0 := le_of_lt (lt_of_not_ge m1)
    exfalso
    have r0 : 1 * d 0 + ((-1:ℝ)/1) * d 4 ≤ 0 := by linarith only [hN.s01]
    have r1 : 1 * d 0 + ((-1:ℝ)/1) * d 7 ≤ 0 := by linarith only [hN.s02]
    have r2 : 1 * d 0 + ((-1:ℝ)/1) * d 9 ≤ 0 := by linarith only [hN.s03]
    have r3 : 1 * d 0 + ((-1:ℝ)/1) * d 3 ≤ 0 := by linarith only [hN.s04]
    have r4cp := h.cp 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have r4 : 4 * d 0 + 4 * d 1 + 4 * d 2 + 4 * d 3 + 4 * d 4 + 4 * d 5 + 4 * d 6 + 4 * d 7 + 4 * d 8 + 4 * d 9 ≤ 25 := by linarith only [r4cp]
    have r5 : ((-12:ℝ)/1) * d 1 + ((-12:ℝ)/1) * d 2 + ((-12:ℝ)/1) * d 5 + ((-12:ℝ)/1) * d 6 + ((-12:ℝ)/1) * d 8 ≤ ((-49:ℝ)/1) := by linarith only [target]
    have combined := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r0 (show (0:ℝ)≤81219991972280208 by norm_num)) (mul_le_mul_of_nonneg_left r1 (show (0:ℝ)≤81219991972280208 by norm_num))) (mul_le_mul_of_nonneg_left r2 (show (0:ℝ)≤81219991972280208 by norm_num))) (mul_le_mul_of_nonneg_left r3 (show (0:ℝ)≤81219991972280208 by norm_num))) (mul_le_mul_of_nonneg_left r4 (show (0:ℝ)≤20304997993070048 by norm_num))) (mul_le_mul_of_nonneg_left r5 (show (0:ℝ)≤6768332664356677 by norm_num)))
    have aggregated : 406099959861401024 * d 0 + 68 * d 1 + 68 * d 2 + ((-16:ℝ)/1) * d 3 + ((-16:ℝ)/1) * d 4 + 68 * d 5 + 68 * d 6 + ((-16:ℝ)/1) * d 7 + 68 * d 8 + ((-16:ℝ)/1) * d 9 ≤ 175976649273274027 := by convert combined using 1 <;> ring
    linarith only [aggregated, lom1, b0_1, b0_2, b1_3, b1_4, b0_5, b0_6, b1_7, b0_8, b1_9]
#print axioms finite_cover_normalized
end C5Certificate
