import OAI.Geometry.HyperbolicGroups.CATZero
import C5.MidpointCycle

namespace C5GeneralCycles
open OAI.HyperbolicObstruction
open scoped BigOperators

variable {X : Type*} [MetricSpace X]

private theorem point_on_cat_segment (hc : CATZero X) {x y p : X}
    (hxy : 0 < dist x y) (he : dist x p + dist p y = dist x y) :
    p = CATZero.segment hc x y (dist x p / dist x y) := by
  have ht : dist x p / dist x y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg dist_nonneg hxy.le, (div_le_one hxy).2 (by linarith [dist_nonneg (x:=p) (y:=y)])⟩
  apply CATZero.eq_segment_of_dist hc ht
  · field_simp
  · field_simp
    nlinarith

/-- Two distinct equal-radius steps along a common geodesic segment have
the same orientation, so their middle point is a metric midpoint. -/
theorem equally_spaced_on_segment (hc : CATZero X) (x y p q : X)
    (hxy : 0 < dist x y)
    (hp : dist x p + dist p y = dist x y)
    (hq : dist x q + dist q y = dist x y)
    (he : dist x p = dist p q) (hneq : 0 < dist x q) :
    dist x p + dist p q = dist x q := by
  have ht (z : X) (hz : dist x z + dist z y = dist x y) :
      dist x z / dist x y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg dist_nonneg hxy.le,
      (div_le_one hxy).2 (by linarith [dist_nonneg (x:=z) (y:=y)])⟩
  have hd := (CATZero.segment_spec hc x y).2.2
    (dist x p / dist x y) (ht p hp) (dist x q / dist x y) (ht q hq)
  rw [← point_on_cat_segment hc hxy hp, ← point_on_cat_segment hc hxy hq,
    ← sub_div, abs_div, abs_of_pos hxy, div_mul_cancel₀ _ (ne_of_gt hxy)] at hd
  rw [← he] at hd
  by_cases h : dist x p - dist x q ≤ 0
  · rw [abs_of_nonpos h] at hd
    linarith
  · rw [abs_of_nonneg (le_of_not_ge h)] at hd
    linarith

/-- A CAT(0) comparison choice for the purported midpoint is unnecessary:
the exact two half-lengths identify that point with the comparison segment. -/
theorem cat_midpoint_cycle_collapses (hc : CATZero X) {I : Type*} [Fintype I]
    (e : I ≃ I) (x : I → X)
    (hmid : ∀ i, dist (x (e.symm i)) (x i) = dist (x i) (x (e i)) ∧
      dist (x (e.symm i)) (x i) + dist (x i) (x (e i)) =
        dist (x (e.symm i)) (x (e i))) :
    ∀ i, x (e.symm i) = x (e i) := by
  classical
  intro i
  let f (j : I) := dist (x i) (x j)^2
  let d (j : I) := dist (x (e.symm j)) (x (e j))^2
  have h (j : I) : f j ≤ (f (e.symm j) + f (e j))/2 - d j/4 := by
    have hm := hmid j
    have hl : dist (x (e.symm j)) (x j) = (1/2 : ℝ) * dist (x (e.symm j)) (x (e j)) := by
      linarith [hm.1, hm.2]
    have hr : dist (x j) (x (e j)) = (1-(1/2 : ℝ)) * dist (x (e.symm j)) (x (e j)) := by
      linarith [hm.1, hm.2]
    have hc' := CATZero.cn_of_dist hc (x i) (by constructor <;> norm_num) hl hr
    dsimp [f,d]
    linarith
  have hz := midpoint_cycle e f d (fun _ => sq_nonneg _) h i
  have hnz : dist (x (e.symm i)) (x (e i)) = 0 := by
    dsimp [d] at hz
    nlinarith [dist_nonneg (x:=x (e.symm i)) (y:=x (e i))]
  exact dist_eq_zero.mp hnz

#print axioms equally_spaced_on_segment
#print axioms cat_midpoint_cycle_collapses
end C5GeneralCycles
