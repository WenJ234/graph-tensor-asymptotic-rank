import C5.OddCyclePeriod
import C5.CATStrictness

namespace C5GeneralCycles
open OAI.HyperbolicObstruction

/-- A periodic chain of equally spaced midpoints cannot keep positive
step-four separation in a CAT(0) space. Use a maximal radius in one period. -/
theorem periodic_cat_contradiction {X : Type*} [MetricSpace X] (hc : CATZero X)
    (x : ℤ → X) (n : ℤ) (hn : 0 < n)
    (hp : ∀ i, x (i+n) = x i)
    (h₂ : ∀ i, dist (x i) (x (i+2)) = dist (x 0) (x 2))
    (h₄ : ∀ i, dist (x i) (x (i+4)) = dist (x 0) (x 4))
    (hseg : dist (x 0) (x 2) + dist (x 2) (x 4) = dist (x 0) (x 4))
    (hpos : 0 < dist (x 0) (x 4)) : False := by
  classical
  let d (i j : ℤ) := dist (x i) (x j)
  let f (i : ℤ) := dist (x 0) (x i)^2
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.Ico (0:ℤ) n) f
    ⟨0, by simpa using hn⟩
  have hmax (i : ℤ) : f i ≤ f j := by
    have hper (z : ℤ) : x (i%n + (z+1)*n) = x (i%n + z*n) := by
      rw [show i%n+(z+1)*n = (i%n+z*n)+n by ring, hp]
    have hr := int_translate_constant (fun z : ℤ => x (i%n + z*n)) hper (i/n)
    rw [show i % n + i/n*n = i by simpa [mul_comm] using Int.emod_add_mul_ediv i n,
      zero_mul,add_zero] at hr
    have hi := hj (i%n) (Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hn),Int.emod_lt_of_pos _ hn⟩)
    change dist (x 0) (x i)^2 ≤ f j
    rw [hr]
    exact hi
  have hmid := tight_midpoint_all d h₂ h₄ hseg j
  have hl : dist (x (j-2)) (x j) = (1/2 : ℝ) * dist (x (j-2)) (x (j+2)) := by
    dsimp [d] at hmid
    linarith [hmid.1,hmid.2]
  have hr : dist (x j) (x (j+2)) = (1-(1/2 : ℝ)) * dist (x (j-2)) (x (j+2)) := by
    dsimp [d] at hmid
    linarith [hmid.1,hmid.2]
  have hcn := CATZero.cn_of_dist hc (x 0) (by constructor <;> norm_num) hl hr
  have hd := h₄ (j-2)
  rw [show j-2+4=j+2 by omega] at hd
  rw [hd] at hcn
  have hneg := sq_pos_of_pos hpos
  have hL := hmax (j-2)
  have hR := hmax (j+2)
  dsimp [f] at hL hR
  linarith

/-- The CAT(0) geometric contradiction of Theorem 5.2, once the finite
copositive equality analysis has supplied the uniform adjacent length and
tight paired triangles. -/
theorem no_paired_odd_cat_cycle {X : Type*} [MetricSpace X] (hc : CATZero X)
    (x : ℤ → X) (k : ℕ) (hk : 2 ≤ k) (a : ℝ) (ha : 0 < a)
    (hp : ∀ i, x (i+(2*(k:ℤ)+1)) = x i)
    (hadj : ∀ i, dist (x i) (x (i+1)) = a)
    (he : ∀ i r : ℤ, 1 ≤ r → r < (k:ℤ) →
      dist (x i) (x (i+2*r)) + dist (x (i+2*r+1)) (x i) = a) : False := by
  let d (i j : ℤ) := dist (x i) (x j)
  have hn (i : ℤ) : d i (i+2*(k:ℤ)) = a := by
    change dist (x i) (x (i+2*(k:ℤ))) = a
    rw [show i+2*(k:ℤ) = i-1+(2*(k:ℤ)+1) by omega, hp, dist_comm]
    simpa only [show i-1+1=i by omega] using hadj (i-1)
  have htr := paired_step_translation (k:ℤ) a d
    (fun _ _ => dist_comm _ _) (fun i j => by simp [d,hp]) he
  have hC (r : ℤ) (hr : 1 ≤ r) (hrk : r ≤ (k:ℤ)) :
      ∀ i : ℤ, d i (i+2*r) = d 0 (0+2*r) := by
    rcases lt_or_eq_of_le hrk with hlt | heq
    · exact int_translate_constant (fun i => d i (i+2*r))
        (fun i => htr i r hr hlt)
    · rw [heq]
      intro i
      rw [hn,hn]
  have h2 : ∀ i, d i (i+2) = d 0 2 := hC 1 (by decide) (by omega)
  have h4 : ∀ i, d i (i+4) = d 0 4 := hC 2 (by decide) (by omega)
  have h01 : 0 < d 0 1 := by
    have h : d 0 1 = a := hadj 0
    rwa [h]
  obtain ⟨_, h04⟩ := nonzero_step_two_four x k hp h01 h2 h4
  have hb (s : ℤ) (hs : 1 ≤ s) (hsk : s ≤ (k:ℤ)) :
      d 0 (2*s) + d (2*s) (2*(k:ℤ)) = d 0 (2*(k:ℤ)) := by
    rcases lt_or_eq_of_le hsk with ht | ht
    · have h := he (2*s) ((k:ℤ)-s) (by omega) (by omega)
      rw [show 2*s+2*((k:ℤ)-s) = 2*(k:ℤ) by omega,
        show 2*(k:ℤ)+1 = 0+(2*(k:ℤ)+1) by omega, hp, add_comm] at h
      have hn0 : d 0 (2*(k:ℤ)) = a := by simpa only [zero_add] using hn 0
      rw [hn0]
      exact h
    · rw [ht]
      simp [d]
  have h02 := hb 1 (by decide) (by omega)
  have h04' := hb 2 (by decide) (by omega)
  have hdist : 0 < d 0 (2*(k:ℤ)) := by
    have hh := hn 0
    simp only [zero_add] at hh
    rwa [hh]
  have hh : d 0 2 = d 2 4 := (h2 2).symm
  have hs := equally_spaced_on_segment hc (x 0) (x (2*(k:ℤ))) (x 2) (x 4)
    hdist h02 h04' hh h04
  exact periodic_cat_contradiction hc x (2*(k:ℤ)+1) (by omega) hp h2 h4 hs h04

#print axioms periodic_cat_contradiction
#print axioms no_paired_odd_cat_cycle
end C5GeneralCycles
