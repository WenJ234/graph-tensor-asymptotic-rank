import ProjectionCut
import OAI.LinearAlgebra.SpectralBooks.TriangleWidth
namespace WenJ.GraphTensor.MaxCut
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open OAI.LinearAlgebra.SpectralBooks
noncomputable section
variable {V : Type*} [Fintype V] [Nonempty V]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sites (p : V → E) : Finset E := by
  classical
  exact Finset.univ.image p

theorem site_mem (p : V → E) (v : V) : p v ∈ sites p := by
  classical
  exact Finset.mem_image_of_mem p (Finset.mem_univ v)

theorem sites_nonempty (p : V → E) : (sites p).Nonempty :=
  let ⟨v⟩ := ‹Nonempty V›
  ⟨p v, site_mem p v⟩

def placementWidth (p : V → E) : ℝ := meanWidth (sites p) (sites_nonempty p)

theorem sum_dist_le_cut_mul_width (edges : Finset (V × V))
    (p : V → E) (K : ℝ) (hcut : ∀ b : V → Bool, cutWeight edges b ≤ K) :
    ∑ e ∈ edges, dist (p e.1) (p e.2) ≤ K * placementWidth p := by
  let S := sites p
  let hS := sites_nonempty p
  let μ := stdGaussian E
  let f := support S hS
  have hproj (g : E) (v : V) : ⟪g, p v⟫ ≤ f g :=
    Finset.le_sup' (f := fun x => ⟪g, x⟫) (site_mem p v)
  have hlo (g : E) (v : V) : -f (-g) ≤ ⟪g, p v⟫ := by
    have h := neg_le_neg (hproj (-g) v)
    simpa [inner_neg_left] using h
  let v₀ : V := Classical.choice ‹Nonempty V›
  have hpt (g : E) :
      ∑ e ∈ edges, |⟪g, p e.1 - p e.2⟫| ≤ K * (f g + f (-g)) := by
    have h := proj_edge_sum_le_cut_times_range edges (fun v => ⟪g, p v⟫)
      (-f (-g)) (f g) K ((hlo g v₀).trans (hproj g v₀))
      (fun v => ⟨hlo g v,hproj g v⟩) hcut
    simpa [inner_sub_right, sub_neg_eq_add] using h
  have hif : Integrable f μ := integrable_support S hS
  have hif_neg : Integrable (fun g : E => f (-g)) μ := by
    let L : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
    have hmap := stdGaussian_map L
    have hmap' : Integrable f (Measure.map L μ) := by simpa [μ, hmap] using hif
    exact hmap'.comp_measurable (L.continuous.measurable)
  have hsym : (∫ g, f (-g) ∂μ) = ∫ g, f g ∂μ := by
    let L : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
    have hmap := stdGaussian_map L
    calc
      _ = ∫ g, f g ∂(μ.map L) :=
        (integral_map L.continuous.aemeasurable (by simpa [μ, hmap] using
          hif.aestronglyMeasurable)).symm
      _ = _ := by rw [show μ.map L = μ from hmap]
  have habs (e : V × V) : Integrable (fun g : E => |⟪g, p e.1 - p e.2⟫|) μ :=
    ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const _).abs
  have H := integral_mono (integrable_finsetSum edges (fun e _ => habs e))
    ((hif.fun_add hif_neg).const_mul K) hpt
  rw [integral_finsetSum edges (fun e _ => habs e), integral_const_mul,
    integral_add hif hif_neg, hsym] at H
  have HB := mul_le_mul_of_nonneg_left H (Real.sqrt_nonneg (2 * Real.pi))
  rw [Finset.mul_sum] at HB
  simp_rw [μ, normalized_integral_abs_inner] at HB
  rw [← Finset.mul_sum] at HB
  simp only [dist_eq_norm, placementWidth, meanWidth]
  change ∑ e ∈ edges, ‖p e.1 - p e.2‖ ≤
    K * (Real.sqrt (2 * Real.pi) * ∫ g, f g ∂μ)
  linarith only [HB]

def maxCutWeight (edges : Finset (V × V)) : ℝ := by
  classical
  exact (Finset.univ : Finset (V → Bool)).sup'
    ⟨fun _ => true, Finset.mem_univ _⟩ (cutWeight edges)

theorem cut_le_maxCutWeight (edges : Finset (V × V)) (b : V → Bool) :
    cutWeight edges b ≤ maxCutWeight edges := by
  classical
  exact Finset.le_sup' (f := cutWeight edges) (Finset.mem_univ b)

theorem cut_attains_maxCutWeight (edges : Finset (V × V)) :
    ∃ b : V → Bool, cutWeight edges b = maxCutWeight edges := by
  classical
  obtain ⟨b,_,h⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (V → Bool)))
      ⟨fun _ => true, Finset.mem_univ _⟩ (cutWeight edges)
  exact ⟨b,h.symm⟩

def twoSite (b : V → Bool) (v : V) : ℝ := if b v then 1 else 0

theorem twoSite_dist (b : V → Bool) (v w : V) :
    dist (twoSite b v) (twoSite b w) = if b v = b w then 0 else 1 := by
  unfold twoSite
  cases b v <;> cases b w <;> norm_num [Real.dist_eq]

theorem twoSite_width (b : V → Bool) (v w : V)
    (hv : b v = true) (hw : b w = false) : placementWidth (twoSite b) = 1 := by
  have hs : sites (twoSite b) = {0,1} := by
    classical
    ext x
    simp only [sites, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨u,rfl⟩
      cases b u <;> simp [twoSite, *]
    · rintro (rfl | rfl)
      · exact ⟨w,by simp [twoSite,hw]⟩
      · exact ⟨v,by simp [twoSite,hv]⟩
  classical
  have hwidth := congrArg
    (fun s : Finset ℝ => if h : s.Nonempty then meanWidth s h else 0) hs
  rw [dif_pos (sites_nonempty (twoSite b)), dif_pos (Finset.insert_nonempty _ _)] at hwidth
  calc
    placementWidth (twoSite b) = _ := hwidth
    _ = 1 := by simpa [Real.dist_eq] using (meanWidth_pair (0 : ℝ) 1)

theorem sum_dist_eq_cut_twoSite (edges : Finset (V × V)) (b : V → Bool) :
    ∑ e ∈ edges, dist (twoSite b e.1) (twoSite b e.2) = cutWeight edges b := by
  simp [cutWeight, twoSite_dist]

theorem maxCut_attained_by_two_sites [Nontrivial V] (edges : Finset (V × V)) :
    ∃ p : V → ℝ, placementWidth p = 1 ∧
      (∑ e ∈ edges, dist (p e.1) (p e.2)) = maxCutWeight edges := by
  classical
  obtain ⟨b,hb⟩ := cut_attains_maxCutWeight edges
  by_cases hSide : ∃ v w : V, b v = true ∧ b w = false
  · obtain ⟨v,w,hv,hw⟩ := hSide
    exact ⟨twoSite b,twoSite_width b v w hv hw,(sum_dist_eq_cut_twoSite edges b).trans hb⟩
  · have hzero : cutWeight edges b = 0 := by
      unfold cutWeight
      apply Finset.sum_eq_zero
      intro e he
      by_cases heq : b e.1 = b e.2
      · simp [heq]
      · exfalso
        cases h1 : b e.1 <;> cases h2 : b e.2
        · exact heq (h1.trans h2.symm)
        · exact hSide ⟨e.2,e.1,h2,h1⟩
        · exact hSide ⟨e.1,e.2,h1,h2⟩
        · exact heq (h1.trans h2.symm)
    obtain ⟨v,w,hvw⟩ := exists_pair_ne V
    let c (i : V) : Bool := decide (i = v)
    have hnonneg : 0 ≤ cutWeight edges c := by
      unfold cutWeight
      apply Finset.sum_nonneg
      intro i hi
      split <;> norm_num
    have hcut := cut_le_maxCutWeight edges c
    rw [← hb,hzero] at hcut
    exact ⟨twoSite c, twoSite_width c v w (by simp [c]) (by simp [c,Ne.symm hvw]),
      (sum_dist_eq_cut_twoSite edges c).trans ((le_antisymm hcut hnonneg).trans
        (hzero.symm.trans hb))⟩


/-- Universal upper bound for the geometric cut ratio in every Euclidean dimension. -/
theorem price_ratio_le_maxCut (edges : Finset (V × V)) (p : V → E)
    (hpos : 0 < placementWidth p) :
    (∑ e ∈ edges, dist (p e.1) (p e.2)) / placementWidth p ≤ maxCutWeight edges :=
  (div_le_iff₀ hpos).mpr (sum_dist_le_cut_mul_width edges p _
    (cut_le_maxCutWeight edges))

/-- The universal upper bound is attained already by placements on the line. -/
theorem real_line_price_ratio_isGreatest [Nontrivial V] (edges : Finset (V × V)) :
    IsGreatest {r : ℝ | ∃ p : V → ℝ, 0 < placementWidth p ∧
      r = (∑ e ∈ edges, dist (p e.1) (p e.2)) / placementWidth p}
      (maxCutWeight edges) := by
  refine ⟨?_,?_⟩
  · obtain ⟨p,hw,he⟩ := maxCut_attained_by_two_sites edges
    exact ⟨p,by rw [hw]; norm_num, by rw [hw,div_one,he]⟩
  · rintro _ ⟨p,hp,rfl⟩
    exact price_ratio_le_maxCut edges p hp

end
end WenJ.GraphTensor.MaxCut
#print axioms WenJ.GraphTensor.MaxCut.sum_dist_le_cut_mul_width
#print axioms WenJ.GraphTensor.MaxCut.maxCut_attained_by_two_sites

#print axioms WenJ.GraphTensor.MaxCut.price_ratio_le_maxCut
#print axioms WenJ.GraphTensor.MaxCut.real_line_price_ratio_isGreatest
