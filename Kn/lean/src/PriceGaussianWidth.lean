import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Normalization of projected lengths for the Gaussian definition of mean width. -/
namespace OddCliquePaper
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
noncomputable section

def gaussianAbsMean : ℝ := ∫ s : ℝ, |s| ∂(gaussianReal 0 1)

theorem gaussianAbsMean_pos : 0 < gaussianAbsMean := by
  unfold gaussianAbsMean
  have hI : Integrable (fun s : ℝ => |s|) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs, id_eq] using (IsGaussian.integrable_id (μ := gaussianReal 0 1)).norm
  rw [integral_pos_iff_support_of_nonneg (fun s => abs_nonneg s) hI]
  have he : Function.support (fun s : ℝ => |s|) = ({0} : Set ℝ)ᶜ := by
    ext s
    simp
  have hz : gaussianReal 0 1 ({0} : Set ℝ) = 0 :=
    gaussianReal_absolutelyContinuous _ (by norm_num : (1 : ℝ≥0) ≠ 0) (by simp)
  rw [he, measure_of_measure_compl_eq_zero (by simpa using hz), measure_univ]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_inner_abs_mean (v : E) :
    (∫ g, |(innerSL ℝ v) g| ∂(stdGaussian E)) = ‖v‖ * gaussianAbsMean := by
  let L := innerSL ℝ v
  have h_map : (stdGaussian E).map L = gaussianReal 0 ((‖v‖ ^ 2).toNNReal) := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    dsimp [L]
    rw [innerSL_apply_norm]
  have h_scale : (gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) =
      gaussianReal 0 ((‖v‖ ^ 2).toNNReal) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply NNReal.eq
    simp [Real.coe_toNNReal', sq_nonneg]
  calc
    (∫ g, |(innerSL ℝ v) g| ∂(stdGaussian E)) = ∫ s : ℝ, |s| ∂((stdGaussian E).map L) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ s : ℝ, |s| ∂((gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x)) := by
      rw [h_map, h_scale]
    _ = ‖v‖ * gaussianAbsMean := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [abs_mul, abs_of_nonneg (norm_nonneg v), integral_const_mul, gaussianAbsMean]

#print axioms gaussianAbsMean_pos
#print axioms gaussian_inner_abs_mean
end
end OddCliquePaper
