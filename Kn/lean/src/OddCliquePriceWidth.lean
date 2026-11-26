import OddCliquePriceProjection
import PriceGaussianWidth
import Mathlib.Tactic.Linarith

/-! Lift the clamped pointwise bound to Gaussian mean width. -/
namespace OddCliquePaper
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev K5Terminal := { x : Fin 5 × Fin 5 // x.1 ≠ x.2 }
private instance : Nonempty K5Terminal := ⟨⟨(0,1),by decide⟩⟩

def terminal (p : Fin 5 → Fin 5 → E) (i : K5Terminal) : E := p i.val.1 i.val.2

def lower (p : Fin 5 → Fin 5 → E) (g : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : K5Terminal => innerSL ℝ (terminal p i) g)
def upper (p : Fin 5 → Fin 5 → E) (g : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : K5Terminal => innerSL ℝ (terminal p i) g)

def terminalMeanWidth (p : Fin 5 → Fin 5 → E) : ℝ :=
  (∫ g, (upper p g - lower p g) ∂(stdGaussian E)) / gaussianAbsMean

def directedLength (p : Fin 5 → Fin 5 → E) : ℝ :=
  ∑ i, ∑ j, ‖p i j - p j i‖
def localTransport (p : Fin 5 → Fin 5 → E) (z : Fin 5 → E) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else ‖p i j - z i‖

private theorem integrable_inner (v : E) :
    Integrable (fun g => innerSL ℝ v g) (stdGaussian E) :=
  IsGaussian.integrable_dual _ (innerSL ℝ v)

private theorem integrable_sup'_real {A : Type*} (s : Finset A) (hs : s.Nonempty) (f : A → E → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (stdGaussian E)) :
    Integrable (fun g => s.sup' hs (fun i => f i g)) (stdGaussian E) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i (Finset.mem_singleton.mpr rfl)
  | cons i s hi hs ih =>
    rw [show (fun g => (s.cons i hi).sup' _ (fun j => f j g)) =
      f i ⊔ (fun g => s.sup' hs (fun j => f j g)) from by
        funext g
        exact Finset.sup'_cons _ _]
    exact (hf i (Finset.mem_cons_self _ _)).sup (ih (fun j hj => hf j (Finset.mem_cons_of_mem hj)))

private theorem integrable_inf'_real {A : Type*} (s : Finset A) (hs : s.Nonempty) (f : A → E → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (stdGaussian E)) :
    Integrable (fun g => s.inf' hs (fun i => f i g)) (stdGaussian E) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i (Finset.mem_singleton.mpr rfl)
  | cons i s hi hs ih =>
    rw [show (fun g => (s.cons i hi).inf' _ (fun j => f j g)) =
      f i ⊓ (fun g => s.inf' hs (fun j => f j g)) from by
        funext g
        exact Finset.inf'_cons _ _]
    exact (hf i (Finset.mem_cons_self _ _)).inf (ih (fun j hj => hf j (Finset.mem_cons_of_mem hj)))

private theorem projection_gap_mean (v w : E) :
    (∫ g, |innerSL ℝ v g - innerSL ℝ w g| ∂(stdGaussian E)) =
      ‖v-w‖ * gaussianAbsMean := by
  have h : ∀ g, innerSL ℝ v g - innerSL ℝ w g = innerSL ℝ (v-w) g := by
    intro g
    simp
  simp only [h, gaussian_inner_abs_mean]

theorem k5_directed_pricing_upper (p : Fin 5 → Fin 5 → E) (z : Fin 5 → E) :
    directedLength p - 2 * localTransport p z ≤ 12 * terminalMeanWidth p := by
  let l (i j : Fin 5) (g : E) := |innerSL ℝ (p i j) g - innerSL ℝ (p j i) g|
  let c (i j : Fin 5) (g : E) := if i = j then (0 : ℝ) else |innerSL ℝ (p i j) g - innerSL ℝ (z i) g|
  have hl (i j : Fin 5) : Integrable (l i j) (stdGaussian E) :=
    ((integrable_inner _).sub (integrable_inner _)).abs
  have hc (i j : Fin 5) : Integrable (c i j) (stdGaussian E) := by
    by_cases h : i = j
    · simpa [c,h] using (integrable_zero : Integrable (0 : E → ℝ) (stdGaussian E))
    · simpa [c,h] using ((integrable_inner (p i j)).sub (integrable_inner (z i))).abs
  have hs : Integrable (fun g => upper p g - lower p g) (stdGaussian E) :=
    (integrable_sup'_real _ _ _ (fun i _ => integrable_inner (terminal p i))).sub
      (integrable_inf'_real _ _ _ (fun i _ => integrable_inner (terminal p i)))
  have hpoint (g : E) : (∑ i, ∑ j, l i j g) ≤
      12*(upper p g-lower p g) + 2*(∑ i, ∑ j, c i j g) := by
    have ha i j (h : i ≠ j) : lower p g ≤ innerSL ℝ (p i j) g :=
      Finset.inf'_le (fun k : K5Terminal => innerSL ℝ (terminal p k) g) (Finset.mem_univ (⟨(i,j),h⟩ : K5Terminal))
    have hb i j (h : i ≠ j) : innerSL ℝ (p i j) g ≤ upper p g :=
      Finset.le_sup' (fun k : K5Terminal => innerSL ℝ (terminal p k) g) (Finset.mem_univ (⟨(i,j),h⟩ : K5Terminal))
    exact k5_projected_transport_bound (fun i j => innerSL ℝ (p i j) g)
      (fun i => innerSL ℝ (z i) g) _ _
      ((ha 0 1 (by decide)).trans (hb 0 1 (by decide))) ha hb
  have hLi : Integrable (fun g => ∑ i, ∑ j, l i j g) (stdGaussian E) := by
    apply integrable_finsetSum; intro i hi
    exact integrable_finsetSum _ (fun j _ => hl i j)
  have hCi : Integrable (fun g => ∑ i, ∑ j, c i j g) (stdGaussian E) := by
    apply integrable_finsetSum; intro i hi
    exact integrable_finsetSum _ (fun j _ => hc i j)
  have hineq := integral_mono hLi ((hs.const_mul 12).add (hCi.const_mul 2)) hpoint
  rw [integral_add' (hs.const_mul 12) (hCi.const_mul 2), integral_const_mul, integral_const_mul] at hineq
  have hL : (∫ g, (∑ i, ∑ j, l i j g) ∂(stdGaussian E)) =
      directedLength p * gaussianAbsMean := by
    unfold directedLength
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hl i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hl _ j), l, projection_gap_mean, Finset.sum_mul]
  have hC : (∫ g, (∑ i, ∑ j, c i j g) ∂(stdGaussian E)) =
      localTransport p z * gaussianAbsMean := by
    unfold localTransport
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hc i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hc _ j), Finset.sum_mul]
    congr 1 with i
    congr 1 with j
    by_cases h : i = j
    · simp [c,h]
    · simpa [c,h] using projection_gap_mean (p i j) (z i)
  rw [hL,hC] at hineq
  unfold terminalMeanWidth
  rw [← mul_div_assoc]
  apply (le_div_iff₀ gaussianAbsMean_pos).mpr
  nlinarith

#print axioms k5_directed_pricing_upper
end
end OddCliquePaper
