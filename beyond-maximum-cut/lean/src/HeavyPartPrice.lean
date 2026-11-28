import ZhouCopositivity

namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

variable {V K : Type} [Fintype V] [Nonempty V] [Field K]

/-- If a multipartite part has mass at least half, place half the testing
mass uniformly there and half outside it. Every edge then receives a
coefficient of at least 1/(4ab), where a and b are the two class sizes.
No estimates on the distances of nonedges are needed beyond nonnegativity. -/
theorem heavy_part_price_le (d : V → V → ℝ) (H : Finset V)
    (edge : V → V → Bool) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    [DecidableEq V] (hH : (H.card:ℝ) = b)
    (hO : ((Finset.univ \ H).card:ℝ) = a)
    (hno : ∀ i ∈ H, ∀ j ∈ H, edge i j = false)
    (hn : ∀ i j, 0 ≤ d i j)
    (hc : ∀ w : V → ℝ, (∀ i, 0 ≤ w i) →
      0 ≤ ∑ i, ∑ j, w i * (1 - 2*d i j) * w j) :
    (∑ i, ∑ j, if edge i j then d i j else 0) ≤ 2*a*b := by
  classical
  have hb := ha.trans_le hab
  let w (i : V) : ℝ := if i ∈ H then 1/(2*b) else 1/(2*a)
  have hw (i : V) : 0 ≤ w i := by unfold w; split <;> positivity
  have hsum : (∑ i, w i) = 1 := by
    rw [← Finset.sum_sdiff (Finset.subset_univ H)]
    have h₁ : ∑ i ∈ H, w i = (H.card:ℝ)*(1/(2*b)) := by
      rw [Finset.sum_congr rfl (g := fun _ => 1/(2*b))
        (fun i hi => if_pos hi)]
      simp
    have h₂ : ∑ i ∈ Finset.univ \ H, w i = ((Finset.univ \ H).card:ℝ)*(1/(2*a)) := by
      rw [Finset.sum_congr rfl (g := fun _ => 1/(2*a))
        (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2)]
      simp
    rw [h₁,h₂,hH,hO]
    field_simp
    <;> ring
  have htest := hc w hw
  have hsplit (i j : V) : w i*(1-2*d i j)*w j = w i*w j - 2*(w i*d i j*w j) := by ring
  simp_rw [hsplit,Finset.sum_sub_distrib,← Finset.mul_sum] at htest
  rw [← Finset.sum_mul, hsum] at htest
  have hbound (i j : V) :
      (if edge i j then d i j else 0) ≤ (4*a*b)*(w i*d i j*w j) := by
    cases he : edge i j
    · simpa [he] using (mul_nonneg (show 0 ≤ 4*a*b by positivity)
      (mul_nonneg (mul_nonneg (hw i) (hn i j)) (hw j)))
    · simp only [he, Bool.true_eq, if_true]
      by_cases hi : i ∈ H <;> by_cases hj : j ∈ H
      · have hh := hno i hi j hj
        simp [he] at hh
      · simp only [w,hi,hj,if_true,if_false]
        field_simp
        <;> nlinarith
      · simp only [w,hi,hj,if_true,if_false]
        field_simp
        <;> nlinarith
      · simp only [w,hi,hj,if_true,if_false]
        have h := mul_nonneg (sub_nonneg.mpr hab) (hn i j)
        field_simp
        <;> nlinarith
  have htotal := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun j _ => hbound i j))
  simp_rw [← Finset.mul_sum] at htotal
  have htest' : (∑ i, ∑ j, w i*d i j*w j) ≤ 1/2 := by linarith only [htest]
  exact htotal.trans (by
    have hh := mul_le_mul_of_nonneg_left htest' (show 0 ≤ 4*a*b by positivity)
    linarith only [hh])

/-- Apply the coefficient bound to the actual spectral point; the
copositivity input is the reusable graph-tensor lemma. -/
theorem heavy_part_wire_price_le
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V K → _ → Prop))
    (H : Finset V) (edge : V → V → Bool) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    [DecidableEq V] (hH : (H.card:ℝ) = b)
    (hO : ((Finset.univ \ H).card:ℝ) = a)
    (hno : ∀ i ∈ H, ∀ j ∈ H, edge i j = false) :
    (∑ i, ∑ j, if edge i j then rawWireDistance φ 1 i j else 0) ≤ 2*a*b := by
  exact heavy_part_price_le _ H edge a b ha hab hH hO hno
    (fun i j => by
      unfold rawWireDistance
      apply rawLogPrice_nonneg
      norm_num)
    (GraphTensorVerification.spectral_copositive φ)

#print axioms heavy_part_price_le
#print axioms heavy_part_wire_price_le
end
end WenJ.GraphTensor.MaxCut
