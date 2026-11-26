import OddWheelCandidateTriangle
import WheelCPUpper

namespace WheelVerification
open scoped BigOperators
noncomputable section

structure WheelMetricConditions {I : Type} (d : I → I → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ d i j
  symm : ∀ i j, d i j = d j i
  diagonal : ∀ i, d i i = 0
  triangle : ∀ i j k, d i k ≤ d i j + d j k

def WheelPSD {I : Type} [Fintype I] (d : I → I → ℝ) : Prop :=
  ∀ u : I → ℝ, 0 ≤ ∑ i, ∑ j, u i*(1-2*d i j)*u j

theorem wheelPSD_imp_CP {I : Type} [Fintype I] {d : I → I → ℝ}
    (h : WheelPSD d) : WheelCopositive d := fun u _ => h u

private theorem cutDistance_symm {I : Type} (f : I → Bool) (i j : I) :
    cutDistance f i j = cutDistance f j i := by
  unfold cutDistance
  simp only [eq_comm]

private theorem cutDistance_nonneg {I : Type} (f : I → Bool) (i j : I) :
    0 ≤ cutDistance f i j := by
  unfold cutDistance
  split <;> norm_num

theorem evenWheel_normalized {I : Type} (f : I → Bool) :
    WheelMetricConditions (evenWheelCandidate f) := by
  refine ⟨?_, ?_, ?_, evenWheelCandidate_triangle f⟩
  · intro i j
    cases i <;> cases j <;> simp only [evenWheelCandidate] <;> try norm_num
    exact cutDistance_nonneg f _ _
  · intro i j
    cases i <;> cases j <;> simp only [evenWheelCandidate,cutDistance_symm]
  · intro i
    cases i <;> simp [evenWheelCandidate,cutDistance]

theorem oddWheel_normalized {I J : Type} [Fintype J] [Nonempty J]
    (f : J → I → Bool) (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    WheelMetricConditions (oddWheelCandidate f s a) := by
  refine ⟨?_, ?_, ?_, oddWheelCandidate_triangle f s a hs ha ha'⟩
  · intro i j
    cases i <;> cases j <;> simp only [oddWheelCandidate] <;> try positivity
    exact mul_nonneg (div_nonneg ha (by positivity)) (Finset.sum_nonneg fun h _ => cutDistance_nonneg (f h) _ _)
  · intro i j
    cases i <;> cases j <;> simp only [oddWheelCandidate,cutDistance_symm]
  · intro i
    cases i <;> simp [oddWheelCandidate,cutDistance]

#print axioms evenWheel_normalized
#print axioms oddWheel_normalized
end
end WheelVerification
