import C5.GlobalBound
import C5.CATPtolemy
import Mathlib.Algebra.BigOperators.Fin
namespace C5Certificate
open scoped BigOperators
set_option maxHeartbeats 0
structure MatrixMetric (D:Fin 5→Fin 5→ℝ) : Prop where
 box : ∀ i j, 0≤D i j ∧ D i j≤1
 diag : ∀ i, D i i=0
 symm : ∀ i j, D i j=D j i
 tri : ∀ i j k, D i k ≤ D i j+D j k
 pt : ∀ a b c d, D a b*D c d ≤ D a c*D b d+D a d*D b c
 cp : ∀ w:Fin 5→ℝ, (∀ i, 0≤w i) → 0≤∑ i,∑ j,w i*(1-2*D i j)*w j
def toCoordinates (D:Fin 5→Fin 5→ℝ) : Fin 10→ℝ
 | 0 => D 0 1
 | 1 => D 0 2
 | 2 => D 0 3
 | 3 => D 0 4
 | 4 => D 1 2
 | 5 => D 1 3
 | 6 => D 1 4
 | 7 => D 2 3
 | 8 => D 2 4
 | 9 => D 3 4
theorem rows_of_matrix (D:Fin 5→Fin 5→ℝ) (h:MatrixMetric D) : MetricRows (toCoordinates D) := by
  constructor
  · intro i
    fin_cases i
    · exact h.box 0 1
    · exact h.box 0 2
    · exact h.box 0 3
    · exact h.box 0 4
    · exact h.box 1 2
    · exact h.box 1 3
    · exact h.box 1 4
    · exact h.box 2 3
    · exact h.box 2 4
    · exact h.box 3 4
  · simpa only [h.symm 1 0, toCoordinates] using h.tri 1 0 2
  · simpa only [h.symm 1 0, toCoordinates] using h.tri 1 0 3
  · simpa only [h.symm 1 0, toCoordinates] using h.tri 1 0 4
  · simpa only [h.symm 2 0, toCoordinates] using h.tri 2 0 3
  · simpa only [h.symm 2 0, toCoordinates] using h.tri 2 0 4
  · simpa only [h.symm 3 0, toCoordinates] using h.tri 3 0 4
  · simpa only [toCoordinates] using h.tri 0 1 2
  · simpa only [toCoordinates] using h.tri 0 1 3
  · simpa only [toCoordinates] using h.tri 0 1 4
  · simpa only [h.symm 2 1, toCoordinates] using h.tri 2 1 3
  · simpa only [h.symm 2 1, toCoordinates] using h.tri 2 1 4
  · simpa only [h.symm 3 1, toCoordinates] using h.tri 3 1 4
  · simpa only [h.symm 2 1, toCoordinates] using h.tri 0 2 1
  · simpa only [toCoordinates] using h.tri 0 2 3
  · simpa only [toCoordinates] using h.tri 0 2 4
  · simpa only [toCoordinates] using h.tri 1 2 3
  · simpa only [toCoordinates] using h.tri 1 2 4
  · simpa only [h.symm 3 2, toCoordinates] using h.tri 3 2 4
  · simpa only [h.symm 3 1, toCoordinates] using h.tri 0 3 1
  · simpa only [h.symm 3 2, toCoordinates] using h.tri 0 3 2
  · simpa only [toCoordinates] using h.tri 0 3 4
  · simpa only [h.symm 3 2, toCoordinates] using h.tri 1 3 2
  · simpa only [toCoordinates] using h.tri 1 3 4
  · simpa only [toCoordinates] using h.tri 2 3 4
  · simpa only [h.symm 4 1, toCoordinates] using h.tri 0 4 1
  · simpa only [h.symm 4 2, toCoordinates] using h.tri 0 4 2
  · simpa only [h.symm 4 3, toCoordinates] using h.tri 0 4 3
  · simpa only [h.symm 4 2, toCoordinates] using h.tri 1 4 2
  · simpa only [h.symm 4 3, toCoordinates] using h.tri 1 4 3
  · simpa only [h.symm 4 3, toCoordinates] using h.tri 2 4 3
  · simpa only [toCoordinates] using h.pt 0 1 2 3
  · simpa only [h.symm 2 1, toCoordinates] using h.pt 0 2 1 3
  · simpa only [h.symm 3 2, h.symm 3 1, toCoordinates] using h.pt 0 3 1 2
  · simpa only [toCoordinates] using h.pt 0 1 2 4
  · simpa only [h.symm 2 1, toCoordinates] using h.pt 0 2 1 4
  · simpa only [h.symm 4 2, h.symm 4 1, toCoordinates] using h.pt 0 4 1 2
  · simpa only [toCoordinates] using h.pt 0 1 3 4
  · simpa only [h.symm 3 1, toCoordinates] using h.pt 0 3 1 4
  · simpa only [h.symm 4 3, h.symm 4 1, toCoordinates] using h.pt 0 4 1 3
  · simpa only [toCoordinates] using h.pt 0 2 3 4
  · simpa only [h.symm 3 2, toCoordinates] using h.pt 0 3 2 4
  · simpa only [h.symm 4 3, h.symm 4 2, toCoordinates] using h.pt 0 4 2 3
  · simpa only [toCoordinates] using h.pt 1 2 3 4
  · simpa only [h.symm 3 2, toCoordinates] using h.pt 1 3 2 4
  · simpa only [h.symm 4 3, h.symm 4 2, toCoordinates] using h.pt 1 4 2 3
  · intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4
    let v : Fin 5→ℝ
     | 0 => a0
     | 1 => a1
     | 2 => a2
     | 3 => a3
     | 4 => a4
    have hv : ∀ i, 0≤v i := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hp := h.cp v hv
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hp
    change 0 ≤ (((a0*(1-2*D 0 0)*a0)+((a0*(1-2*D 0 1)*a1)+((a0*(1-2*D 0 2)*a2)+((a0*(1-2*D 0 3)*a3)+(a0*(1-2*D 0 4)*a4)))))+(((a1*(1-2*D 1 0)*a0)+((a1*(1-2*D 1 1)*a1)+((a1*(1-2*D 1 2)*a2)+((a1*(1-2*D 1 3)*a3)+(a1*(1-2*D 1 4)*a4)))))+(((a2*(1-2*D 2 0)*a0)+((a2*(1-2*D 2 1)*a1)+((a2*(1-2*D 2 2)*a2)+((a2*(1-2*D 2 3)*a3)+(a2*(1-2*D 2 4)*a4)))))+(((a3*(1-2*D 3 0)*a0)+((a3*(1-2*D 3 1)*a1)+((a3*(1-2*D 3 2)*a2)+((a3*(1-2*D 3 3)*a3)+(a3*(1-2*D 3 4)*a4)))))+((a4*(1-2*D 4 0)*a0)+((a4*(1-2*D 4 1)*a1)+((a4*(1-2*D 4 2)*a2)+((a4*(1-2*D 4 3)*a3)+(a4*(1-2*D 4 4)*a4))))))))) at hp
    rw [h.diag 0, h.diag 1, h.diag 2, h.diag 3, h.diag 4, h.symm 1 0, h.symm 2 0, h.symm 3 0, h.symm 4 0, h.symm 2 1, h.symm 3 1, h.symm 4 1, h.symm 3 2, h.symm 4 2, h.symm 4 3] at hp
    change 4*a0*a1*D 0 1+4*a0*a2*D 0 2+4*a0*a3*D 0 3+4*a0*a4*D 0 4+4*a1*a2*D 1 2+4*a1*a3*D 1 3+4*a1*a4*D 1 4+4*a2*a3*D 2 3+4*a2*a4*D 2 4+4*a3*a4*D 3 4 ≤ (a0+a1+a2+a3+a4)^2
    nlinarith only [hp]
theorem matrix_objective_le (D:Fin 5→Fin 5→ℝ) (h:MatrixMetric D) :
 D 0 2+D 1 3+D 2 4+D 0 3+D 1 4 ≤ (49:ℝ)/12 := by
  exact objective_le (toCoordinates D) (rows_of_matrix D h)
#print axioms matrix_objective_le
end C5Certificate
