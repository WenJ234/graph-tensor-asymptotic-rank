import C5.CATPtolemy
import C5.OddCycleTranslate

namespace C5GeneralCycles

variable {X : Type*} [MetricSpace X]

private theorem repeated_jump (x : ℤ → X) (a b : ℤ)
    (h : ∀ i, x (i+b)=x i) (j : ℕ) :
    x (a + (j:ℤ)*b) = x a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show a + ((j+1:ℕ):ℤ)*b = (a + (j:ℤ)*b)+b by push_cast; ring, h, ih]

theorem nonzero_step_two_four (x : ℤ → X) (k : ℕ)
    (hp : ∀ i, x (i+(2*(k:ℤ)+1)) = x i)
    (ha : 0 < dist (x 0) (x 1))
    (h2 : ∀ i, dist (x i) (x (i+2)) = dist (x 0) (x 2))
    (h4 : ∀ i, dist (x i) (x (i+4)) = dist (x 0) (x 4)) :
    0 < dist (x 0) (x 2) ∧ 0 < dist (x 0) (x 4) := by
  have htwo : 0 < dist (x 0) (x 2) := by
    by_contra! hn
    have hzero := le_antisymm hn dist_nonneg
    have hz (i : ℤ) : x (i+2) = x i := (dist_eq_zero.mp ((h2 i).trans hzero)).symm
    have hy := repeated_jump x 0 2 hz (k+1)
    rw [show 0 + ((k+1:ℕ):ℤ)*2 = 1+(2*(k:ℤ)+1) by push_cast; ring, hp] at hy
    exact (dist_pos.mp ha) hy.symm
  refine ⟨htwo, ?_⟩
  by_contra! hn
  have hzero := le_antisymm hn dist_nonneg
  have hz (i : ℤ) : x (i+4) = x i := (dist_eq_zero.mp ((h4 i).trans hzero)).symm
  have hy := repeated_jump x 0 4 hz (k+1)
  rw [show 0 + ((k+1:ℕ):ℤ)*4 = (2+(2*(k:ℤ)+1))+(2*(k:ℤ)+1) by push_cast; ring,
    hp,hp] at hy
  exact (dist_pos.mp htwo) hy.symm

#print axioms nonzero_step_two_four
end C5GeneralCycles
