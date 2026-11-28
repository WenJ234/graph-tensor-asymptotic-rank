import C5.OddCycleAdjacent
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic

namespace C5GeneralCycles

/-- The two tight triangles complementary in an odd cycle force every
even-step distance short of the full even step to be translation invariant. -/
theorem paired_step_translation (k : ℤ) (a : ℝ)
    (d : ℤ → ℤ → ℝ)
    (hs : ∀ i j, d i j = d j i)
    (hp : ∀ i j, d i (j+(2*k+1)) = d i j)
    (he : ∀ i r, 1 ≤ r → r < k →
        d i (i+2*r) + d (i+2*r+1) i = a) :
    ∀ i r, 1 ≤ r → r < k → d (i+1) (i+1+2*r) = d i (i+2*r) := by
  intro i r hr hk
  have h₁ := he i r hr hk
  have h₂ := he (i+2*r+1) (k-r) (by omega) (by omega)
  have h₃ : i+2*r+1+2*(k-r) = i+(2*k+1) := by omega
  have h₄ : i+(2*k+1)+1 = i+1+(2*k+1) := by omega
  rw [h₃,h₄,hp,hs (i+1+(2*k+1)) (i+2*r+1),hp] at h₂
  have h₅ : i+2*r+1 = i+1+2*r := by omega
  rw [hs (i+2*r+1) (i+1)] at h₂
  rw [h₅] at h₁ h₂
  linarith

/-- Constancy under adding one gives constancy on all integer translates. -/
theorem int_translate_constant {A : Type*} (g : ℤ → A)
    (h : ∀ i, g (i+1)=g i) :
    ∀ i, g i = g 0 := by
  intro i
  induction i using Int.induction_on with
  | zero => rfl
  | succ i ih =>
    exact (h i).trans ih
  | pred i ih =>
    have hp := h (-(i:ℤ)-1)
    have he : -(i:ℤ)-1+1 = -(i:ℤ) := by omega
    rw [he] at hp
    exact hp.symm.trans ih

/-- After translation is proved, the equality of the three distances used
to force every cycle point to be an equidistant point on a segment. -/
theorem tight_midpoint_all (d : ℤ → ℤ → ℝ)
    (h2 : ∀ i, d i (i+2) = d 0 2)
    (h4 : ∀ i, d i (i+4) = d 0 4)
    (hseg : d 0 2 + d 2 4 = d 0 4) :
    ∀ i, d (i-2) i = d i (i+2) ∧
      d (i-2) i + d i (i+2) = d (i-2) (i+2) := by
  intro i
  have h₁ := h2 (i-2)
  have h₂ := h2 i
  have h₃ := h4 (i-2)
  have h₄ := h2 2
  rw [show i-2+2=i by omega] at h₁
  rw [show i-2+4=i+2 by omega] at h₃
  have ht : d 2 4 = d 0 2 := h₄
  exact ⟨h₁.trans h₂.symm, by linarith⟩

#print axioms paired_step_translation
#print axioms int_translate_constant
#print axioms tight_midpoint_all
end C5GeneralCycles
