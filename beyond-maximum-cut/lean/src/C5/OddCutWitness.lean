import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace C5Placement
open scoped BigOperators

private def cutSign : Bool → ℤ
  | false => 1
  | true => -1

private theorem cutSign_sq (b : Bool) : cutSign b * cutSign b = 1 := by
  cases b <;> decide

/-- Every two-coloring leaves an uncut edge for an odd number of sites
with a cyclic successor. In fact bijectivity of successor suffices. -/
theorem odd_permutation_has_uncut_edge {I : Type} [Fintype I] (hI : Odd (Fintype.card I))
    (σ : Equiv.Perm I) (b : I → Bool) : ∃ i, b i = b (σ i) := by
  by_contra! h
  have hp : (∏ i, cutSign (b i) * cutSign (b (σ i))) = 1 := by
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => cutSign (b i))]
    rw [← Finset.prod_mul_distrib]
    simp only [cutSign_sq,Finset.prod_const_one]
  have hn (i : I) : cutSign (b i) * cutSign (b (σ i)) = -1 := by
    have hi := h i
    cases h₁ : b i <;> cases h₂ : b (σ i) <;> simp [h₁,h₂,cutSign] at hi ⊢
  simp only [hn,Finset.prod_const,Finset.card_univ] at hp
  rcases hI with ⟨k,hk⟩
  rw [hk, pow_add,pow_mul] at hp
  norm_num at hp

#print axioms odd_permutation_has_uncut_edge
end C5Placement
