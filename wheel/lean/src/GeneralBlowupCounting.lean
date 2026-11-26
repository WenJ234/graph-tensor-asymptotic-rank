import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
namespace GraphTensorVerification
open scoped BigOperators

theorem sum_ordered_pairs {I : Type*} [Fintype I] [LinearOrder I]
 (d : I → I → ℝ) (diag : ∀ i,d i i=0) (symm : ∀ i j,d i j=d j i) :
 2*(∑ i, ∑ j, if i<j then d i j else 0) = ∑ i, ∑ j, d i j := by
  let f (i j:I) : ℝ := if i<j then d i j else 0
  have h (i j:I) : f i j + f j i = d i j := by
    rcases lt_trichotomy i j with hij|hij|hij
    · simp [f,hij,not_lt_of_gt hij]
    · subst j
      simp [f,diag]
    · simp [f,hij,not_lt_of_gt hij,symm j i]
  have s : (∑ i,∑ j,f j i)=(∑ i,∑ j,f i j) := Finset.sum_comm
  change 2*(∑ i,∑ j,f i j)=_
  calc
    2*(∑ i,∑ j,f i j) = (∑ i,∑ j,f i j)+(∑ i,∑ j,f j i) := by rw [s,two_mul]
    _ = ∑ i,∑ j,d i j := by
      rw [←Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _=>?_
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _=>h i j

/-- Counting each ordered pair of clones multiplies a terminal-pair distance
by the two integer clone counts. This does not assume a tensor-rank bound. -/
theorem sigma_distance_sum {J : Type} [Fintype J] (m : J → ℕ) (d : J → J → ℝ) :
 (∑ u : (Σ i, Fin (m i)), ∑ v : (Σ i, Fin (m i)), d u.1 v.1) =
 ∑ i, ∑ j, (m i:ℝ)*(m j:ℝ)*d i j := by
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _=>by ring

/-- Convert an even-clique clone distance bound to the exact integer CP test.
Here the free variables are all pairwise distances, not a pre-certified fixture. -/
theorem cp_from_even_clones {J : Type} [Fintype J] (a : J → ℕ) (d : J → J → ℝ)
 (h : (∑ u : (Σ i, Fin (2*a i)), ∑ v : (Σ i, Fin (2*a i)), d u.1 v.1)
       ≤ 2*(∑ i, (a i:ℝ))^2) :
 0 ≤ ∑ i, ∑ j, (a i:ℝ)*(1-2*d i j)*(a j:ℝ) := by
  rw [sigma_distance_sum] at h
  push_cast at h
  let sk : ℝ := ∑ i, ∑ j, (a i:ℝ)*(a j:ℝ)*d i j
  have sc : (∑ i, ∑ j, (a i:ℝ)*(a j:ℝ))=(∑ i, (a i:ℝ))^2 := by
    rw [pow_two, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _=>by rw [Finset.mul_sum]
  have hd : (∑ i, ∑ j, (2*(a i:ℝ))*(2*(a j:ℝ))*d i j)=4*sk := by
    dsimp [sk]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by ring
  rw [hd] at h
  have hcp : (∑ i, ∑ j, (a i:ℝ)*(1-2*d i j)*(a j:ℝ)) =
      (∑ i, (a i:ℝ))^2 - 2*sk := by
    rw [←sc]
    dsimp [sk]
    simp only [Finset.mul_sum, ←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by ring
  rw [hcp]
  linarith

#print axioms sum_ordered_pairs
#print axioms sigma_distance_sum
#print axioms cp_from_even_clones
end GraphTensorVerification
