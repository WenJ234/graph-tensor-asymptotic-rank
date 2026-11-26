import CliqueCoordinates
import GeneralBlowupCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

namespace GraphTensorVerification
open scoped BigOperators

theorem clique_sum_expand {n : ℕ} (d : Fin n → Fin n → ℝ) :
    (∑ e : SortedEdge n, d e.val.1 e.val.2) =
    ∑ i, ∑ j, if i<j then d i j else 0 := by
  classical
  let p : Fin n × Fin n → Prop := fun x => x.1 < x.2
  let f : Fin n × Fin n → ℝ := fun x => d x.1 x.2
  calc
    _ = ∑ x ∈ Finset.univ.filter p, f x := by
      symm
      exact Finset.sum_subtype _ (by simp [p]) f
    _ = ∑ x : Fin n × Fin n, if p x then f x else 0 := Finset.sum_filter _ _
    _ = _ := Fintype.sum_prod_type _

theorem ordered_clique_sum {n : ℕ} (d : Fin n → Fin n → ℝ)
    (diag : ∀ i, d i i = 0) (symm : ∀ i j, d i j = d j i) :
    2*(∑ e : SortedEdge n, d e.val.1 e.val.2) = ∑ i, ∑ j, d i j := by
  rw [clique_sum_expand]
  exact sum_ordered_pairs d diag symm

#print axioms ordered_clique_sum
end GraphTensorVerification
