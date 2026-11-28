import C5.CopoTightRows

namespace C5GeneralCycles
open scoped BigOperators

/-- The row pairing on an odd cycle accounts for every offset, including
both adjacent offsets and the diagonal. -/
theorem sum_odd_offsets (f : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range (2*(k+1)+1), f j) =
      f 0 + f 1 + f (2*(k+1)) +
        ∑ r ∈ Finset.range k, (f (2*r+2) + f (2*r+3)) := by
  have h (l : ℕ) : (∑ j ∈ Finset.range (2*l+2), f j) =
      f 0 + f 1 + ∑ r ∈ Finset.range l, (f (2*r+2) + f (2*r+3)) := by
    induction l with
    | zero => simp [Finset.sum_range_succ]
    | succ l ih =>
      rw [show 2*(l+1)+2 = (2*l+2)+1+1 by omega,
        Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]
      rw [show 2*l+2+1 = 2*l+3 by omega]
      ring
  rw [show 2*(k+1)+1 = (2*k+2)+1 by omega,Finset.sum_range_succ,h]
  rw [show 2*(k+1) = 2*k+2 by omega]
  ring

theorem pairing_row_slack (f a : ℕ → ℝ) (k : ℕ) (hf0 : f 0 = 0)
    (h : ∀ r < k, a r ≤ f (2*r+2) + f (2*r+3)) :
    f 1 + f (2*(k+1)) + (∑ r ∈ Finset.range k, a r) ≤
      ∑ j ∈ Finset.range (2*(k+1)+1), f j := by
  rw [sum_odd_offsets,hf0,zero_add]
  gcongr with r hr
  exact h r (Finset.mem_range.mp hr)

theorem pairing_row_eq_implies_tight (f a : ℕ → ℝ) (k : ℕ) (hf0 : f 0 = 0)
    (h : ∀ r < k, a r ≤ f (2*r+2) + f (2*r+3))
    (he : f 1 + f (2*(k+1)) + (∑ r ∈ Finset.range k, a r) =
      ∑ j ∈ Finset.range (2*(k+1)+1), f j) :
    ∀ r < k, a r = f (2*r+2) + f (2*r+3) := by
  have hh := he
  rw [sum_odd_offsets,hf0,zero_add] at hh
  intro r hr
  apply le_antisymm (h r hr)
  by_contra! ht
  have hs := Finset.sum_lt_sum
      (s := Finset.range k) (f := a) (g := fun r => f (2*r+2)+f (2*r+3))
      (fun r hr => h r (Finset.mem_range.mp hr))
      ⟨r,Finset.mem_range.mpr hr,ht⟩
  linarith

#print axioms sum_odd_offsets
#print axioms pairing_row_eq_implies_tight
end C5GeneralCycles

namespace C5GeneralCycles
open scoped BigOperators

/-- Aggregate the rowwise pairing estimates using the actual rotation
permutations. Equality forces both the global copositive and local triangle
budgets to be spent exactly. -/
theorem pairing_budget_tight {I : Type*} [Fintype I] (prev : I ≃ I)
    (rot : ℕ → I ≃ I) (a R : I → ℝ) (k : ℕ) (U : ℝ)
    (hrow : ∀ i, a (prev i) + a i + (∑ r ∈ Finset.range k, a (rot r i)) ≤ R i)
    (hglobal : (∑ i, R i) ≤ U) :
    ((k:ℝ)+2)*(∑ i, a i) ≤ U ∧
    (((k:ℝ)+2)*(∑ i, a i) = U →
      (∑ i, R i) = U ∧
      ∀ i, a (prev i) + a i + (∑ r ∈ Finset.range k, a (rot r i)) = R i) := by
  classical
  let b (i : I) := a (prev i) + a i + (∑ r ∈ Finset.range k, a (rot r i))
  have hb : (∑ i, b i) = ((k:ℝ)+2)*(∑ i, a i) := by
    unfold b
    simp only [Finset.sum_add_distrib, Equiv.sum_comp]
    rw [Finset.sum_comm]
    simp only [Equiv.sum_comp,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring
  have hsum : (∑ i, b i) ≤ ∑ i, R i :=
    Finset.sum_le_sum (fun i _ => hrow i)
  refine ⟨(hb ▸ hsum).trans hglobal, fun he => ?_⟩
  have hge : U ≤ ∑ i, R i := by simpa only [hb,he] using hsum
  have hR := le_antisymm hglobal hge
  refine ⟨hR, fun i => le_antisymm (hrow i) ?_⟩
  by_contra! hi
  have hlt : (∑ j, b j) < ∑ j, R j :=
    Finset.sum_lt_sum (fun j _ => hrow j) ⟨i,Finset.mem_univ i,hi⟩
  rw [hb,he,hR] at hlt
  exact (lt_irrefl U) hlt

#print axioms pairing_budget_tight
end C5GeneralCycles
