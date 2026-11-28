import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace C5GeneralCycles
open scoped BigOperators

/-- At a zero of a copositive quadratic form at the all-ones vector, every
row sum vanishes when the diagonal is one. This uses one-variable variation,
not differentiability. -/
theorem copo_rows_at_ones {I : Type*} [Fintype I]
    (Q : I → I → ℝ)
    (hs : ∀ i j, Q i j = Q j i)
    (hd : ∀ i, Q i i = 1)
    (h0 : (∑ i, ∑ j, Q i j) = 0)
    (hcp : ∀ x : I → ℝ, (∀ i, 0 ≤ x i) → 0 ≤ ∑ i, ∑ j, Q i j * x i * x j) :
    ∀ i, (∑ j, Q i j) = 0 := by
  classical
  intro i
  let r := ∑ j, Q i j
  have hexpand (t : ℝ) (ht : -1 ≤ t) : 0 ≤ 2*t*r+t^2 := by
    let e (j : I) : ℝ := if j=i then 1 else 0
    let x (j : I) : ℝ := 1+t*e j
    have hx (j) : 0 ≤ x j := by
      by_cases h : j = i <;> simp [x,e,h] <;> linarith
    have h := hcp x hx
    have hp (j k : I) : Q j k * x j * x k =
        Q j k + t*(Q j k*e j) + t*(Q j k*e k) + t^2*(Q j k*e j*e k) := by
      simp only [x]
      ring
    simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    have hleft : (∑ j, ∑ k, Q j k * e j) = r := by
      rw [Finset.sum_comm]
      simp [e,r,mul_ite]
    have hright : (∑ j, ∑ k, Q j k * e k) = r := by
      simp only [e,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      exact Finset.sum_congr rfl (fun j _ => hs j i)
    have hdiag : (∑ j, ∑ k, Q j k * e j * e k) = 1 := by
      simp [e,mul_ite,hd]
    rw [h0,hleft,hright,hdiag] at h
    nlinarith only [h]
  by_contra hr
  let t : ℝ := -r/(|r|+1)
  have hp : 0 < |r|+1 := by linarith [abs_nonneg r]
  have ht : -1 ≤ t := (le_div_iff₀ hp).2 (by nlinarith [le_abs_self r])
  have ha := hexpand t ht
  have hneg : 2*t*r+t^2 < 0 := by
    have he : 2*t*r+t^2 = -(r^2)*(2*|r|+1)/(|r|+1)^2 := by
      dsimp [t]
      field_simp [hp.ne']
      <;> ring
    rw [he]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (neg_lt_zero.mpr (sq_pos_of_ne_zero hr)) (by linarith [abs_nonneg r])) (sq_pos_of_pos hp)
  exact (not_lt_of_ge ha) hneg

#print axioms copo_rows_at_ones
end C5GeneralCycles
