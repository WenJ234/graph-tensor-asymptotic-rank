import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Abel

namespace C5GeneralCycles
open scoped BigOperators

/-- The constant-pairing-sum step of strictness uses only a one-step
telescoping identity, without Fourier analysis. -/
theorem pairing_constant_adjacent {A : Type*} [AddCommGroup A]
    (a : ℤ → A) (k : ℕ)
    (hp : ∀ i : ℤ, a (i + (2 * (k : ℤ) + 1)) = a i)
    (hc : ∀ i : ℤ,
      a (i + 2 - 1) + (∑ r ∈ Finset.range k, a (i + 2 + 2*(r : ℤ))) =
      a (i - 1) + (∑ r ∈ Finset.range k, a (i + 2*(r : ℤ)))) :
    ∀ i : ℤ, a (i + 1) = a i := by
  intro i
  have h := hc i
  have htel :
      (∑ r ∈ Finset.range k, a (i + 2 + 2*(r : ℤ))) + a i =
      (∑ r ∈ Finset.range k, a (i + 2*(r : ℤ))) + a (i + 2*(k : ℤ)) := by
    have h' := Finset.sum_range_succ' (fun r : ℕ => a (i + 2*(r : ℤ))) k
    rw [Finset.sum_range_succ] at h'
    rw [h']
    simp only [Nat.cast_succ, Nat.cast_zero, mul_zero, add_zero]
    apply congrArg (fun z => z + a i)
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    omega
  have hwrap : a (i + 2*(k : ℤ)) = a (i - 1) := by
    convert hp (i - 1) using 2 <;> omega
  rw [hwrap] at htel
  have hi : i + 2 - 1 = i + 1 := by omega
  rw [hi] at h
  calc
    a (i + 1) = (a (i + 1) + (∑ r ∈ Finset.range k, a (i + 2 + 2*(r : ℤ)))) -
           (∑ r ∈ Finset.range k, a (i + 2 + 2*(r : ℤ))) := by abel
    _ = (a (i - 1) + (∑ r ∈ Finset.range k, a (i + 2*(r : ℤ)))) -
           (∑ r ∈ Finset.range k, a (i + 2 + 2*(r : ℤ))) := by rw [h]
    _ = a i := by
      rw [add_comm (a (i-1)), ← htel]
      abel

#print axioms pairing_constant_adjacent
end C5GeneralCycles
