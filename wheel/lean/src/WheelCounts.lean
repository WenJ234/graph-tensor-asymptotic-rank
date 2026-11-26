import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Lean.Elab.Tactic.Omega

/-! Counts for canonical wheel edges indexed by their rim source. -/
namespace WheelVerification
open scoped BigOperators

def rimNext' (r i : ℕ) : ℕ := if i+1 < r then i+1 else 0

def crossRim (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, if i % 2 ≠ rimNext' r i % 2 then 1 else 0

def spokeClass (r parity : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, if i % 2 = parity then 1 else 0

theorem crossRim_even (k : ℕ) : crossRim (2*k) = 2*k := by
  unfold crossRim
  calc
    _ = ∑ _i ∈ Finset.range (2*k), (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h : i % 2 ≠ rimNext' (2*k) i % 2 := by
        unfold rimNext'
        split <;> omega
      simp [h]
    _ = _ := by simp

theorem crossRim_odd (k : ℕ) : crossRim (2*k+1) = 2*k := by
  unfold crossRim
  rw [Finset.sum_range_succ]
  have hlast : rimNext' (2*k+1) (2*k) = 0 := by simp [rimNext']
  calc
    _ = (∑ _i ∈ Finset.range (2*k), (1 : ℕ)) + 0 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have h : i % 2 ≠ rimNext' (2*k+1) i % 2 := by
          unfold rimNext'
          have ht : i+1 < 2*k+1 := by omega
          rw [if_pos ht]
          omega
        simp [h]
      · have he : (2*k)%2 = 0 := by omega
        simp [hlast, he]
    _ = _ := by simp

theorem spokeClass_even (k parity : ℕ) (hp : parity ≤ 1) :
    spokeClass (2*k) parity = k := by
  induction k with
  | zero => simp [spokeClass]
  | succ k ih =>
    have h : 2*(k+1) = (2*k+1)+1 := by omega
    rw [h]
    unfold spokeClass at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have he : (2*k)%2 = 0 := by omega
    have ho : (2*k+1)%2 = 1 := by omega
    have hp2 : parity = 0 ∨ parity = 1 := by omega
    rcases hp2 with h0 | h1
    · simp [h0, he, ho, Nat.succ_eq_add_one]
    · simp [h1, he, ho, Nat.succ_eq_add_one]

theorem spokeClass_odd_zero (k : ℕ) : spokeClass (2*k+1) 0 = k+1 := by
  have h := spokeClass_even k 0 (by omega)
  unfold spokeClass at *
  rw [Finset.sum_range_succ, h]
  have he : (2*k)%2 = 0 := by omega
  simp [he]

theorem spokeClass_odd_one (k : ℕ) : spokeClass (2*k+1) 1 = k := by
  have h := spokeClass_even k 1 (by omega)
  unfold spokeClass at *
  rw [Finset.sum_range_succ, h]
  have he : (2*k)%2 ≠ 1 := by omega
  simp [he]

#print axioms crossRim_even
#print axioms crossRim_odd
#print axioms spokeClass_even
#print axioms spokeClass_odd_zero
#print axioms spokeClass_odd_one
end WheelVerification
