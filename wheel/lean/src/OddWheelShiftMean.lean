import OddWheelCovariance
import WheelGroupedCounts
import Mathlib.Tactic.FieldSimp

namespace WheelVerification
open scoped BigOperators
noncomputable section

def alternatingSign {r : ℕ} (v : ZMod r) : ℝ := if v.val%2 = 0 then 1 else -1

def alternatingShift {r : ℕ} (h v : ZMod r) : ℝ := alternatingSign (h+v)

private theorem sum_parity_zero (k : ℕ) :
    (∑ v : ZMod (2*k+1), (if v.val%2 = 0 then 1 else 0 : ℕ)) = k+1 := by
  calc
    _ = ∑ i : Fin (2*k+1), (if i.val%2 = 0 then 1 else 0 : ℕ) := by
      refine Fintype.sum_equiv (ZMod.finEquiv (2*k+1)).symm.toEquiv _ _ ?_
      intro i
      rfl
    _ = spokeClass (2*k+1) 0 := Fin.sum_univ_eq_sum_range (fun i : ℕ => (if i%2 = 0 then 1 else 0 : ℕ)) (2*k+1)
    _ = k+1 := spokeClass_odd_zero k

theorem alternatingShift_is_sign {r : ℕ} (h v : ZMod r) :
    alternatingShift h v = 1 ∨ alternatingShift h v = -1 := by
  unfold alternatingShift alternatingSign
  split <;> simp

theorem alternatingShift_sum (k : ℕ) (v : ZMod (2*k+1)) :
    (∑ h : ZMod (2*k+1), alternatingShift h v) = 1 := by
  have reindex : (∑ h : ZMod (2*k+1), alternatingShift h v) =
      ∑ h : ZMod (2*k+1), alternatingSign h := by
    exact Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)
  rw [reindex]
  have hc : (∑ h : ZMod (2*k+1), (if h.val%2 = 0 then 1 else 0 : ℝ)) =
      (k : ℝ)+1 := by exact_mod_cast sum_parity_zero k
  have he (h : ZMod (2*k+1)) : alternatingSign h =
      2*(if h.val%2 = 0 then 1 else 0)-1 := by
    unfold alternatingSign
    split <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hc]
  simp [ZMod.card]
  ring

theorem alternatingShift_mean (k : ℕ) (v : ZMod (2*k+1)) :
    (∑ h : ZMod (2*k+1), alternatingShift h v) =
      (Fintype.card (ZMod (2*k+1)) : ℝ) * (1/((2:ℝ)*k+1)) := by
  rw [alternatingShift_sum,ZMod.card]
  push_cast
  field_simp
  <;> positivity

#print axioms alternatingShift_mean
end
end WheelVerification
