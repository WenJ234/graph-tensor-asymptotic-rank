import OddWheelSDPWitness
import Mathlib.Tactic.FieldSimp

namespace WheelVerification
open scoped BigOperators
noncomputable section

private theorem sum_toggle (k : ℕ) :
    (∑ v : ZMod (2*k+1), (if v.val%2 ≠ (v+1).val%2 then 1 else 0 : ℕ)) = 2*k := by
  calc
    _ = ∑ v : ZMod (2*k+1), (if v.val%2 ≠ rimNext' (2*k+1) v.val%2 then 1 else 0 : ℕ) := by
      simp_rw [rim_val_next]
    _ = ∑ i : Fin (2*k+1), (if i.val%2 ≠ rimNext' (2*k+1) i.val%2 then 1 else 0 : ℕ) := by
      refine Fintype.sum_equiv (ZMod.finEquiv (2*k+1)).symm.toEquiv _ _ ?_
      intro i
      rfl
    _ = crossRim (2*k+1) := Fin.sum_univ_eq_sum_range (fun i : ℕ => (if i%2 ≠ rimNext' (2*k+1) i%2 then 1 else 0 : ℕ)) (2*k+1)
    _ = 2*k := crossRim_odd k

theorem oddWheelCuts_rim_sum (k : ℕ) (h : ZMod (2*k+1)) :
    (∑ v : ZMod (2*k+1), cutDistance (oddWheelCuts k h) v (v+1)) = (2:ℝ)*k := by
  have hd (v : ZMod (2*k+1)) :
      cutDistance (oddWheelCuts k h) v (v+1) =
      if (h+v).val%2 ≠ (h+v+1).val%2 then 1 else 0 := by
    rw [add_assoc]
    have ha : (h+v).val%2 = 0 ∨ (h+v).val%2 = 1 := by omega
    have hb : (h+(v+1)).val%2 = 0 ∨ (h+(v+1)).val%2 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      norm_num [cutDistance,oddWheelCuts,ha,hb]
  simp_rw [hd]
  have he : (∑ v : ZMod (2*k+1), (if (h+v).val%2 ≠ (h+v+1).val%2 then 1 else 0 : ℝ)) =
      ∑ v : ZMod (2*k+1), (if v.val%2 ≠ (v+1).val%2 then 1 else 0 : ℝ) := by
    exact Fintype.sum_equiv (Equiv.addLeft h) _ _ (fun _ => rfl)
  rw [he]
  exact_mod_cast sum_toggle k

theorem oddWheelMetric_edge_score (k : ℕ) (hk : 1 ≤ k) :
    (∑ v : ZMod (2*k+1), oddWheelMetric k (some v) (some (v+1))) +
      (∑ v : ZMod (2*k+1), oddWheelMetric k none (some v)) =
      (5*(2*(k:ℝ)+1)+1)^2 / (16*((2*(k:ℝ)+1)+1)) := by
  unfold oddWheelMetric
  simp only [oddWheelCandidate, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [oddWheelCuts_rim_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
  push_cast
  have hp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h1 : 0 < 2*(k:ℝ)+1 := by positivity
  have h2 : 0 < (2*(k:ℝ)+1)^2-1 := by nlinarith [sq_nonneg (k:ℝ)]
  have h3 : 0 < (2*(k:ℝ)+1)+1 := by positivity
  unfold oddWheelA oddWheelS oddWheelX
  field_simp [h1.ne',h2.ne',h3.ne']
  <;> ring

#print axioms oddWheelMetric_edge_score
end
end WheelVerification
