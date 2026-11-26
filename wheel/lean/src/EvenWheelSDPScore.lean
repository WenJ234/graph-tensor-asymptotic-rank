import EvenWheelSDP
import WheelGroup

namespace WheelVerification
open scoped BigOperators
noncomputable section

def evenWheelCut (k : ℕ) (v : ZMod (2*k)) : Bool := decide (v.val%2 = 0)

theorem evenWheelCut_adjacent (k : ℕ) [NeZero (2*k)] (v : ZMod (2*k)) :
    cutDistance (evenWheelCut k) v (v+1) = 1 := by
  have h : v.val%2 ≠ (v+1).val%2 := by
    rw [rim_val_next]
    have hv := ZMod.val_lt v
    unfold rimNext'
    split <;> omega
  have ha : v.val%2 = 0 ∨ v.val%2 = 1 := by omega
  have hb : (v+1).val%2 = 0 ∨ (v+1).val%2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp_all [cutDistance,evenWheelCut]

theorem evenWheelMetric_edge_score (k : ℕ) [NeZero (2*k)] :
    (∑ v : ZMod (2*k), evenWheelCandidate (evenWheelCut k) (some v) (some (v+1))) +
    (∑ v : ZMod (2*k), evenWheelCandidate (evenWheelCut k) none (some v)) =
      25*((2*k : ℕ) : ℝ)/16 := by
  simp only [evenWheelCandidate,evenWheelCut_adjacent,mul_one,Finset.sum_const,
    Finset.card_univ,ZMod.card,nsmul_eq_mul]
  ring

#print axioms evenWheelMetric_edge_score
end
end WheelVerification
