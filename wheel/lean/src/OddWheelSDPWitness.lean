import OddWheelCandidateTriangle
import OddWheelShiftMean
import OddWheelNormalization

namespace WheelVerification
open scoped BigOperators
noncomputable section

def oddWheelCuts (k : ℕ) (h v : ZMod (2*k+1)) : Bool :=
  decide ((h+v).val%2 = 0)

theorem oddWheelCuts_cutSign (k : ℕ) (h v : ZMod (2*k+1)) :
    cutSign (oddWheelCuts k) h v = alternatingShift h v := by
  simp [cutSign,oddWheelCuts,alternatingShift,alternatingSign]

def oddWheelMetric (k : ℕ) : Option (ZMod (2*k+1)) → Option (ZMod (2*k+1)) → ℝ :=
  oddWheelCandidate (oddWheelCuts k) (oddWheelS ((2:ℝ)*k+1)) (oddWheelA ((2:ℝ)*k+1))

theorem oddWheelMetric_psd (k : ℕ) (hk : 1 ≤ k) (u : Option (ZMod (2*k+1)) → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * (1-2*oddWheelMetric k i j) * u j := by
  have h : (3:ℝ) ≤ 2*k+1 := by linarith [show (1:ℝ) ≤ k by exact_mod_cast hk]
  obtain ⟨_,_,ha,_,hs⟩ := oddWheel_parameters _ h
  apply oddWheelCandidate_psd (oddWheelCuts k) (1/(2*(k:ℝ)+1)) _ _ ha _ hs
  intro i
  simp_rw [oddWheelCuts_cutSign]
  exact alternatingShift_mean k i

theorem oddWheelMetric_triangle (k : ℕ) (hk : 1 ≤ k) (x y z : Option (ZMod (2*k+1))) :
    oddWheelMetric k x z ≤ oddWheelMetric k x y + oddWheelMetric k y z := by
  have h : (3:ℝ) ≤ 2*k+1 := by linarith [show (1:ℝ) ≤ k by exact_mod_cast hk]
  obtain ⟨hs,_,ha,ha',_⟩ := oddWheel_parameters _ h
  exact oddWheelCandidate_triangle (oddWheelCuts k) _ _ hs ha ha' x y z

#print axioms oddWheelMetric_psd
#print axioms oddWheelMetric_triangle
end
end WheelVerification
