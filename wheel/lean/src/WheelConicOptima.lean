import WheelSDPMetricBasics
import EvenWheelSDPScore
import OddWheelSDPScore

namespace WheelVerification
open scoped BigOperators
noncomputable section

def wheelObjective (r : ℕ) [NeZero r] (d : Option (ZMod r) → Option (ZMod r) → ℝ) : ℝ :=
  (∑ v : ZMod r, d (some v) (some (v+1))) + (∑ v : ZMod r, d none (some v))

def wheelCPValues (r : ℕ) [NeZero r] : Set ℝ :=
  {x | ∃ d, WheelMetricConditions d ∧ WheelCopositive d ∧ wheelObjective r d = x}

def wheelSDPValues (r : ℕ) [NeZero r] : Set ℝ :=
  {x | ∃ d, WheelMetricConditions d ∧ WheelPSD d ∧ wheelObjective r d = x}

private theorem wheel_conic_common_of_witness (r : ℕ) [NeZero r] (u : ℝ)
    (d : Option (ZMod r) → Option (ZMod r) → ℝ)
    (hd : WheelMetricConditions d) (hp : WheelPSD d) (hu : wheelObjective r d = u)
    (hupper : ∀ a : Option (ZMod r) → Option (ZMod r) → ℝ,
      WheelMetricConditions a → WheelCopositive a → wheelObjective r a ≤ u) :
    IsGreatest (wheelCPValues r) u ∧ IsGreatest (wheelSDPValues r) u := by
  constructor
  · refine ⟨⟨d,hd,wheelPSD_imp_CP hp,hu⟩,?_⟩
    intro y hy
    obtain ⟨m,hm,hp',rfl⟩ := hy
    exact hupper m hm hp'
  · refine ⟨⟨d,hd,hp,hu⟩,?_⟩
    intro y hy
    obtain ⟨m,hm,hp',rfl⟩ := hy
    exact hupper m hm (wheelPSD_imp_CP hp')

theorem even_wheel_conic_optima (k : ℕ) [NeZero (2*k)] :
    IsGreatest (wheelCPValues (2*k)) (25*((2*k : ℕ) : ℝ)/16) ∧
    IsGreatest (wheelSDPValues (2*k)) (25*((2*k : ℕ) : ℝ)/16) := by
  let f := evenWheelCut k
  exact wheel_conic_common_of_witness _ _ (evenWheelCandidate f)
    (evenWheel_normalized f) (evenWheelCandidate_psd f) (evenWheelMetric_edge_score k)
    (fun a ha hp => wheel_cp_upper_even_or_odd _ a ha.symm ha.diagonal hp)

theorem odd_wheel_conic_optima (k : ℕ) (hk : 1 ≤ k) :
    let u := (5*((2*k+1 : ℕ) : ℝ)+1)^2 / (16*(((2*k+1 : ℕ) : ℝ)+1))
    IsGreatest (wheelCPValues (2*k+1)) u ∧ IsGreatest (wheelSDPValues (2*k+1)) u := by
  dsimp only
  have hr : (3:ℝ) ≤ 2*k+1 := by linarith [show (1:ℝ) ≤ k by exact_mod_cast hk]
  obtain ⟨hs,_,ha,ha',_⟩ := oddWheel_parameters _ hr
  refine wheel_conic_common_of_witness _ _ (oddWheelMetric k) ?_ (oddWheelMetric_psd k hk) ?_ ?_
  · exact oddWheel_normalized (oddWheelCuts k) _ _ hs ha ha'
  · simpa only [wheelObjective, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
      oddWheelMetric_edge_score k hk
  · exact fun a ha hp => wheel_cp_upper_odd k hk a ha.symm ha.diagonal ha.triangle hp

#print axioms even_wheel_conic_optima
#print axioms odd_wheel_conic_optima
end
end WheelVerification
