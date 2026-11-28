import C5.OddZModStrict
import C5.UnconditionalSpectralUpper

namespace C5GeneralCycles
open OAI OAI.HyperbolicObstruction
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators NNReal
noncomputable section

variable {I K : Type} [Fintype I] [Nonempty I] [Field K]

def cyclicWire (u v : I) : TensorClass.{0} I K :=
  ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![u,v])

private theorem cyclicWire_nonzero (u v : I) :
    cyclicWire (K:=K) u v ≠ 0 := by
  intro hz
  have hg := (ofRaw_eq_zero_iff _).mp hz
  have he : (Raw.diagonal (Fin 2) K (Fin 2)).coeff = 0 := by
    by_contra hn
    exact (((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff ![u,v]).mpr hn) hg
  have hx := congrFun he (fun _=>(0:Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _=>(0:Fin 2))=0 at hx
  simp [Raw.diagonal,funext_iff] at hx

def cycleProduct (k : ℕ) : TensorClass.{0} (ZMod (2*(k+1)+1)) K :=
  ∏ i : ZMod (2*(k+1)+1), cyclicWire i (i+1)

private theorem cyclic_log_sum (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (s : Finset I) (next : I → I) :
    Real.logb 2 (φ.val (∏ i ∈ s, cyclicWire i (next i)) : ℝ) =
      ∑ i ∈ s, rawWireDistance φ 1 i (next i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [φ.property.2.1]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    rw [φ.property.2.2.2.1,NNReal.coe_mul]
    have ha : 0 < (φ.val (cyclicWire j (next j)) : ℝ) := by
      exact_mod_cast spectral_value_pos φ (cyclicWire_nonzero j (next j))
    have hb : 0 < (φ.val (∏ i ∈ s, cyclicWire i (next i)) : ℝ) := by
      exact_mod_cast spectral_value_pos φ (Finset.prod_ne_zero_iff.mpr (fun i _ => cyclicWire_nonzero i (next i)))
    rw [Real.logb_mul ha.ne' hb.ne',ih]
    simp [rawWireDistance,rawLogPrice,cyclicWire]

/-- The strict upper endpoint from Theorem 5.2 for the tensor of the
binary cycle on 2(k+1)+1 sites, with no extra spectral assumptions. -/
theorem odd_cycle_strict_spectral_upper (k : ℕ) (hk : 1 ≤ k) :
    Real.logb 2 (asymptoticRank (cycleProduct (K:=K) k)) <
      (((2*(k+1)+1:ℕ):ℝ)^2) / ((2*(k+1)+2:ℕ):ℝ) := by
  classical
  letI : Fact (1 < 2*(k+1)+1) := ⟨by omega⟩
  obtain ⟨φ,hφ⟩ := exists_spectral_value_eq_asymptoticRank (cycleProduct (K:=K) k)
  obtain ⟨X,mX,P,f,_,eq,_⟩ := exists_metric_price_realization φ 1 zero_le_one
  letI := mX
  obtain ⟨Y,mY,Q,⟨e⟩,_,cat⟩ := P.exists_complete_catZero_extension
  letI := mY
  let x (i : ZMod (2*(k+1)+1)) := e.map (f i)
  have hd (i j) : dist (x i) (x j) = rawWireDistance φ 1 i j := by
    simp only [x,e.isometry.dist_eq,eq]
  have hcp (p : ZMod (2*(k+1)+1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
      0 ≤ ∑ i, ∑ j, (1-2*dist (x i) (x j))*p i*p j := by
    have hg := GraphTensorVerification.spectral_copositive φ p hp
    have hh (i j : ZMod (2*(k+1)+1)) : (1-2*rawWireDistance φ 1 i j)*p i*p j =
        p i*(1-2*rawWireDistance φ 1 i j)*p j := by ring
    simp_rw [hd,hh]
    exact hg
  have h := odd_cyclic_copo_strict cat k hk x hcp
  simp_rw [hd] at h
  rw [← hφ,cycleProduct,cyclic_log_sum]
  have hpos : 0 < ((2*(k+1)+2:ℕ):ℝ) := by positivity
  apply (lt_div_iff₀ hpos).2
  push_cast at h ⊢
  nlinarith

#print axioms odd_cycle_strict_spectral_upper
end
end C5GeneralCycles
