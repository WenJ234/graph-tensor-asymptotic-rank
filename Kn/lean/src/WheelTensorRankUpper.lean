import WheelSpectralUpper
import EvenWheelSpectralUpper
import OAI.LinearAlgebra.SpectralBooks.StrassenRank

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators NNReal
noncomputable section

abbrev Point {I K : Type} [Fintype I] [Nonempty I] [Field K] :=
  normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)

def wireAt {I : Type} [Fintype I] (K : Type) [Field K] (a b : I) :
    TensorClass.{0} I K := ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![a,b])

private theorem wireAt_ne_zero {I K : Type} [Fintype I] [Field K] (a b : I) :
    wireAt K a b ≠ 0 := by
  intro hz
  have hp := (ofRaw_eq_zero_iff _).mp hz
  have hd : (Raw.diagonal (Fin 2) K (Fin 2)).coeff = 0 := by
    by_contra hn
    exact (((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff ![a,b]).mpr hn) hp
  have hx := congrFun hd (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at hx
  simp [Raw.diagonal, funext_iff] at hx

private theorem eval_pos {I K : Type} [Fintype I] [Nonempty I] [Field K]
    (φ : Point (I := I) (K := K)) {T : TensorClass.{0} I K} (hT : T ≠ 0) :
    0 < (φ.val T : ℝ) := by exact_mod_cast spectral_value_pos φ hT

private theorem log_mul {I K : Type} [Fintype I] [Nonempty I] [Field K]
    (φ : Point (I := I) (K := K)) {T U : TensorClass.{0} I K}
    (hT : T ≠ 0) (hU : U ≠ 0) :
    Real.logb 2 (φ.val (T*U) : ℝ) = Real.logb 2 (φ.val T : ℝ) + Real.logb 2 (φ.val U : ℝ) := by
  rw [φ.property.2.2.2.1, NNReal.coe_mul, Real.logb_mul (eval_pos φ hT).ne' (eval_pos φ hU).ne']

private theorem log_products {I K A : Type} [Fintype I] [Nonempty I] [Field K]
    (φ : Point (I := I) (K := K)) (s : Finset A) (f : A → TensorClass.{0} I K)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 (φ.val (∏ a ∈ s, f a) : ℝ) = ∑ a ∈ s, Real.logb 2 (φ.val (f a) : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [φ.property.2.1]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      log_mul φ (hf a) (Finset.prod_ne_zero_iff.mpr (fun b _ => hf b)), ih]

def rimTensor (K : Type) [Field K] (r : ℕ) [NeZero r] : TensorClass.{0} (Option (ZMod r)) K :=
  ∏ v : ZMod r, wireAt K (some v) (some (v+1))

def spokeTensor (K : Type) [Field K] (r : ℕ) [NeZero r] : TensorClass.{0} (Option (ZMod r)) K :=
  ∏ v : ZMod r, wireAt K none (some v)

def wheelTensor (K : Type) [Field K] (r : ℕ) [NeZero r] : TensorClass.{0} (Option (ZMod r)) K :=
  rimTensor K r * spokeTensor K r

theorem wheel_log_eval (K : Type) [Field K] (r : ℕ) [NeZero r]
    (φ : Point (I := Option (ZMod r)) (K := K)) :
    Real.logb 2 (φ.val (wheelTensor K r) : ℝ) =
    (∑ v : ZMod r, rawWireDistance φ 1 (some v) (some (v+1))) +
       ∑ v : ZMod r, rawWireDistance φ 1 none (some v) := by
  rw [wheelTensor, rimTensor, spokeTensor]
  rw [log_mul φ (Finset.prod_ne_zero_iff.mpr (fun v _ => wireAt_ne_zero _ _))
    (Finset.prod_ne_zero_iff.mpr (fun v _ => wireAt_ne_zero _ _))]
  rw [log_products φ _ _ (fun v => wireAt_ne_zero _ _),
    log_products φ _ _ (fun v => wireAt_ne_zero _ _)]
  simp only [rawWireDistance, rawLogPrice, one_mul, wireAt]

theorem wheel_rank_upper_by_rim_rows (K : Type) [Field K] (r : ℕ) [NeZero r] :
    Real.logb 2 (asymptoticRank (wheelTensor K r)) ≤ 25*(r : ℝ)/16 := by
  obtain ⟨φ, hφ⟩ := exists_spectral_value_eq_asymptoticRank (wheelTensor K r)
  rw [← hφ,wheel_log_eval]
  exact wheel_spectral_upper_by_rim_rows K r φ

theorem odd_wheel_rank_upper (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    Real.logb 2 (asymptoticRank (wheelTensor K (2*k+1))) ≤
      (5 * ((2*k+1 : ℕ) : ℝ) + 1)^2 / (16 * (((2*k+1 : ℕ) : ℝ)+1)) := by
  obtain ⟨φ, hφ⟩ := exists_spectral_value_eq_asymptoticRank (wheelTensor K (2*k+1))
  rw [← hφ,wheel_log_eval]
  exact odd_wheel_spectral_upper K k hk φ

#print axioms wheel_rank_upper_by_rim_rows
#print axioms odd_wheel_rank_upper
end
end WheelVerification
