import WheelMaxCut
import WheelGroupRank
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators NNReal
noncomputable section

def boolSite : Bool → Fin 2
  | false => 0
  | true => 1

def cutGrouping {r : ℕ} (f : ZMod r → Bool) : Option (ZMod r) → Fin 2
  | none => 0
  | some v => boolSite (f v)

theorem wireAt_fin2 (K : Type) [Field K] (a b : Bool) :
    wireAt K (boolSite a) (boolSite b) =
      (2 : TensorClass.{0} (Fin 2) K) ^ (if a ≠ b then 1 else 0) := by
  have he : wireAt K (0 : Fin 2) 1 = (2 : TensorClass.{0} (Fin 2) K) := by
    have hp : (![0,1] : Fin 2 → Fin 2) = id := by
      funext i
      fin_cases i <;> rfl
    rw [wireAt,hp,ofRaw_eq_iff.mpr ((Raw.diagonal (Fin 2) K (Fin 2)).group_id_equivalent)]
    exact ofRaw_diagonal_fin_eq_natCast (Fin 2) K 2
  cases a <;> cases b <;> simp [boolSite, he, wireAt_self, wireAt_symm (K := K) (1 : Fin 2) 0]

theorem grouped_wheel_cut (K : Type) [Field K] (r : ℕ) [NeZero r] (f : ZMod r → Bool) :
    groupClass (cutGrouping f) (wheelTensor K r) =
      (2 : TensorClass.{0} (Fin 2) K) ^ wheelCutSize r f := by
  change groupMulHom (cutGrouping f) (rimTensor K r * spokeTensor K r) = _
  rw [map_mul]
  unfold rimTensor spokeTensor
  simp only [map_prod]
  simp_rw [show ∀ a b, groupMulHom (cutGrouping f) (wireAt K a b) =
    wireAt K (cutGrouping f a) (cutGrouping f b) from group_wireAt (cutGrouping f)]
  change ((∏ v : ZMod r, wireAt K (boolSite (f v)) (boolSite (f (v+1)))) *
      ∏ v : ZMod r, wireAt K (boolSite false) (boolSite (f v))) = _
  simp_rw [wireAt_fin2, Finset.prod_pow_eq_pow_sum, ← pow_add]
  have hb (v : ZMod r) : (false ≠ f v) ↔ f v = true := by cases f v <;> decide
  simp only [wheelCutSize,spokesCut,rimCut,hb,add_comm]

theorem wheel_asymptotic_rank_lower_by_cut (K : Type) [Field K] (r : ℕ) [NeZero r]
    (f : ZMod r → Bool) (hf : Function.Surjective (cutGrouping f)) :
    Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K r)) ≥ wheelCutSize r f := by
  obtain ⟨φ,hφ⟩ := spectrum_nonempty.{0} (Fin 2) K
  let ψ : Point (I := Fin 2) (K := K) := ⟨φ,hφ⟩
  let h := normalizedSpectrum.toRingHom ψ
  have u : h ((2 : TensorClass.{0} (Fin 2) K) ^ wheelCutSize r f) =
      (2 : ℝ≥0) ^ wheelCutSize r f := by rw [map_pow, map_ofNat]
  have hv := spectral_value_le_asymptoticRank ψ
    ((2 : TensorClass.{0} (Fin 2) K) ^ wheelCutSize r f)
  have hd := grouped_asymptotic_rank_le (cutGrouping f) hf (wheelTensor K r)
  rw [grouped_wheel_cut] at hd
  change (h _ : ℝ) ≤ _ at hv
  rw [u, NNReal.coe_pow, NNReal.coe_ofNat] at hv
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) (hv.trans hd)
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hh

theorem parityCutGrouping_surjective (r : ℕ) [NeZero r] :
    Function.Surjective (cutGrouping (parityCut r)) := by
  intro i
  fin_cases i
  · exact ⟨none,rfl⟩
  · exact ⟨some 0,by simp [cutGrouping,parityCut,boolSite]⟩

theorem wheel_maxcut_lower (K : Type) [Field K] (r : ℕ) [NeZero r] :
    ((3*r)/2 : ℕ) ≤ Real.logb 2 (SiteTensor.asymptoticRank (wheelTensor K r)) := by
  have h := wheel_asymptotic_rank_lower_by_cut K r (parityCut r)
    (parityCutGrouping_surjective r)
  have eq : wheelCutSize r (parityCut r) = (3*r)/2 :=
    wheel_parity_cut_size r
  simpa only [eq] using h

#print axioms wheel_maxcut_lower
#print axioms grouped_wheel_cut
#print axioms wheel_asymptotic_rank_lower_by_cut
end
end WheelVerification
