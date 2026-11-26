import CutGroupingRank
import WheelCutTensor

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped NNReal
noncomputable section

theorem exact_wheel_cut_flattening_rank (K : Type) [Field K] (r : ℕ) [NeZero r]
    (f : ZMod r → Bool) :
    cutRank (fun i : Option (ZMod r) => cutGrouping f i = 0) K (wheelTensor K r) =
      2 ^ wheelCutSize r f := by
  let s (j : Fin 2) : Prop := j = 0
  letI : DecidablePred s := fun _ => inferInstanceAs (Decidable (_ = (0 : Fin 2)))
  letI : Nonempty {j // s j} := ⟨⟨0,rfl⟩⟩
  letI : Nonempty {j // ¬s j} := ⟨⟨1,by decide⟩⟩
  change cutRank (fun i => s (cutGrouping f i)) K (wheelTensor K r) = _
  rw [← cutRank_groupClass (cutGrouping f) s, grouped_wheel_cut]
  let φ := normalizedSpectrum.toRingHom (cutSpectrum.{0} s K)
  have he : (↑(cutRank s K ((2 : TensorClass.{0} (Fin 2) K)^wheelCutSize r f)) : ℝ≥0) =
      (2 : ℝ≥0)^wheelCutSize r f := by
    change φ ((2 : TensorClass.{0} (Fin 2) K)^wheelCutSize r f) = _
    rw [map_pow,map_ofNat]
  exact_mod_cast he

#print axioms exact_wheel_cut_flattening_rank
end
end WheelVerification
