import WheelTensorRankUpper
import WheelCounts
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

theorem group_wireAt {I J K : Type} [Fintype I] [Fintype J] [Field K]
    (p : I → J) (a b : I) :
    groupClass p (wireAt K a b) = wireAt K (p a) (p b) := by
  unfold wireAt
  rw [groupClass_ofRaw]
  apply ofRaw_eq_iff.mpr
  have h := (Raw.diagonal (Fin 2) K (Fin 2)).group_group_equivalent ![a,b] p
  have hp : (p ∘ ![a,b]) = ![p a,p b] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hp] using h

theorem wireAt_symm {I K : Type} [Fintype I] [Field K] (a b : I) :
    wireAt K a b = wireAt K b a := by
  unfold wireAt
  exact ofRaw_eq_iff.mpr (Raw.grouped_wire_symm K (Fin 2) a b)

theorem wireAt_self {I K : Type} [Fintype I] [Nonempty I] [Field K] (a : I) :
    wireAt K a a = 1 := by
  apply le_antisymm
  · change ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![a,a]) ≤ _
    have hp : (![a,a] : Fin 2 → I) = fun _ => a := by
      funext i; fin_cases i <;> rfl
    rw [hp]
    exact ofRaw_le_iff.mpr ((Raw.diagonal (Fin 2) K (Fin 2)).group_const_restricts_one a)
  · apply one_le_of_ne_zero
    intro hh
    have hp := (ofRaw_eq_zero_iff _).mp hh
    have hd : (Raw.diagonal (Fin 2) K (Fin 2)).coeff ≠ 0 := by
      intro he
      have hz := congrFun he (fun _ => (0 : Fin 2))
      change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at hz
      simp [Raw.diagonal, funext_iff] at hz
    exact (((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff ![a,a]).mpr hd) hp

def rimGroup (r : ℕ) (v : ZMod r) : Fin 3 :=
  if v.val % 2 = 0 then 0 else 1

def wheelGroup (r : ℕ) : Option (ZMod r) → Fin 3
  | none => 2
  | some v => rimGroup r v

theorem wheelGroup_surj (r : ℕ) (hr : 1 < r) :
    Function.Surjective (wheelGroup r) := by
  intro i
  fin_cases i
  · refine ⟨some 0, ?_⟩
    simp [wheelGroup, rimGroup]
  · refine ⟨some 1, ?_⟩
    have hh : (1 : ZMod r).val = 1 := ZMod.val_one'' (by omega)
    simp [wheelGroup, rimGroup, hh]
  · exact ⟨none,rfl⟩

theorem rim_val_next (r : ℕ) [NeZero r] (v : ZMod r) :
    (v+1).val = rimNext' r v.val := by
  have hv := ZMod.val_lt v
  have he : v+1 = ((v.val+1 : ℕ) : ZMod r) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
  rw [he, ZMod.val_natCast, rimNext']
  split
  · rename_i hi
    exact Nat.mod_eq_of_lt hi
  · rename_i hi
    have he : v.val+1 = r := by omega
    rw [he, Nat.mod_self]

#print axioms group_wireAt
#print axioms wireAt_self
#print axioms wheelGroup_surj
#print axioms rim_val_next
end
end WheelVerification
