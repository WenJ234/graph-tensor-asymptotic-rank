import WireDimension

namespace OddCliquePaper
open WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

theorem group_wireDim {I J K : Type} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J] [Field K]
    (p : I → J) (a b : I) (q : ℕ) :
    groupClass p (wireDimension K a b q) = wireDimension K (p a) (p b) q := by
  unfold wireDimension
  rw [groupClass_ofRaw]
  apply ofRaw_eq_iff.mpr
  have h := (Raw.diagonal (Fin 2) K (Fin q)).group_group_equivalent ![a,b] p
  have hp : (p ∘ ![a,b]) = ![p a,p b] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hp] using h

theorem wireDim_symm {I K : Type} [Fintype I] [Nonempty I] [Field K] (a b : I) (q : ℕ) :
    wireDimension K a b q = wireDimension K b a q := by
  unfold wireDimension
  exact ofRaw_eq_iff.mpr (Raw.grouped_wire_symm K (Fin q) a b)

theorem wireDim_self {I K : Type} [Fintype I] [Nonempty I] [Field K] (a : I) (q : ℕ) [NeZero q] :
    wireDimension K a a q = 1 := by
  apply le_antisymm
  · change ofRaw ((Raw.diagonal (Fin 2) K (Fin q)).group ![a,a]) ≤ _
    have hp : (![a,a] : Fin 2 → I) = fun _ => a := by
      funext i; fin_cases i <;> rfl
    rw [hp]
    exact ofRaw_le_iff.mpr ((Raw.diagonal (Fin 2) K (Fin q)).group_const_restricts_one a)
  · apply one_le_of_ne_zero
    intro hh
    have hp := (ofRaw_eq_zero_iff _).mp hh
    have hd : (Raw.diagonal (Fin 2) K (Fin q)).coeff ≠ 0 := by
      intro he
      have hz := congrFun he (fun _ => (0 : Fin q))
      change (Raw.diagonal (Fin 2) K (Fin q)).coeff (fun _ => (0 : Fin q)) = (0 : K) at hz
      simp [Raw.diagonal, funext_iff] at hz
    exact (((Raw.diagonal (Fin 2) K (Fin q)).group_ne_zero_iff ![a,a]).mpr hd) hp

end
end OddCliquePaper
