import OAI.LinearAlgebra.SpectralBooks.CutSpectrum
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open Crossing
noncomputable section

private def sideEquiv {I J : Type} (σ : I → J) (s : J → Prop) (A : I → Type) :
    ((j : {j // s j}) → (i : {i // σ i = j.val}) → A i.val) ≃
    ((i : {i // s (σ i)}) → A i.val) where
  toFun f i := f ⟨σ i,i.property⟩ ⟨i,rfl⟩
  invFun g j i := g ⟨i, i.property.symm ▸ j.property⟩
  left_inv f := by
    funext ⟨j,hj⟩ ⟨i,hi⟩
    change σ i = j at hi
    subst j
    rfl
  right_inv g := rfl

theorem cutRank_groupClass {I J K : Type} [Fintype I] [Fintype J] [Field K]
    (σ : I → J) (s : J → Prop) [DecidablePred s] (T : TensorClass.{0} I K) :
    cutRank s K (groupClass σ T) = cutRank (fun i => s (σ i)) K T := by
  classical
  revert T
  refine Quotient.ind fun X => ?_
  change cutRank s K (groupClass σ (ofRaw X)) = cutRank (fun i => s (σ i)) K (ofRaw X)
  rw [groupClass_ofRaw,cutRank_ofRaw,cutRank_ofRaw]
  let e₁ : ((j : {j // s j}) → (X.group σ).Leg j.val) ≃
      ((i : {i // s (σ i)}) → X.Leg i.val) := sideEquiv σ s X.Leg
  let e₂ : ((j : {j // ¬s j}) → (X.group σ).Leg j.val) ≃
      ((i : {i // ¬s (σ i)}) → X.Leg i.val) := sideEquiv σ (fun j => ¬s j) X.Leg
  have he : cutMatrix s (X.group σ).coeff =
      (cutMatrix (fun i => s (σ i)) X.coeff).submatrix e₁ e₂ := by
    ext r c
    apply congrArg X.coeff
    funext i
    change ((cutEquiv s (X.group σ).Leg).symm (r,c)) (σ i) ⟨i,rfl⟩ =
      ((cutEquiv (fun i => s (σ i)) X.Leg).symm (e₁ r,e₂ c)) i
    by_cases hi : s (σ i) <;>
      simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hi, e₁,e₂,sideEquiv] <;> rfl
  rw [he]
  exact Matrix.rank_submatrix (cutMatrix (fun i => s (σ i)) X.coeff) e₁ e₂

#print axioms cutRank_groupClass
end
end WheelVerification
