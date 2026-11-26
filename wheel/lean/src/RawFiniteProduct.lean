import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import Mathlib.Algebra.BigOperators.Fin

/-! Finite products of chosen coefficient arrays, preserving every local
coordinate by equivalence rather than rank estimates. -/
namespace GraphTensorVerification
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

noncomputable section
variable {I K E : Type} [Fintype I] [Nonempty I] [Field K]

def rawIndexedProduct [Fintype E] (W : E → Raw.{0} I K) : Raw.{0} I K := by
  classical
  exact ⟨fun i => (e : E) → (W e).Leg i, inferInstance,
    fun x => ∏ e, (W e).coeff (fun i => x i e)⟩

theorem rawIndexedProduct_fin (n : ℕ) (W : Fin n → Raw.{0} I K) :
    ofRaw (rawIndexedProduct W) = ∏ j, ofRaw (W j) := by
  classical
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero, ← ofRaw_one (I := I) (K := K)]
    apply ofRaw_eq_iff.mpr
    let e (i : I) : ((j : Fin 0) → (W j).Leg i) ≃ PUnit :=
      ⟨fun _ => PUnit.unit, fun _ j => Fin.elim0 j,
        fun _ => funext fun j => Fin.elim0 j, fun p => by cases p; rfl⟩
    refine Raw.reindex_equivalent e fun x => ?_
    simp [rawIndexedProduct, Raw.one]
  | succ n ih =>
    rw [Fin.prod_univ_succ, ← ih (fun j => W j.succ), ← ofRaw_mul]
    apply ofRaw_eq_iff.mpr
    let e (i : I) : ((j : Fin (n+1)) → (W j).Leg i) ≃
        (W 0).Leg i × ((j : Fin n) → (W j.succ).Leg i) :=
      (Fin.consEquiv (fun j => (W j).Leg i)).symm
    refine Raw.reindex_equivalent e fun x => ?_
    change (∏ j : Fin (n+1), (W j).coeff (fun i => x i j)) =
      (W 0).coeff (fun i => (e i (x i)).1) *
      ∏ j : Fin n, (W j.succ).coeff (fun i => (e i (x i)).2 j)
    rw [Fin.prod_univ_succ] <;> rfl

theorem rawIndexedProduct_class [Fintype E] (W : E → Raw.{0} I K) :
    ofRaw (rawIndexedProduct W) = ∏ j, ofRaw (W j) := by
  classical
  let a := Fintype.equivFin E
  let W' (j : Fin (Fintype.card E)) := W (a.symm j)
  calc
    _ = ofRaw (rawIndexedProduct W') := by
      apply ofRaw_eq_iff.mpr
      let e (i : I) : ((x : E) → (W x).Leg i) ≃
          ((j : Fin (Fintype.card E)) → (W' j).Leg i) :=
        Equiv.piCongrLeft' (fun x => (W x).Leg i) a
      refine Raw.reindex_equivalent e fun x => ?_
      change (∏ j : E, (W j).coeff (fun i => x i j)) =
        ∏ j : Fin (Fintype.card E), (W' j).coeff (fun i => (e i (x i)) j)
      exact Fintype.prod_equiv a.symm _ _ (fun _ => rfl) |>.symm
    _ = ∏ j, ofRaw (W' j) := rawIndexedProduct_fin _ _
    _ = _ := Fintype.prod_equiv a.symm _ _ (fun _ => rfl)

#print axioms rawIndexedProduct_class
end
end GraphTensorVerification
