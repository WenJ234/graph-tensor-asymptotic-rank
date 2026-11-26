import CliqueCoordinates
import RawFiniteProduct
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
import Lemmata.TensorRank.Def.Graph

/-! The actual upstream complete clique coefficient tensor is a product
of the same two-site diagonals at the manuscript’s arbitrary edge dimension. -/
namespace GraphTensorVerification
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

noncomputable section

variable {n q : ℕ} {K : Type} [Field K]

def cliqueWireDim (K : Type) [Field K] (q : ℕ) (e : SortedEdge n) : Raw.{0} (Fin n) K :=
  (Raw.diagonal (Fin 2) K (Fin q)).group (sortedEndpoints e)

def cliqueLegPackingDim (q : ℕ) (i : Fin n) :
    (AdjacentIndex i → Fin q) ≃
      ((e : SortedEdge n) → (_ : {t : Fin 2 // sortedEndpoints e t = i}) → Fin q) :=
  (Equiv.piCongrLeft' (fun _ : AdjacentIndex i => Fin q)
    ((neighborEquivIncident i).trans (slotEquivIncident i).symm)).trans
    (Equiv.piCurry fun _ _ => Fin q)

theorem packed_dim_at_lower (e : SortedEdge n) (z : AdjacentIndex e.val.1 → Fin q) :
    cliqueLegPackingDim q e.val.1 z e ⟨0, by simp [sortedEndpoints]⟩ =
      z ⟨e.val.2, e.property.ne'⟩ := by
  change z (toNeighbor e.val.1 (slotIncident e.val.1 ⟨e, ⟨0, _⟩⟩)) = _
  simp [toNeighbor, slotIncident]

theorem packed_dim_at_upper (e : SortedEdge n) (z : AdjacentIndex e.val.2 → Fin q) :
    cliqueLegPackingDim q e.val.2 z e ⟨1, by simp [sortedEndpoints]⟩ =
      z ⟨e.val.1, e.property.ne⟩ := by
  change z (toNeighbor e.val.2 (slotIncident e.val.2 ⟨e, ⟨1, _⟩⟩)) = _
  have h : e.val.1 ≠ e.val.2 := e.property.ne
  simp [toNeighbor, slotIncident, h]

theorem clique_wire_dim_coeff (e : SortedEdge n) (x : ∀ i : Fin n, AdjacentIndex i → Fin q) :
    (cliqueWireDim K q e).coeff (fun i => cliqueLegPackingDim q i (x i) e) =
      if x e.val.1 ⟨e.val.2, e.property.ne'⟩ =
         x e.val.2 ⟨e.val.1, e.property.ne⟩ then (1 : K) else 0 := by
  classical
  let labels (t : Fin 2) : Fin q := cliqueLegPackingDim q (sortedEndpoints e t)
    (x (sortedEndpoints e t)) e ⟨t,rfl⟩
  change (Raw.diagonal (Fin 2) K (Fin q)).coeff labels = _
  rw [Raw.diagonal_coeff_at (K := K) (1 : Fin 2) labels]
  have lower : labels 0 = x e.val.1 ⟨e.val.2,e.property.ne'⟩ :=
    packed_dim_at_lower e _
  have upper : labels 1 = x e.val.2 ⟨e.val.1,e.property.ne⟩ :=
    packed_dim_at_upper e _
  have eq : (∀ t, labels t = labels 1) ↔
      x e.val.1 ⟨e.val.2,e.property.ne'⟩ = x e.val.2 ⟨e.val.1,e.property.ne⟩ := by
    rw [← lower, ← upper]
    exact ⟨fun h => h 0, fun h t => by fin_cases t <;> first | exact h | rfl⟩
  by_cases h : ∀ t, labels t = labels 1
  · exact (if_pos h).trans (if_pos (eq.mp h)).symm
  · exact (if_neg h).trans (if_neg (fun hg => h (eq.mpr hg))).symm

theorem completeGraph_eq_wires_dim [Nonempty (Fin n)] :
    ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) n q) =
      ∏ e : SortedEdge n, ofRaw (cliqueWireDim K q e) := by
  classical
  rw [← rawIndexedProduct_class]
  apply ofRaw_eq_iff.mpr
  refine Raw.reindex_equivalent (cliqueLegPackingDim q) fun x => ?_
  change Lemmata.TensorRank.completeGraph (𝕜 := K) n q x =
    ∏ e : SortedEdge n, (cliqueWireDim K q e).coeff (fun i => cliqueLegPackingDim q i (x i) e)
  simp_rw [clique_wire_dim_coeff]
  exact consistency_indicator_factorizes x

#print axioms completeGraph_eq_wires_dim
end
end GraphTensorVerification
