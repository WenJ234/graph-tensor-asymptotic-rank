import MultipartitePartMap
import MultipartiteCutExact
import MultipartiteHeavyRank
import GraphMaxCutBridge

namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification
noncomputable section

/-- In the light-part branch the actual graph exponent is equal to MaxCut
exactly when a cut places each whole part on one side and balances the
number of vertices on the two sides. -/
theorem multipartite_light_maxCut_eq_iff {K P : Type} [Field K] [Fintype P]
    [DecidableEq P] {n : ℕ} [Nonempty (Fin n)] (label : Fin n → P)
    (hn : 2 ≤ n) (hlen : 2 ≤ Fintype.card P)
    (hlight : ∀ p, 0 < partMass label p ∧ 2*partMass label p < n) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    (Real.logb 2 (asymptoticRank (simpleGraphWire K E)) =
      maxCutWeight (graphEdgeSet E)) ↔
      ∃ f : Fin n → Bool, (∀ i j, label i = label j → f i = f j) ∧
        (cutSide f true).card = (cutSide f false).card := by
  dsimp only
  let E := (Finset.univ : Finset (SortedEdge n)).filter
    (fun e => label e.val.1 ≠ label e.val.2)
  change (Real.logb 2 (asymptoticRank (simpleGraphWire K E)) =
    maxCutWeight (graphEdgeSet E)) ↔ _
  have hex := multipartite_light_exponent_exact (K := K) label hn hlen hlight
  have hcrit := multipartite_cut_quarter_iff label
  change (∃ f : Fin n → Bool, 4*edgeCutSize (E.toList.map Subtype.val) f = n*n) ↔ _
    at hcrit
  constructor
  · intro h
    obtain ⟨f,hf⟩ := cut_attains_maxCutWeight (graphEdgeSet E)
    rw [graph_cutWeight_eq_edgeCutSize,← h,hex] at hf
    refine hcrit.mp ⟨f,?_⟩
    exact_mod_cast (show (4:ℝ)*(edgeCutSize (E.toList.map Subtype.val) f:ℝ) =
      (n:ℝ)*(n:ℝ) by nlinarith only [hf])
  · intro h
    obtain ⟨f,hf⟩ := hcrit.mpr h
    have hf' : (4:ℝ)*(edgeCutSize (E.toList.map Subtype.val) f:ℝ) = (n:ℝ)*(n:ℝ) :=
      by exact_mod_cast hf
    have hw := cut_le_maxCutWeight (graphEdgeSet E) f
    rw [graph_cutWeight_eq_edgeCutSize] at hw
    apply le_antisymm _ (maxCutWeight_le_graph_exponent E)
    rw [hex]
    nlinarith only [hw,hf']

theorem multipartite_heavy_maxCut_eq {K P : Type} [Field K] [DecidableEq P]
    {n : ℕ} [Nonempty (Fin n)] (label : Fin n → P) (heavy : P)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hH : ((Finset.univ.filter (fun i => label i = heavy)).card) = b)
    (hO : ((Finset.univ \ Finset.univ.filter (fun i => label i = heavy)).card) = a) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    Real.logb 2 (asymptoticRank (simpleGraphWire K E)) =
      maxCutWeight (graphEdgeSet E) := by
  dsimp only
  let E := (Finset.univ : Finset (SortedEdge n)).filter (fun e => label e.val.1 ≠ label e.val.2)
  obtain ⟨hex, f, hf⟩ := multipartite_heavy_exponent_and_cut (K := K) label heavy a b ha hab hH hO
  change Real.logb 2 (asymptoticRank (simpleGraphWire K E)) = _
  apply le_antisymm _ (maxCutWeight_le_graph_exponent E)
  rw [hex]
  have hw := cut_le_maxCutWeight (graphEdgeSet E) f
  rw [graph_cutWeight_eq_edgeCutSize, hf, Nat.cast_mul] at hw
  exact hw

#print axioms multipartite_heavy_maxCut_eq
#print axioms multipartite_light_maxCut_eq_iff
end
end WenJ.GraphTensor.MaxCut
