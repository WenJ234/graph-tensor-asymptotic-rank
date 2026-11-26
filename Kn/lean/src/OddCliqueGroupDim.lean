import CliqueWiresDim
import CliqueWireGrouping
import TriangleWireCoordinates
import OddCliqueGroup

namespace OddCliquePaper
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification WheelVerification
open scoped BigOperators
noncomputable section

open scoped BigOperators
private theorem cliqueWireDim_eq_wireDimension (K : Type) [Field K] {n q : ℕ} [Nonempty (Fin n)] (e : SortedEdge n) :
    ofRaw (cliqueWireDim K q e) = wireDimension K e.val.1 e.val.2 q := by
  have h : sortedEndpoints e = ![e.val.1,e.val.2] := by
    funext i
    fin_cases i <;> simp [sortedEndpoints]
  rw [wireDimension,cliqueWireDim,h]

theorem grouped_clique_eq_rectangle (K : Type) [Field K] {n : ℕ} [Nonempty (Fin n)]
    (c : Fin n → Fin 3) (q : ℕ) [NeZero q] :
    groupClass c (ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) n q)) =
      rectWire K (q^pairCount c 0 1) (q^pairCount c 2 1) (q^pairCount c 2 0) := by
  rw [completeGraph_eq_wires_dim]
  simp_rw [cliqueWireDim_eq_wireDimension]
  change groupMulHom c (∏ e : SortedEdge n, wireDimension K e.val.1 e.val.2 q) = _
  rw [map_prod]
  simp_rw [show ∀ a b, groupMulHom c (wireDimension K a b q) = wireDimension K (c a) (c b) q from fun a b => group_wireDim c a b q]
  let f (e : SortedEdge n) (i j : Fin 3) : ℕ :=
    if (c e.val.1 = i ∧ c e.val.2 = j) ∨
       (c e.val.1 = j ∧ c e.val.2 = i) then 1 else 0
  have h (e : SortedEdge n) : wireDimension K (c e.val.1) (c e.val.2) q =
      wireDimension K 0 1 q ^ f e 0 1 * (wireDimension K 2 0 q ^ f e 2 0 * wireDimension K 2 1 q ^ f e 2 1) := by
    generalize ha : c e.val.1 = a
    generalize hb : c e.val.2 = b
    fin_cases a <;> fin_cases b <;>
      simp [f,ha,hb,wireDim_self,wireDim_symm (K := K) (1 : Fin 3) 0 q,
        wireDim_symm (K := K) (0 : Fin 3) 2 q, wireDim_symm (K := K) (1 : Fin 3) 2 q]
  simp_rw [h,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  simp only [rectWire, wireDimension_pow, f, pairCount]

#print axioms grouped_clique_eq_rectangle
end
end OddCliquePaper
