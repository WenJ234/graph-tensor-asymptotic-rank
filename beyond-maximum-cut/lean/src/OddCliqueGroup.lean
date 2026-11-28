import CliqueWires
import WheelGroupedCounts

namespace OddCliquePaper
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification WheelVerification
open scoped BigOperators
noncomputable section

def pairCount {n : ℕ} (c : Fin n → Fin 3) (i j : Fin 3) : ℕ :=
  ∑ e : SortedEdge n,
    if (c e.val.1 = i ∧ c e.val.2 = j) ∨
       (c e.val.1 = j ∧ c e.val.2 = i) then 1 else 0

private theorem cliqueWire_eq_wireAt (K : Type) [Field K] {n : ℕ} (e : SortedEdge n) :
    ofRaw (cliqueWire K e) = wireAt K e.val.1 e.val.2 := by
  have h : sortedEndpoints e = ![e.val.1,e.val.2] := by
    funext i
    fin_cases i <;> simp [sortedEndpoints]
  rw [wireAt,cliqueWire,h]

theorem grouped_clique_eq_triangle (K : Type) [Field K] {n : ℕ} [Nonempty (Fin n)]
    (c : Fin n → Fin 3) :
    groupClass c (ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2)) =
      triangleWires K (pairCount c 0 1) (pairCount c 2 0) (pairCount c 2 1) := by
  rw [completeGraph_eq_wires]
  simp_rw [cliqueWire_eq_wireAt]
  change groupMulHom c (∏ e : SortedEdge n, wireAt K e.val.1 e.val.2) = _
  rw [map_prod]
  simp_rw [show ∀ a b, groupMulHom c (wireAt K a b) = wireAt K (c a) (c b) from group_wireAt c]
  let f (e : SortedEdge n) (i j : Fin 3) : ℕ :=
    if (c e.val.1 = i ∧ c e.val.2 = j) ∨
       (c e.val.1 = j ∧ c e.val.2 = i) then 1 else 0
  have h (e : SortedEdge n) : wireAt K (c e.val.1) (c e.val.2) =
      wireAt K 0 1 ^ f e 0 1 * (wireAt K 2 0 ^ f e 2 0 * wireAt K 2 1 ^ f e 2 1) := by
    generalize ha : c e.val.1 = a
    generalize hb : c e.val.2 = b
    fin_cases a <;> fin_cases b <;>
      simp [f,ha,hb,wireAt_self,wireAt_symm (K := K) (1 : Fin 3) 0,
        wireAt_symm (K := K) (0 : Fin 3) 2, wireAt_symm (K := K) (1 : Fin 3) 2]
  simp_rw [h,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl

#print axioms grouped_clique_eq_triangle
end
end OddCliquePaper
