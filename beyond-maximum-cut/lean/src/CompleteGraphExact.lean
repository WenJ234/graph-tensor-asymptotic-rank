import MultipartitePartMap
import GraphMaxCutBridge
import MultipartiteCutExact

namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification
noncomputable section

theorem complete_graph_exponent_exact (K : Type) [Field K] {n : ℕ}
    [Nonempty (Fin n)] (hn : 2 ≤ n) :
    Real.logb 2 (asymptoticRank (simpleGraphWire K (Finset.univ : Finset (SortedEdge n))))
      = (n:ℝ)^2/4 := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    let E := (Finset.univ : Finset (SortedEdge 2))
    let f (i : Fin 2) : Bool := decide (i = 1)
    have hcut : edgeCutSize (E.toList.map Subtype.val) f = 1 := by
      rw [graph_cut_eq_card]
      let e : SortedEdge 2 := ⟨(0,1),by decide⟩
      have hE : cutEdges E f = {e} := by
        ext x
        obtain ⟨⟨i,j⟩,hij⟩ := x
        fin_cases i <;> fin_cases j <;> first | contradiction | decide +revert
      rw [hE, Finset.card_singleton]
    have hlo := graph_cut_le_exponent_any K (E.toList.map Subtype.val) f
    rw [hcut, Nat.cast_one, ← simpleGraphWire_eq_list] at hlo
    have hu := simpleGraphWire_asymptoticRank_upper K (n := 2) (by decide) E
    have hp : 0 < asymptoticRank (simpleGraphWire K E) := by
      rw [simpleGraphWire_eq_list]
      exact zero_lt_one.trans_le (graph_wire_asymptoticRank_ge_one (K := K) _)
    have hu' := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hp hu
    rw [Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num)] at hu'
    exact le_antisymm hu' (by norm_num; exact hlo)
  · have hm (p : Fin n) : partMass id p = 1 := by
      unfold partMass
      have hs : (Finset.univ.filter (fun x : Fin n => id x = p)) = {p} := by
        ext x
        simp
      rw [hs, Finset.card_singleton]
    have hs := multipartite_light_exponent_exact (K := K) (id : Fin n → Fin n)
      hn (by simpa using hn) (fun p => by rw [hm]; omega)
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => (id e.val.1 : Fin n) ≠ id e.val.2)
    change Real.logb 2 (asymptoticRank (simpleGraphWire K E)) = (n:ℝ)^2/4 at hs
    have he : E = Finset.univ := by
      ext e
      simp [E, ne_of_lt e.property]
    simpa only [he] using hs

#print axioms complete_graph_exponent_exact
end
end WenJ.GraphTensor.MaxCut
