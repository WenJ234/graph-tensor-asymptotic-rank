import GraphMaxCutBridge
import CompleteGraphExact
import MultipartiteMain
import OddCycleGraphBridge
import EuclideanPrice
import GraphThreeBlock

namespace WenJ.GraphTensor.MaxCut

open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification

/-- Proposition 1 on finite nonempty sets, with no surjectivity requirement
on the bipartite coloring. If just one color is used the edge list is empty. -/
theorem bipartite_graph_rank_of_coloring {I : Type} [Fintype I] [Nonempty I]
    (K : Type) [Field K] (es : List (I × I)) (f : I → Bool)
    (h : ∀ e ∈ es, f e.1 ≠ f e.2) :
    rank (graphWireTensor K es) = 2 ^ es.length ∧
      asymptoticRank (graphWireTensor K es) = (2:ℝ)^es.length := by
  cases es with
  | nil =>
    let T := graphWireTensor K ([] : List (I × I))
    have hlow : (1:ℝ) ≤ asymptoticRank T := graph_wire_asymptoticRank_ge_one []
    have hru : rank T ≤ 1 := graph_rank_le_edge_count K []
    have hmid := asymptoticRank_le_one_copy K T
    have hlu : (rank T : ℝ) ≤ 1 := by exact_mod_cast hru
    have hlr : 1 ≤ rank T := by exact_mod_cast hlow.trans hmid
    exact ⟨le_antisymm hru hlr, le_antisymm (hmid.trans hlu) hlow⟩
  | cons e es =>
    apply bipartite_graph_exact_rank K (e::es) f _ h
    have he := h e (by simp)
    intro b
    by_cases h₁ : f e.1 = b
    · exact ⟨e.1,h₁⟩
    · refine ⟨e.2,?_⟩
      cases b <;> cases hE₁ : f e.1 <;> cases hE₂ : f e.2 <;> simp_all


end WenJ.GraphTensor.MaxCut
