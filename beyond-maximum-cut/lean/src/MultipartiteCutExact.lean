import GraphCutRank
import OddCliquePairCount
import NatMultipartiteCut

namespace WenJ.GraphTensor.MaxCut
open WheelVerification GraphTensorVerification OddCliquePaper
open scoped BigOperators

variable {n : ℕ}

def cutEdges (E : Finset (SortedEdge n)) (f : Fin n → Bool) : Finset (SortedEdge n) :=
  E.filter (fun e => f e.val.1 ≠ f e.val.2)

def cutSide (f : Fin n → Bool) (b : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f i = b)

theorem graph_cut_eq_card (E : Finset (SortedEdge n)) (f : Fin n → Bool) :
    edgeCutSize (E.toList.map Subtype.val) f = (cutEdges E f).card := by
  unfold edgeCutSize
  rw [List.map_map,Finset.sum_map_toList]
  exact Finset.sum_boole _ _

theorem complete_graph_cut_card (f : Fin n → Bool) :
    (cutEdges Finset.univ f).card = (cutSide f true).card * (cutSide f false).card := by
  let g (i : Fin n) : Fin 3 := if f i then 0 else 1
  rw [← graph_cut_eq_card]
  have h : edgeCutSize ((Finset.univ : Finset (SortedEdge n)).toList.map Subtype.val) f =
      pairCount g 0 1 := by
    unfold edgeCutSize pairCount
    rw [List.map_map,Finset.sum_map_toList]
    apply Finset.sum_congr rfl
    intro e _
    cases h₁ : f e.val.1 <;> cases h₂ : f e.val.2 <;> simp [g,h₁,h₂]
  rw [h,pairCount_eq_product g 0 1 (by decide)]
  congr 1
  · apply (Fintype.card_of_subtype (cutSide f true))
    intro i
    cases h₁ : f i <;> simp [cutSide,g,h₁]
  · apply (Fintype.card_of_subtype (cutSide f false))
    intro i
    cases h₁ : f i <;> simp [cutSide,g,h₁]

theorem cutSide_total (f : Fin n → Bool) :
    (cutSide f true).card + (cutSide f false).card = n := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => f i = true)
  have he (i : Fin n) : (¬ f i = true) ↔ f i = false := by cases f i <;> simp
  simpa [cutSide, he] using h

private theorem multipartite_cut_subset {P : Type} [DecidableEq P]
    (label : Fin n → P) (f : Fin n → Bool) :
    cutEdges (Finset.univ.filter (fun e : SortedEdge n => label e.val.1 ≠ label e.val.2)) f
      ⊆ cutEdges Finset.univ f := by
  intro e he
  simpa [cutEdges] using (Finset.mem_filter.mp he).2

theorem multipartite_cut_quarter_iff {P : Type} [DecidableEq P]
    (label : Fin n → P) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    (∃ f : Fin n → Bool, 4*edgeCutSize (E.toList.map Subtype.val) f = n*n) ↔
      ∃ f : Fin n → Bool,
        (∀ i j, label i = label j → f i = f j) ∧
        (cutSide f true).card = (cutSide f false).card := by
  dsimp only
  let E := (Finset.univ : Finset (SortedEdge n)).filter
    (fun e => label e.val.1 ≠ label e.val.2)
  constructor
  · rintro ⟨f,h⟩
    have ht := cutSide_total f
    have hs : cutEdges E f ⊆ cutEdges Finset.univ f := multipartite_cut_subset label f
    have h₁ := Finset.card_le_card hs
    have h₂ := NatModel.four_cut_le_square (cutSide f true).card (cutSide f false).card
    rw [ht,← complete_graph_cut_card] at h₂
    rw [graph_cut_eq_card] at h
    change 4*(cutEdges E f).card = n*n at h
    have he : cutEdges E f = cutEdges Finset.univ f :=
      Finset.eq_of_subset_of_card_le hs (by omega)
    refine ⟨f,?_,?_⟩
    · intro i j hij
      by_contra hne
      have hn : i ≠ j := fun heq => hne (congrArg f heq)
      rcases lt_or_gt_of_ne hn with hl | hl
      · let e : SortedEdge n := ⟨(i,j),hl⟩
        have hm : e ∈ cutEdges Finset.univ f := by simp [cutEdges,e,hne]
        rw [← he] at hm
        have hbad : e ∈ E := (Finset.mem_filter.mp hm).1
        exact (Finset.mem_filter.mp hbad).2 hij
      · let e : SortedEdge n := ⟨(j,i),hl⟩
        have hm : e ∈ cutEdges Finset.univ f := by simp [cutEdges,e,Ne.symm hne]
        rw [← he] at hm
        have hbad : e ∈ E := (Finset.mem_filter.mp hm).1
        exact (Finset.mem_filter.mp hbad).2 hij.symm
    · apply (NatModel.four_cut_eq_square_iff _ _).mp
      rwa [ht,← complete_graph_cut_card,← he]
  · rintro ⟨f,hintact,hbalance⟩
    have hs : cutEdges E f = cutEdges Finset.univ f := by
      apply Finset.Subset.antisymm (multipartite_cut_subset label f)
      intro e hm
      have hne := (Finset.mem_filter.mp hm).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun he => hne (hintact _ _ he)⟩,hne⟩
    refine ⟨f,?_⟩
    rw [graph_cut_eq_card,hs,complete_graph_cut_card]
    calc
      _ = ((cutSide f true).card + (cutSide f false).card) *
          ((cutSide f true).card + (cutSide f false).card) :=
        (NatModel.four_cut_eq_square_iff _ _).mpr hbalance
      _ = _ := congrArg (fun m : ℕ => m*m) (cutSide_total f)

#print axioms complete_graph_cut_card
#print axioms multipartite_cut_quarter_iff
end WenJ.GraphTensor.MaxCut
