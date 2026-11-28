import CliqueWires

namespace WenJ.GraphTensor.MaxCut
open GraphTensorVerification
open scoped BigOperators

private def ascending (n : ℕ) : SortedEdge n ↪ (Fin n × Fin n) :=
  ⟨Subtype.val, Subtype.val_injective⟩

private def descending (n : ℕ) : SortedEdge n ↪ (Fin n × Fin n) :=
  ⟨fun e => e.val.swap, fun a b h =>
    Subtype.val_injective (by simpa using congrArg Prod.swap h)⟩

def doubledEdges {n : ℕ} (E : Finset (SortedEdge n)) : Finset (Fin n × Fin n) :=
  E.map (ascending n) ∪ E.map (descending n)

def graphEdgeTest {n : ℕ} (E : Finset (SortedEdge n)) (i j : Fin n) : Bool :=
  decide ((i,j) ∈ doubledEdges E)

theorem sum_ordered_edges {n : ℕ} (E : Finset (SortedEdge n))
    (d : Fin n → Fin n → ℝ) (hs : ∀ i j, d i j = d j i) :
    (∑ i, ∑ j, if graphEdgeTest E i j then d i j else 0) =
      2*(∑ e ∈ E, d e.val.1 e.val.2) := by
  classical
  have hd : Disjoint (E.map (ascending n)) (E.map (descending n)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a,ha,ra⟩ := Finset.mem_map.mp hp
    obtain ⟨b,hb,rb⟩ := Finset.mem_map.mp hq
    subst p
    have h₁ := a.property
    have h₂ := b.property
    change b.val.swap = a.val at rb
    rw [← rb] at h₁
    exact (lt_asymm h₁ h₂)
  let f (p : Fin n × Fin n) := d p.1 p.2
  rw [← Finset.sum_product' (f := fun i j => if graphEdgeTest E i j then d i j else 0)]
  rw [Finset.univ_product_univ]
  change (∑ p : Fin n × Fin n, if graphEdgeTest E p.1 p.2 then f p else 0) = _
  simp only [graphEdgeTest, Prod.mk.eta, decide_eq_true_eq]
  rw [← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [doubledEdges,Finset.sum_union hd,Finset.sum_map,Finset.sum_map]
  change (∑ e ∈ E, d e.val.1 e.val.2) + (∑ e ∈ E, d e.val.2 e.val.1) = _
  have hh : (∑ e ∈ E, d e.val.2 e.val.1) = ∑ e ∈ E, d e.val.1 e.val.2 :=
    Finset.sum_congr rfl (fun e _ => hs e.val.2 e.val.1)
  rw [hh]
  ring

#print axioms sum_ordered_edges
end WenJ.GraphTensor.MaxCut
