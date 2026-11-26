import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Local clique coordinates in the two representations: a neighbor label,
or a sorted incident edge. This statement is independent of rank. -/
namespace GraphTensorVerification
open scoped BigOperators

abbrev AdjacentIndex {n : ℕ} (i : Fin n) := { j : Fin n // j ≠ i }
abbrev IncidentIndex {n : ℕ} (i : Fin n) :=
  { p : Fin n × Fin n // p.1 < p.2 ∧ (p.1 = i ∨ p.2 = i) }

def toIncident {n : ℕ} (i : Fin n) (j : AdjacentIndex i) : IncidentIndex i :=
  if h : i < j.val then ⟨(i,j.val),h,Or.inl rfl⟩
  else ⟨(j.val,i),lt_of_le_of_ne (le_of_not_gt h) j.property,Or.inr rfl⟩

def toNeighbor {n : ℕ} (i : Fin n) (p : IncidentIndex i) : AdjacentIndex i :=
  if h : p.val.1 = i then
    ⟨p.val.2, fun he => p.property.1.ne (h.trans he.symm)⟩
  else ⟨p.val.1, h⟩

theorem neighbor_incident_inverse {n : ℕ} (i : Fin n) (j : AdjacentIndex i) :
    toNeighbor i (toIncident i j) = j := by
  apply Subtype.ext
  by_cases h : i < j.val
  · simp [toIncident, toNeighbor, h]
  · simp [toIncident, toNeighbor, h, j.property]

theorem incident_neighbor_inverse {n : ℕ} (i : Fin n) (p : IncidentIndex i) :
    toIncident i (toNeighbor i p) = p := by
  apply Subtype.ext
  obtain ⟨⟨u,v⟩, huv, hi⟩ := p
  change u < v at huv
  change u = i ∨ v = i at hi
  rcases hi with rfl | rfl
  · simp [toIncident, toNeighbor, huv]
  · simp [toIncident, toNeighbor, huv.ne, not_lt_of_gt huv]

def neighborEquivIncident {n : ℕ} (i : Fin n) : AdjacentIndex i ≃ IncidentIndex i :=
  ⟨toIncident i, toNeighbor i, neighbor_incident_inverse i, incident_neighbor_inverse i⟩

theorem sorted_consistency_iff {n : ℕ} {A : Type} (x : ∀ i : Fin n, AdjacentIndex i → A) :
    (∀ (i j : Fin n) (h : i < j), x i ⟨j,h.ne'⟩ = x j ⟨i,h.ne⟩) ↔
    (∀ (i j : Fin n) (h : i ≠ j), x i ⟨j,h.symm⟩ = x j ⟨i,h⟩) := by
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with lt | gt
    · exact h i j lt
    · exact (h j i gt).symm
  · intro h i j hij
    exact h i j hij.ne

abbrev SortedEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

theorem consistency_indicator_factorizes {n : ℕ} {A K : Type} [CommMonoidWithZero K]
    [DecidableEq A] [Fintype (SortedEdge n)]
    (x : ∀ i : Fin n, AdjacentIndex i → A) :
    (if ∀ (i j : Fin n) (h : i ≠ j), x i ⟨j,h.symm⟩ = x j ⟨i,h⟩
      then (1 : K) else 0) =
    ∏ e : SortedEdge n,
      if x e.val.1 ⟨e.val.2,e.property.ne'⟩ =
         x e.val.2 ⟨e.val.1,e.property.ne⟩ then 1 else 0 := by
  classical
  by_cases h : ∀ (i j : Fin n) (hn : i < j), x i ⟨j,hn.ne'⟩ = x j ⟨i,hn.ne⟩
  · rw [if_pos ((sorted_consistency_iff x).mp h)]
    symm
    apply Finset.prod_eq_one
    intro e _
    exact if_pos (h _ _ e.property)
  · rw [if_neg (fun all => h ((sorted_consistency_iff x).mpr all))]
    simp only [not_forall] at h
    obtain ⟨i,j,hi,hneq⟩ := h
    symm
    let e : SortedEdge n := ⟨(i,j),hi⟩
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    exact if_neg hneq

def sortedEndpoints {n : ℕ} (e : SortedEdge n) (j : Fin 2) : Fin n :=
  if j = 0 then e.val.1 else e.val.2

abbrev WireSlot {n : ℕ} (i : Fin n) :=
  Σ e : SortedEdge n, { t : Fin 2 // sortedEndpoints e t = i }

theorem sortedEndpoints_injective {n : ℕ} (e : SortedEdge n) :
    Function.Injective (sortedEndpoints e) := by
  intro j k h
  fin_cases j <;> fin_cases k
  · rfl
  · have he : e.val.1 = e.val.2 := by simpa [sortedEndpoints] using h
    exact (e.property.ne he).elim
  · have he : e.val.2 = e.val.1 := by simpa [sortedEndpoints] using h
    exact (e.property.ne he.symm).elim
  · rfl

def slotIncident {n : ℕ} (i : Fin n) (w : WireSlot i) : IncidentIndex i :=
  ⟨w.1.val, w.1.property, by
    have h := w.2.property
    by_cases h0 : w.2.val = 0
    · exact Or.inl (by simpa [sortedEndpoints,h0] using h)
    · exact Or.inr (by simpa [sortedEndpoints,h0] using h)⟩

noncomputable def slotEquivIncident {n : ℕ} (i : Fin n) : WireSlot i ≃ IncidentIndex i :=
  Equiv.ofBijective (slotIncident i) ⟨by
    rintro ⟨e,s⟩ ⟨f,t⟩ h
    have he := congrArg (fun p : IncidentIndex i => p.val) h
    have hef : e = f := Subtype.ext he
    subst f
    have hst : s = t := Subtype.ext
      (sortedEndpoints_injective e (s.property.trans t.property.symm))
    subst t
    rfl, by
    intro p
    let e : SortedEdge n := ⟨p.val,p.property.1⟩
    rcases p.property.2 with h | h
    · refine ⟨⟨e,⟨0,?_⟩⟩,rfl⟩
      simpa [sortedEndpoints,e] using h
    · refine ⟨⟨e,⟨1,?_⟩⟩,rfl⟩
      simpa [sortedEndpoints,e] using h⟩

#print axioms slotEquivIncident
#print axioms consistency_indicator_factorizes
#print axioms neighborEquivIncident
#print axioms sorted_consistency_iff
end GraphTensorVerification
