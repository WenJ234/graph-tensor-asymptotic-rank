import ThreeBlocks
import MultipartiteLightRank
import Mathlib.Data.List.Nodup

namespace WenJ.GraphTensor.MaxCut
open OddCliquePaper GraphTensorVerification
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

variable {P : Type} [DecidableEq P] {n : ℕ}

def partMass (label : Fin n → P) (p : P) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun v => label v = p)).card

theorem card_color_eq_groupSize (label : Fin n → P) (group : P → Fin 3)
    (ps : List P) (hnd : ps.Nodup) (i : Fin 3)
    (hgroup : ∀ v : Fin n, group (label v) = i ↔ label v ∈ ps) :
    Fintype.card (ColorClass (group ∘ label) i) = groupSize (partMass label) ps := by
  classical
  rw [Fintype.card_of_subtype
    ((Finset.univ : Finset (Fin n)).filter (fun v => label v ∈ ps))]
  · have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin n)) ps.toFinset label
    have hs : (∑ p ∈ ps.toFinset, partMass label p) =
        groupSize (partMass label) ps := by
      simpa [groupSize] using List.sum_toFinset (partMass label) hnd
    rw [← hs]
    simpa [partMass] using h.symm
  · intro v
    simpa [Function.comp_def] using (hgroup v).symm

theorem groupSize_all_parts [Fintype P] (label : Fin n → P) :
    groupSize (partMass label) (Finset.univ : Finset P).toList = n := by
  unfold groupSize
  rw [Finset.sum_map_toList]
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset P) label
  refine Eq.trans ?_ (show _ = n by simpa using h)
  apply Finset.sum_congr rfl
  intro p _
  unfold partMass
  congr 1

/-- Lists enumerate disjoint collections of original parts, not individual
vertices. Hence this map never splits a part, and its three fibers have
exactly the promised sums of part masses. -/
theorem color_three_part_lists [Fintype P] (label : Fin n → P)
    (a b c : List P) (hcover : (a ++ b ++ c).Perm (Finset.univ : Finset P).toList) :
    ∃ group : P → Fin 3,
      Fintype.card (ColorClass (group ∘ label) 1) = groupSize (partMass label) a ∧
      Fintype.card (ColorClass (group ∘ label) 0) = groupSize (partMass label) b ∧
      Fintype.card (ColorClass (group ∘ label) 2) = groupSize (partMass label) c := by
  have hnd := hcover.nodup_iff.mpr (Finset.nodup_toList _)
  rw [List.nodup_append] at hnd
  obtain ⟨hab,hc,habc⟩ := hnd
  rw [List.nodup_append] at hab
  obtain ⟨ha,hb,hab⟩ := hab
  have hall (p : P) : p ∈ a ∨ p ∈ b ∨ p ∈ c := by
    have hp : p ∈ a ++ b ++ c := hcover.mem_iff.mpr (by simp)
    simpa only [List.mem_append,or_assoc] using hp
  have h_ac (p : P) (hp : p ∈ a) : p ∉ c := fun h => habc p (List.mem_append_left _ hp) p h rfl
  have h_bc (p : P) (hp : p ∈ b) : p ∉ c := fun h => habc p (List.mem_append_right _ hp) p h rfl
  let group (p : P) : Fin 3 := if p ∈ a then 1 else if p ∈ b then 0 else 2
  refine ⟨group,card_color_eq_groupSize _ _ a ha 1 ?_,
    card_color_eq_groupSize _ _ b hb 0 ?_,card_color_eq_groupSize _ _ c hc 2 ?_⟩
  · intro v
    by_cases h₁ : label v ∈ a <;> by_cases h₂ : label v ∈ b <;> simp [group,h₁,h₂]
  · intro v
    by_cases h₁ : label v ∈ a <;> by_cases h₂ : label v ∈ b
    · exact (hab (label v) h₁ (label v) h₂ rfl).elim
    all_goals simp [group,h₁,h₂]
  · intro v
    by_cases h₁ : label v ∈ a
    · simp [group,h₁,h_ac _ h₁]
    by_cases h₂ : label v ∈ b
    · simp [group,h₁,h₂,h_bc _ h₂]
    · have h₃ := (hall (label v)).resolve_left h₁ |>.resolve_left h₂
      simp [group,h₁,h₂,h₃]

theorem order_three_groups (mass : List P → ℕ) (a b c : List P) :
    ∃ A B C : List P, [A,B,C].Perm [a,b,c] ∧ mass C ≤ mass B ∧ mass B ≤ mass A := by
  have h₁ : [b,a,c].Perm [a,b,c] := List.Perm.swap a b [c]
  have h₂ : [a,c,b].Perm [a,b,c] := (List.Perm.swap b c []).cons a
  have h₃ : [c,a,b].Perm [a,b,c] := (List.Perm.swap a c [b]).trans h₂
  have h₄ : [b,c,a].Perm [a,b,c] := ((List.Perm.swap a c []).cons b).trans h₁
  have h₅ : [c,b,a].Perm [a,b,c] := (List.Perm.swap b c [a]).trans h₄
  by_cases hba : mass b ≤ mass a
  · by_cases hcb : mass c ≤ mass b
    · exact ⟨a,b,c,List.Perm.refl _,hcb,hba⟩
    · by_cases hca : mass c ≤ mass a
      · exact ⟨a,c,b,h₂,by omega,hca⟩
      · exact ⟨c,a,b,h₃,hba,by omega⟩
  · by_cases hca : mass c ≤ mass a
    · exact ⟨b,a,c,h₁,hca,by omega⟩
    · by_cases hcb : mass c ≤ mass b
      · exact ⟨b,c,a,h₄,by omega,hcb⟩
      · exact ⟨c,b,a,h₅,by omega,by omega⟩

theorem ordered_balanced_part_lists [Fintype P] (label : Fin n → P)
    (hlen : 2 ≤ Fintype.card P)
    (hlight : ∀ p, 0 < partMass label p ∧ 2*partMass label p < n) :
    ∃ a b c : List P,
      (a ++ b ++ c).Perm (Finset.univ : Finset P).toList ∧
      let x := groupSize (partMass label) a
      let y := groupSize (partMass label) b
      let z := groupSize (partMass label) c
      0 < z ∧ z ≤ y ∧ y ≤ x ∧ x+y+z = n ∧ x ≤ y+z := by
  let parts := (Finset.univ : Finset P).toList
  obtain ⟨a,b,c,hcover,hgood⟩ := balancedThreeBlocks_strict
    (partMass label) n parts (by simpa [parts] using hlen)
    (groupSize_all_parts label) (fun p _ => hlight p)
  obtain ⟨A,B,C,hord,hCB,hBA⟩ := order_three_groups (groupSize (partMass label)) a b c
  have hflat : (A ++ B ++ C).Perm (a ++ b ++ c) := by
    simpa [List.append_assoc] using hord.flatten
  have hperm : (A ++ B ++ C).Perm parts := hflat.trans (hcover ▸ List.Perm.refl _)
  have htot : groupSize (partMass label) (A ++ B ++ C) = n := by
    unfold groupSize
    rw [(hperm.map (partMass label)).sum_eq]
    exact groupSize_all_parts label
  rw [groupSize_append,groupSize_append] at htot
  have hA := hgood A (hord.mem_iff.mp (by simp))
  have hC := hgood C (hord.mem_iff.mp (by simp))
  exact ⟨A,B,C,hperm,hC.1,hCB,hBA,htot,by omega⟩

/-- The light-case formula for the manuscript's labelled multipartite
tensor. The groups are generated from the original parts, not assumed
as an extra hypothesis. -/
theorem multipartite_light_exponent_exact {K : Type} [Field K] [Fintype P]
    [Nonempty (Fin n)] (label : Fin n → P) (hn : 2 ≤ n)
    (hlen : 2 ≤ Fintype.card P)
    (hlight : ∀ p, 0 < partMass label p ∧ 2*partMass label p < n) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    Real.logb 2 (asymptoticRank (simpleGraphWire K E)) = (n:ℝ)^2/4 := by
  dsimp only
  let E := (Finset.univ : Finset (SortedEdge n)).filter
    (fun e => label e.val.1 ≠ label e.val.2)
  change Real.logb 2 (asymptoticRank (simpleGraphWire K E)) = (n:ℝ)^2/4
  obtain ⟨a,b,c,hperm,hz,hzy,hyx,hsum,hhalf⟩ := ordered_balanced_part_lists label hlen hlight
  obtain ⟨group,hx,hy,hz'⟩ := color_three_part_lists label a b c hperm
  have hlo := multipartite_three_color_lower (K := K) label group _ _ _ hx hy hz'
    hz hzy hyx hsum hhalf
  refine le_antisymm ?_ hlo
  have hp : 0 < asymptoticRank (simpleGraphWire K E) := by
    have hnon := asymptoticRank_nonneg (simpleGraphWire K E)
    by_contra! h
    have hz₀ : asymptoticRank (simpleGraphWire K E) = 0 := le_antisymm h hnon
    change (n:ℝ)^2/4 ≤ Real.logb 2 (asymptoticRank (simpleGraphWire K E)) at hlo
    rw [hz₀,Real.logb_zero] at hlo
    have hn₀ : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact (not_le_of_gt (show (0:ℝ) < (n:ℝ)^2/4 by positivity)) hlo
  calc
    _ ≤ Real.logb 2 ((2:ℝ)^((n:ℝ)^2/4)) :=
      Real.logb_le_logb_of_le (by norm_num) hp (simpleGraphWire_asymptoticRank_upper K hn E)
    _ = _ := Real.logb_rpow (by norm_num) (by norm_num)

#print axioms multipartite_light_exponent_exact
#print axioms ordered_balanced_part_lists
#print axioms card_color_eq_groupSize
#print axioms groupSize_all_parts
#print axioms color_three_part_lists
end WenJ.GraphTensor.MaxCut
