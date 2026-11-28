import Lean
namespace WenJ.GraphTensor.MaxCut
universe u
variable {α : Type u}

def groupSize (partSize : α → Nat) (parts : List α) : Nat := (parts.map partSize).sum

theorem groupSize_append (partSize : α → Nat) (a b : List α) :
    groupSize partSize (a ++ b) = groupSize partSize a + groupSize partSize b := by
  simp [groupSize, List.sum_append]

/-- Group neighboring parts, preserving the ordered list of entire parts. -/
theorem balancedThreeGroups (partSize : α → Nat) (N : Nat)
    (groups : List (List α)) (hlen : 3 ≤ groups.length)
    (hsum : groupSize partSize groups.flatten = N)
    (hvalid : ∀ g ∈ groups, 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N) :
    ∃ a b c : List α, a ++ b ++ c = groups.flatten ∧
      (∀ g ∈ [a,b,c], 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N) := by
  generalize hlength : groups.length = n
  induction n using Nat.strongRecOn generalizing groups with
  | ind n ih =>
    rcases groups with (_ | ⟨a, (_ | ⟨b, (_ | ⟨c, (_ | ⟨d, rest⟩)⟩)⟩)⟩)
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · exact ⟨a,b,c,by simp [List.append_assoc], hvalid⟩
    · have ha := hvalid a (by simp)
      have hb := hvalid b (by simp)
      have hc := hvalid c (by simp)
      have hd := hvalid d (by simp)
      have hsum' : groupSize partSize a + groupSize partSize b +
          groupSize partSize c + groupSize partSize d ≤ N := by
        simp only [List.flatten_cons, groupSize_append] at hsum
        omega
      by_cases hab : 2 * (groupSize partSize a + groupSize partSize b) ≤ N
      · let merged := (a ++ b) :: c :: d :: rest
        have hflatten : merged.flatten = (a :: b :: c :: d :: rest).flatten := by
          simp [merged, List.append_assoc]
        have hnew : ∀ g ∈ merged, 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N := by
          intro g hg
          have hg' : g = a ++ b ∨ g = c ∨ g = d ∨ g ∈ rest := by simpa [merged] using hg
          rcases hg' with hg' | hg' | hg' | hg'
          · rw [hg', groupSize_append]
            exact ⟨by omega, hab⟩
          · exact hg' ▸ hc
          · exact hg' ▸ hd
          · exact hvalid g (by simp [hg'])
        have hlenMerged : 3 ≤ merged.length := by simp [merged]
        have hstep : merged.length < n := by
          simp [merged] at hlength ⊢
          omega
        obtain ⟨a',b',c',heq,hout⟩ :=
          ih merged.length hstep merged hlenMerged (hflatten ▸ hsum) hnew rfl
        exact ⟨a',b',c',heq.trans hflatten,hout⟩
      · let merged := a :: b :: (c ++ d) :: rest
        have hflatten : merged.flatten = (a :: b :: c :: d :: rest).flatten := by
          simp [merged, List.append_assoc]
        have hcd : 2 * (groupSize partSize c + groupSize partSize d) ≤ N := by omega
        have hnew : ∀ g ∈ merged, 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N := by
          intro g hg
          have hg' : g = a ∨ g = b ∨ g = c ++ d ∨ g ∈ rest := by simpa [merged] using hg
          rcases hg' with hg' | hg' | hg' | hg'
          · exact hg' ▸ ha
          · exact hg' ▸ hb
          · rw [hg', groupSize_append]
            exact ⟨by omega, hcd⟩
          · exact hvalid g (by simp [hg'])
        have hlenMerged : 3 ≤ merged.length := by simp [merged]
        have hstep : merged.length < n := by
          simp [merged] at hlength ⊢
          omega
        obtain ⟨a',b',c',heq,hout⟩ :=
          ih merged.length hstep merged hlenMerged (hflatten ▸ hsum) hnew rfl
        exact ⟨a',b',c',heq.trans hflatten,hout⟩

theorem balancedThreeBlocks (partSize : α → Nat) (N : Nat) (parts : List α)
    (hlen : 3 ≤ parts.length) (hsum : groupSize partSize parts = N)
    (hvalid : ∀ p ∈ parts, 0 < partSize p ∧ 2 * partSize p ≤ N) :
    ∃ a b c : List α, a ++ b ++ c = parts ∧
      (∀ g ∈ [a,b,c], 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N) := by
  let groups : List (List α) := parts.map fun p => [p]
  have hflatten (xs : List α) : (xs.map fun p => [p]).flatten = xs := by
    induction xs with
    | nil => rfl
    | cons p ps ih => simp [ih]
  have hg : groups.flatten = parts := hflatten parts
  have hgroup : ∀ g ∈ groups, 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N := by
    intro g h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    simpa [groupSize] using hvalid p hp
  simpa only [hg] using balancedThreeGroups partSize N groups
    (by simpa [groups] using hlen) (by simpa only [hg] using hsum) hgroup

theorem balancedThreeBlocks_strict (partSize : α → Nat) (N : Nat) (parts : List α)
    (hlen : 2 ≤ parts.length) (hsum : groupSize partSize parts = N)
    (hvalid : ∀ p ∈ parts, 0 < partSize p ∧ 2 * partSize p < N) :
    ∃ a b c : List α, a ++ b ++ c = parts ∧
      (∀ g ∈ [a,b,c], 0 < groupSize partSize g ∧ 2 * groupSize partSize g ≤ N) := by
  have h₃ : 3 ≤ parts.length := by
    rcases parts with (_ | ⟨p, (_ | ⟨q, (_ | ⟨r,rest⟩)⟩)⟩)
    · simp at hlen
    · simp at hlen
    · have hp := (hvalid p (by simp)).2
      have hq := (hvalid q (by simp)).2
      simp [groupSize] at hsum
      apply False.elim
      omega
    · simp
  exact balancedThreeBlocks partSize N parts h₃ hsum
    (fun p h => ⟨(hvalid p h).1, Nat.le_of_lt (hvalid p h).2⟩)
end WenJ.GraphTensor.MaxCut
#print axioms WenJ.GraphTensor.MaxCut.balancedThreeGroups
#print axioms WenJ.GraphTensor.MaxCut.balancedThreeBlocks
#print axioms WenJ.GraphTensor.MaxCut.balancedThreeBlocks_strict
