import MultipartiteMaxCutTheorem

namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification
noncomputable section

theorem exists_maximal_part {P : Type} [Fintype P] [DecidableEq P] {n : ℕ}
    (label : Fin n → P) (hlen : 2 ≤ Fintype.card P) :
    ∃ big : P, ∀ p, partMass label p ≤ partMass label big := by
  letI : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p,_,hp⟩ := Finset.exists_max_image Finset.univ
    (partMass label) Finset.univ_nonempty
  exact ⟨p,fun q => hp q (Finset.mem_univ q)⟩

/-- Theorem 4, for a labelled complete multipartite graph with every part
nonempty. The maximizing part is supplied with its checked bound on all
part masses, and either branch handles the exact same graph tensor. -/
theorem multipartite_exponent_and_maxCut {K P : Type} [Field K] [Fintype P]
    [DecidableEq P] {n : ℕ} [Nonempty (Fin n)] (label : Fin n → P)
    (big : P) (hn : 2 ≤ n) (hlen : 2 ≤ Fintype.card P)
    (hpos : ∀ p, 0 < partMass label p)
    (hmax : ∀ p, partMass label p ≤ partMass label big) :
    let b := partMass label big
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    let γ := Real.logb 2 (asymptoticRank (simpleGraphWire K E))
    γ = (if n ≤ 2*b then ((n-b:ℕ):ℝ)*b else (n:ℝ)^2/4) ∧
      (γ = maxCutWeight (graphEdgeSet E) ↔
        n ≤ 2*b ∨ ∃ f : Fin n → Bool,
          (∀ i j, label i = label j → f i = f j) ∧
          (cutSide f true).card = (cutSide f false).card) := by
  dsimp only
  let b := partMass label big
  by_cases hb : n ≤ 2*b
  · have hb' : n-b ≤ b := by omega
    let H := (Finset.univ : Finset (Fin n)).filter (fun i => label i = big)
    have hH : H.card = b := rfl
    have hO : ((Finset.univ : Finset (Fin n)) \ H).card = n-b := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ H),Finset.card_univ,
        Fintype.card_fin,hH]
    letI : Nontrivial P :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨p,hp⟩ := exists_ne big
    have hpick : ((Finset.univ : Finset (Fin n)).filter
        (fun i => label i = p)).Nonempty := Finset.card_pos.mp (hpos p)
    obtain ⟨i,hi⟩ := hpick
    have him : i ∈ (Finset.univ : Finset (Fin n)) \ H := by
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,H,Finset.mem_filter]
      have he := (Finset.mem_filter.mp hi).2
      simp [he,hp]
    have ha : 0 < n-b := hO ▸ Finset.card_pos.mpr ⟨i,him⟩
    have h₁ := multipartite_heavy_exponent_exact (K := K) label big (n-b) b ha hb' hH hO
    have h₂ := multipartite_heavy_maxCut_eq (K := K) label big (n-b) b ha hb' hH hO
    rw [if_pos hb]
    exact ⟨h₁, ⟨fun _ => Or.inl hb,fun _ => h₂⟩⟩
  · have hlight (p : P) : 0 < partMass label p ∧ 2*partMass label p < n :=
      ⟨hpos p, by have h := hmax p; change partMass label p ≤ b at h; omega⟩
    have h₁ := multipartite_light_exponent_exact (K := K) label hn hlen hlight
    have h₂ := multipartite_light_maxCut_eq_iff (K := K) label hn hlen hlight
    rw [if_neg hb]
    exact ⟨h₁, by rw [or_iff_right (show ¬ n ≤ 2 * partMass label big from hb)]; exact h₂⟩

#print axioms exists_maximal_part
#print axioms multipartite_exponent_and_maxCut
end
end WenJ.GraphTensor.MaxCut
