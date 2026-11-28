import GraphHeavyPartExact
import MultipartiteLightRank
import GraphCutRank

namespace WenJ.GraphTensor.MaxCut
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification GraphTensorVerification OddCliquePaper
noncomputable section

/-- Isolating one part produces the full product cut; match it with the
copositive upper bound when the isolated part has at least half the mass. -/
theorem multipartite_heavy_exponent_and_cut {K P : Type} [Field K] [DecidableEq P]
    {n : ℕ} [Nonempty (Fin n)] (label : Fin n → P) (heavy : P)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hH : ((Finset.univ.filter (fun i => label i = heavy)).card) = b)
    (hO : ((Finset.univ \ Finset.univ.filter (fun i => label i = heavy)).card) = a) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    Real.logb 2 (asymptoticRank (simpleGraphWire K E)) = (a : ℝ)*b ∧
      ∃ f : Fin n → Bool, edgeCutSize (E.toList.map Subtype.val) f = a*b := by
  dsimp only
  let E := (Finset.univ : Finset (SortedEdge n)).filter
    (fun e => label e.val.1 ≠ label e.val.2)
  let H := (Finset.univ : Finset (Fin n)).filter (fun i => label i = heavy)
  let W := Finset.univ \ H
  let g (p : P) : Fin 3 := if p = heavy then 0 else 1
  let f (v : Fin n) : Bool := decide (label v = heavy)
  have hcard0 : Fintype.card (ColorClass (g ∘ label) 0) = b := by
    rw [Fintype.card_of_subtype H]
    · exact hH
    · intro i
      by_cases h : label i = heavy <;> simp [H,g,Function.comp_def,h]
  have hcard1 : Fintype.card (ColorClass (g ∘ label) 1) = a := by
    rw [Fintype.card_of_subtype W]
    · exact hO
    · intro i
      by_cases h : label i = heavy <;> simp [W,H,g,Function.comp_def,h]
  have hf : Function.Surjective f := by
    intro k
    cases k
    · have h : 0 < W.card := by
        dsimp [W,H]
        rw [hO]
        exact ha
      obtain ⟨i,hi⟩ := Finset.card_pos.mp h
      exact ⟨i,by simpa [W,H,f] using (Finset.mem_sdiff.mp hi).2⟩
    · have h : 0 < H.card := by
        dsimp [H]
        rw [hH]
        exact ha.trans_le hab
      obtain ⟨i,hi⟩ := Finset.card_pos.mp h
      exact ⟨i,by simpa [H,f] using hi⟩
  have hb : edgeCutSize (E.toList.map Subtype.val) f =
      graphBetween (E.toList.map Subtype.val) (g ∘ label) 0 1 := by
    unfold edgeCutSize graphBetween
    congr 1
    apply List.map_congr_left
    intro e _
    by_cases h₁ : label e.1 = heavy <;> by_cases h₂ : label e.2 = heavy <;>
      simp [f,g,between,Function.comp_def,h₁,h₂]
  have hcut : edgeCutSize (E.toList.map Subtype.val) f = a*b := by
    rw [hb,multipartite_between_count label g 0 1 (by decide),hcard0,hcard1,mul_comm]
  refine ⟨le_antisymm
    (multipartite_heavy_part_exponent_upper label heavy (a:ℝ) (b:ℝ)
      (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hH) (by exact_mod_cast hO))
    ?_, ⟨f,hcut⟩⟩
  have hc := graph_cut_le_exponent K (E.toList.map Subtype.val) f hf
  rw [hb,multipartite_between_count label g 0 1 (by decide),hcard0,hcard1,
    ← simpleGraphWire_eq_list] at hc
  push_cast at hc
  simpa [mul_comm] using hc

theorem multipartite_heavy_exponent_exact {K P : Type} [Field K] [DecidableEq P]
    {n : ℕ} [Nonempty (Fin n)] (label : Fin n → P) (heavy : P)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hH : ((Finset.univ.filter (fun i => label i = heavy)).card) = b)
    (hO : ((Finset.univ \ Finset.univ.filter (fun i => label i = heavy)).card) = a) :
    let E := (Finset.univ : Finset (SortedEdge n)).filter
      (fun e => label e.val.1 ≠ label e.val.2)
    Real.logb 2 (asymptoticRank (simpleGraphWire K E)) = (a : ℝ)*b :=
  (multipartite_heavy_exponent_and_cut (K := K) label heavy a b ha hab hH hO).1

#print axioms multipartite_heavy_exponent_and_cut
#print axioms multipartite_heavy_exponent_exact
end
end WenJ.GraphTensor.MaxCut
