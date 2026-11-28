import GraphThreeBlock
import WheelCutTensor

namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification
open scoped NNReal
noncomputable section

variable {I : Type} [Fintype I] [Nonempty I]

def edgeCutSize (es : List (I × I)) (f : I → Bool) : ℕ :=
  (es.map (fun e => if f e.1 ≠ f e.2 then 1 else 0)).sum

theorem group_graph_cut (K : Type) [Field K] (es : List (I × I)) (f : I → Bool) :
    groupClass (boolSite ∘ f) (graphWireTensor K es) =
      (2 : TensorClass.{0} (Fin 2) K) ^ edgeCutSize es f := by
  change groupMulHom (boolSite ∘ f) _ = _
  induction es with
  | nil => simp [graphWireTensor,edgeCutSize]
  | cons e es ih =>
    simp only [graphWireTensor,List.map_cons,List.prod_cons,map_mul,edgeCutSize,List.sum_cons] at *
    rw [show groupMulHom (boolSite ∘ f) (wireAt K e.1 e.2) =
      wireAt K (boolSite (f e.1)) (boolSite (f e.2)) from group_wireAt _ _ _,
      ih,wireAt_fin2,pow_add]

theorem graph_cut_le_asymptoticRank (K : Type) [Field K] (es : List (I × I))
    (f : I → Bool) (hf : Function.Surjective f) :
    (2 : ℝ) ^ edgeCutSize es f ≤ asymptoticRank (graphWireTensor K es) := by
  have hb : Function.Surjective boolSite := by
    intro i
    fin_cases i
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have h := grouped_asymptotic_rank_le (boolSite ∘ f) (hb.comp hf) (graphWireTensor K es)
  rw [group_graph_cut] at h
  obtain ⟨φ,hφ⟩ := spectrum_nonempty.{0} (Fin 2) K
  let ψ : Point (I := Fin 2) (K := K) := ⟨φ,hφ⟩
  let ρ := normalizedSpectrum.toRingHom ψ
  have he : ρ ((2 : TensorClass.{0} (Fin 2) K) ^ edgeCutSize es f) =
              (2 : ℝ≥0)^edgeCutSize es f := by rw [map_pow,map_ofNat]
  have hv := spectral_value_le_asymptoticRank ψ
    ((2 : TensorClass.{0} (Fin 2) K) ^ edgeCutSize es f)
  change (ρ _ : ℝ) ≤ _ at hv
  rw [he,NNReal.coe_pow,NNReal.coe_ofNat] at hv
  exact hv.trans h

theorem graph_cut_le_exponent (K : Type) [Field K] (es : List (I × I))
    (f : I → Bool) (hf : Function.Surjective f) :
    (edgeCutSize es f : ℝ) ≤ Real.logb 2 (asymptoticRank (graphWireTensor K es)) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (pow_pos (by norm_num : (0:ℝ)<2) _) (graph_cut_le_asymptoticRank K es f hf)
  simpa [Real.logb_pow] using h

/-- A local coordinate matrix copies the diagonal label to exactly the
endpoints of the edge. Empty fibers contribute 1, including at isolated sites. -/
theorem wireAt_le_two (K : Type) [Field K] (a b : I) :
    wireAt K a b ≤ (2 : TensorClass.{0} I K) := by
  classical
  change wireAt K a b ≤ ((2 : ℕ) : TensorClass.{0} I K)
  rw [← ofRaw_diagonal_fin_eq_natCast I K 2]
  apply ofRaw_le_iff.mpr
  let σ : Fin 2 → I := ![a,b]
  change ((Raw.diagonal (Fin 2) K (Fin 2)).group σ).Restricts
    (Raw.diagonal I K (Fin 2))
  refine ⟨fun i x t => if ∀ j : {j // σ j = i}, x j = t then 1 else 0, fun x => ?_⟩
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff ((groupIndexEquiv σ _).symm x) =
    ∑ t : I → Fin 2, (Raw.diagonal I K (Fin 2)).coeff t *
      ∏ i, (if ∀ j : {j // σ j = i}, x i j = t i then 1 else 0)
  simp only [Raw.diagonal]
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [ite_mul,zero_mul,one_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  apply Finset.sum_congr rfl
  intro k _
  have he : ((groupIndexEquiv σ (fun _ => Fin 2)).symm x = fun _ => k) ↔
      ∀ (i : I) (j : {j // σ j = i}), x i j = k := by
    constructor
    · intro h i j
      obtain ⟨v, hv⟩ := j
      subst i
      exact congrFun h v
    · intro h
      funext j
      exact h (σ j) ⟨j,rfl⟩
  let Q : Prop := (groupIndexEquiv σ (Raw.diagonal (Fin 2) K (Fin 2)).Leg).symm x = fun _ => k
  have heQ : Q ↔ ∀ (i : I) (j : {j // σ j = i}), x i j = k := he
  change @ite K Q (Classical.propDecidable Q) 1 0 =
    ∏ i : I, if (∀ j : {j // σ j = i}, x i j = k) then (1:K) else 0
  by_cases hh : Q
  · have hs (i : I) : ∀ j : {j // σ j = i}, x i j = k := heQ.mp hh i
    have hh₁ : @ite K Q (Classical.propDecidable Q) 1 0 = 1 := by
      letI : Decidable Q := Classical.propDecidable Q
      exact if_pos hh
    refine hh₁.trans (Finset.prod_eq_one ?_).symm
    intro i _
    exact if_pos (hs i)
  · have hn : ¬ ∀ (i : I) (j : {j // σ j = i}), x i j = k :=
      fun h => hh (heQ.mpr h)
    push_neg at hn
    obtain ⟨i,j,hj⟩ := hn
    have hh₀ : @ite K Q (Classical.propDecidable Q) 1 0 = 0 :=
      by
      letI : Decidable Q := Classical.propDecidable Q
      exact if_neg hh
    exact hh₀.trans (Finset.prod_eq_zero (Finset.mem_univ i)
      (if_neg (fun h => hj (h j)))).symm

theorem graph_rank_le_edge_count (K : Type) [Field K] (es : List (I × I)) :
    rank (graphWireTensor K es) ≤ 2 ^ es.length := by
  induction es with
  | nil => exact rank_le_of_le (by simp [graphWireTensor])
  | cons e es ih =>
    change rank (wireAt K e.1 e.2 * graphWireTensor K es) ≤ 2^(es.length+1)
    rw [pow_succ, Nat.mul_comm (2^es.length) 2]
    exact (rank_mul_le _ _).trans (Nat.mul_le_mul (rank_le_of_le (wireAt_le_two K _ _)) ih)

theorem asymptoticRank_le_one_copy (K : Type) [Field K] (T : TensorClass.{0} I K) :
    asymptoticRank T ≤ (rank T : ℝ) := by
  unfold SiteTensor.asymptoticRank
  have h := ciInf_le (f := fun n : ℕ => (rank (T^(n+1)) : ℝ)^((n+1:ℝ)⁻¹))
    (show BddBelow (Set.range _) from ⟨0,by rintro _ ⟨n,rfl⟩; positivity⟩) 0
  simpa using h

theorem bipartite_graph_exact_rank (K : Type) [Field K] (es : List (I × I))
    (f : I → Bool) (hf : Function.Surjective f)
    (h : ∀ e ∈ es, f e.1 ≠ f e.2) :
    rank (graphWireTensor K es) = 2 ^ es.length ∧
      asymptoticRank (graphWireTensor K es) = (2 : ℝ) ^ es.length := by
  have hc : edgeCutSize es f = es.length := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      have ht := h e (by simp)
      have hr := ih (fun a ha => h a (by simp [ha]))
      change (if f e.1 ≠ f e.2 then 1 else 0) + edgeCutSize es f = es.length + 1
      rw [if_pos ht,hr,Nat.add_comm]
  have hl := graph_cut_le_asymptoticRank K es f hf
  rw [hc] at hl
  have hm := asymptoticRank_le_one_copy K (graphWireTensor K es)
  have ho : (rank (graphWireTensor K es) : ℝ) ≤ (2:ℝ)^es.length := by
    exact_mod_cast graph_rank_le_edge_count K es
  have he := le_antisymm ho (hl.trans hm)
  exact ⟨by exact_mod_cast he,le_antisymm (hm.trans ho) hl⟩

#print axioms group_graph_cut
#print axioms graph_cut_le_exponent
#print axioms bipartite_graph_exact_rank
end
end WenJ.GraphTensor.MaxCut
