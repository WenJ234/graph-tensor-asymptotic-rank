import C5.OddFoldTensor
import C5.OddSpectralStrict
import WireGraphStructure
import OddCycleActualCut

namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification C5GeneralCycles
open scoped BigOperators
noncomputable section

private theorem cycle_group_undo {A B K : Type} [Fintype A] [Fintype B] [Field K]
    (e : A ≃ B) (X : TensorClass.{0} A K) :
    groupClass e.symm (groupClass e X) = X := by
  induction X using Quotient.inductionOn with
  | _ T =>
    change groupClass e.symm (groupClass e (ofRaw T)) = ofRaw T
    simp only [groupClass_ofRaw]
    apply ofRaw_eq_iff.mpr
    have hc := T.group_group_equivalent e e.symm
    have h : (⇑e.symm) ∘ (⇑e) = id := funext fun i => e.symm_apply_apply i
    rw [h] at hc
    exact ⟨restrict_trans hc.1 T.group_id_equivalent.1,
      restrict_trans T.group_id_equivalent.2 hc.2⟩

def oddSiteEquiv (k : ℕ) : Fin (2*k+3) ≃ ZMod (2*(k+1)+1) :=
  (ZMod.finEquiv (2*(k+1)+1)).toEquiv

private theorem oddSiteEquiv_succ (k : ℕ) (i : Fin (2*k+3)) :
    oddSiteEquiv k (finRotate _ i) = oddSiteEquiv k i + 1 := by
  rw [finRotate_apply]
  change (ZMod.finEquiv (2*(k+1)+1)) (i + 1) =
    (ZMod.finEquiv (2*(k+1)+1)) i + 1
  rw [map_add,map_one]

theorem odd_cycle_group_transport (K : Type) [Field K] (k : ℕ) :
    groupClass (oddSiteEquiv k) (graphWireTensor K (foldEdges k)) =
      cycleProduct (K := K) k := by
  change groupClass (oddSiteEquiv k) (graphClass (foldEdges k)) = _
  rw [group_graphClass]
  unfold foldEdges graphClass cycleProduct
  simp only [List.map_ofFn, List.prod_ofFn, oddSiteEquiv_succ]
  apply Fintype.prod_equiv (oddSiteEquiv k)
  intro i
  simp only [Function.comp_apply, oddSiteEquiv_succ]
  rfl

theorem odd_cycle_rank_transport (K : Type) [Field K] (k : ℕ) :
    asymptoticRank (graphWireTensor K (foldEdges k)) =
      asymptoticRank (cycleProduct (K := K) k) := by
  rw [← odd_cycle_group_transport]
  apply le_antisymm
  · calc
      asymptoticRank (graphWireTensor K (foldEdges k)) =
          asymptoticRank (groupClass (oddSiteEquiv k).symm
            (groupClass (oddSiteEquiv k) (graphWireTensor K (foldEdges k)))) :=
        congrArg (fun X => asymptoticRank X) (cycle_group_undo _ _).symm
      _ ≤ _ := grouped_asymptotic_rank_le (oddSiteEquiv k).symm
        (oddSiteEquiv k).symm.surjective _
  · exact grouped_asymptotic_rank_le (oddSiteEquiv k) (oddSiteEquiv k).surjective _

theorem five_cycle_maxcut_paper_bounds (K : Type) [Field K] :
    (49:ℝ)/12 ≤ Real.logb 2 (asymptoticRank (graphWireTensor K (foldEdges 1))) ∧
      Real.logb 2 (asymptoticRank (graphWireTensor K (foldEdges 1))) < (25:ℝ)/6 := by
  constructor
  · convert odd_cycle_folded_lower K 1 using 1 <;> norm_num
  · rw [odd_cycle_rank_transport]
    convert odd_cycle_strict_spectral_upper (K := K) 1 (by decide) using 1 <;> norm_num

/-- All odd cycles have the published strict gap over the actual cut
maximum. The parameter k indexes 2*k+3 vertices. -/
theorem odd_cycle_paper_lower_and_actual_cut (K : Type) [Field K] (k : ℕ) :
    let γ := Real.logb 2 (asymptoticRank (graphWireTensor K (foldEdges k)))
    (2*k+2:ℝ) + 1/(4*(2*k+1)) ≤ γ ∧
    (∀ f : Fin (2*k+3) → Bool, (edgeCutSize (foldEdges k) f : ℝ) < γ) ∧
    (∃ f : Fin (2*k+3) → Bool, edgeCutSize (foldEdges k) f = 2*k+2) := by
  dsimp only
  have h := odd_cycle_folded_lower K k
  refine ⟨h, ?_, odd_cycle_actual_cut_attained k⟩
  intro f
  have hcut : (edgeCutSize (foldEdges k) f : ℝ) ≤ (2*k+2:ℝ) := by
    exact_mod_cast odd_cycle_actual_cut_upper k f
  have hstrict : (2*k+2:ℝ) < (2*k+2:ℝ)+1/(4*(2*k+1)) := by
    apply lt_add_of_pos_right
    positivity
  exact hcut.trans_lt (hstrict.trans_le h)

#print axioms odd_cycle_paper_lower_and_actual_cut
#print axioms odd_cycle_group_transport
#print axioms odd_cycle_rank_transport
#print axioms five_cycle_maxcut_paper_bounds
end
end WenJ.GraphTensor.MaxCut
