import C5.OddFoldColor
import C5.GeneralRectangle
import GraphThreeBlock
import Mathlib.Data.List.OfFn

namespace C5GeneralCycles
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification
open scoped BigOperators
noncomputable section

def foldEdges (k : ℕ) : List (Fin (2*k+3) × Fin (2*k+3)) :=
  List.ofFn (fun i => (i,finRotate _ i))

private theorem fold_between (k : ℕ) (i j : Fin 3) :
    graphBetween (foldEdges k) (foldColor k) i j =
      (2*k+1)*between i j 0 1 + between i j 1 2 + between i j 2 0 := by
  let d (u v : Fin 3) : ℝ := (between i j u v : ℝ)
  have hs (u v : Fin 3) : d u v = d v u := by
    unfold d between
    simp only [show ((u=i ∧ v=j) ∨ u=j ∧ v=i) ↔ ((v=i ∧ u=j) ∨ v=j ∧ u=i) by tauto]
  have h := fold_color_wire_sum k d hs
  unfold graphBetween foldEdges
  rw [List.map_ofFn,List.sum_ofFn]
  unfold d at h
  exact_mod_cast h

theorem fold_cycle_group (K : Type) [Field K] (k : ℕ) :
    groupClass (foldColor k) (graphWireTensor K (foldEdges k)) =
      triangleWires K (2*k+1) 1 1 := by
  rw [graph_groupClass_eq_triangle,fold_between,fold_between,fold_between]
  norm_num [between]

/-- The lower inequality of Theorem 5.2, now on the actual product of
binary wires, after the verified three-site rectangular normalization. -/
theorem odd_cycle_folded_lower (K : Type) [Field K] (k : ℕ) :
    (2*k+2:ℝ)+1/(4*(2*k+1)) ≤
      Real.logb 2 (asymptoticRank (graphWireTensor K (foldEdges k))) := by
  have h := grouped_asymptotic_rank_le (foldColor k) (fold_color_surjective k)
    (graphWireTensor K (foldEdges k))
  rw [fold_cycle_group,triangle_asymptotic_rank_exact] at h
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) h
  rw [Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1),
    Nat.cast_one] at hlog
  have hk : (1:ℝ) ≤ ((2*k+1:ℕ):ℝ) := by push_cast; nlinarith [show (0:ℝ) ≤ (k:ℝ) by positivity]
  rw [odd_cycle_rectangle_value K _ hk] at hlog
  push_cast at hlog
  convert hlog using 1 <;> ring

#print axioms fold_cycle_group
#print axioms odd_cycle_folded_lower
end
end C5GeneralCycles
