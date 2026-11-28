import RectangleNormalization
import WheelArbitraryGrouping
import WheelGroupRank

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
noncomputable section

variable {I : Type} [Fintype I] [Nonempty I]

def graphWireTensor (K : Type) [Field K] (edges : List (I × I)) : TensorClass.{0} I K :=
  (edges.map (fun e => wireAt K e.1 e.2)).prod

def graphBetween (edges : List (I × I)) (σ : I → Fin 3) (i j : Fin 3) : ℕ :=
  (edges.map (fun e => between i j (σ e.1) (σ e.2))).sum

theorem graph_groupClass_eq_triangle (K : Type) [Field K] (edges : List (I × I))
    (σ : I → Fin 3) :
    groupClass σ (graphWireTensor K edges) =
      triangleWires K (graphBetween edges σ 0 1) (graphBetween edges σ 2 0)
        (graphBetween edges σ 2 1) := by
  change groupMulHom σ (graphWireTensor K edges) = _
  induction edges with
  | nil => simp [graphWireTensor,graphBetween,triangleWires]
  | cons e es ih =>
    simp only [graphWireTensor,List.map_cons,List.prod_cons,map_mul,graphBetween,List.sum_cons] at *
    rw [show groupMulHom σ (wireAt K e.1 e.2) = wireAt K (σ e.1) (σ e.2) from group_wireAt σ _ _,ih]
    have hw : wireAt K (σ e.1) (σ e.2) =
        triangleWires K (between 0 1 (σ e.1) (σ e.2)) (between 2 0 (σ e.1) (σ e.2))
          (between 2 1 (σ e.1) (σ e.2)) := by
      generalize σ e.1 = u
      generalize σ e.2 = v
      fin_cases u <;> fin_cases v <;>
        simp [between,triangleWires,wireAt_self,wireAt_symm (K := K) (1 : Fin 3) 0,
          wireAt_symm (K := K) (0 : Fin 3) 2,wireAt_symm (K := K) (1 : Fin 3) 2]
    rw [hw]
    simp only [triangleWires,pow_add]
    ac_rfl

theorem graph_three_block_rank_lower (K : Type) [Field K] (edges : List (I × I))
    (σ : I → Fin 3) (hs : Function.Surjective σ) :
    formalOmega K (graphBetween edges σ 0 1) (graphBetween edges σ 2 1) (graphBetween edges σ 2 0) ≤
      Real.logb 2 (SiteTensor.asymptoticRank (graphWireTensor K edges)) := by
  have h := grouped_asymptotic_rank_le σ hs (graphWireTensor K edges)
  rw [graph_groupClass_eq_triangle,triangle_asymptotic_rank_exact] at h
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) _) h
  rwa [Real.logb_rpow (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)] at hl

#print axioms graph_three_block_rank_lower
end
end WheelVerification
