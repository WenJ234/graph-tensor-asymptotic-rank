import OddCliquePriceExact
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Relate the optimized joint cost to the sum of five attained local minima. -/
namespace OddCliquePaper
open scoped BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def vertexTransport (p : Fin 5 → Fin 5 → E) (i : Fin 5) (y : E) : ℝ :=
  ∑ j, if i = j then 0 else ‖p i j - y‖

private theorem vertexTransport_nonneg (p : Fin 5 → Fin 5 → E) (i : Fin 5) (y : E) :
    0 ≤ vertexTransport p i y := by
  unfold vertexTransport
  apply Finset.sum_nonneg
  intro j hj
  split <;> positivity

theorem vertex_transport_minimum_attained (p : Fin 5 → Fin 5 → E) (i : Fin 5) :
    ∃ x : E, ∀ y, vertexTransport p i x ≤ vertexTransport p i y := by
  let j : Fin 5 := if i = 0 then 1 else 0
  have hij : i ≠ j := by
    unfold j
    by_cases h : i = 0
    · simp [h]
    · simp [h]
  let a := p i j
  let R := vertexTransport p i a
  have hR : 0 ≤ R := vertexTransport_nonneg p i a
  have ha : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self hR
  have hcont : Continuous (vertexTransport p i) := by
    apply continuous_finsetSum
    intro k hk
    by_cases h : i = k
    · simpa only [if_pos h] using (continuous_const : Continuous (fun _ : E => (0 : ℝ)))
    · simpa [h] using ((continuous_const : Continuous fun _ : E => p i k).sub continuous_id).norm
  obtain ⟨x, hx, hx_min⟩ := (isCompact_closedBall a R).exists_isMinOn ⟨a,ha⟩ hcont.continuousOn
  refine ⟨x, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall a R
  · exact hx_min hy
  · have hdy : R < ‖p i j - y‖ := by
      simpa only [Metric.mem_closedBall, not_le, dist_comm y a, dist_eq_norm, a] using hy
    have hterm : ‖p i j - y‖ ≤ vertexTransport p i y := by
      unfold vertexTransport
      calc
        ‖p i j - y‖ = (if i = j then 0 else ‖p i j - y‖) := by simp [hij]
        _ ≤ ∑ k, (if i = k then 0 else ‖p i k - y‖) :=
          Finset.single_le_sum (f := fun k : Fin 5 => if i = k then (0 : ℝ) else ‖p i k - y‖)
            (fun k _ => by split <;> positivity) (Finset.mem_univ j)
    exact (hx_min ha).trans (hdy.le.trans hterm)

theorem joint_transport_minimum_attained (p : Fin 5 → Fin 5 → E) :
    ∃ z : Fin 5 → E, minTransport p = localTransport p z ∧
      ∀ i y, vertexTransport p i (z i) ≤ vertexTransport p i y := by
  classical
  choose z hz using vertex_transport_minimum_attained p
  refine ⟨z, le_antisymm ?_ ?_, hz⟩
  · apply ciInf_le
    exact ⟨0, by rintro _ ⟨y,rfl⟩; exact Finset.sum_nonneg (fun i _ => vertexTransport_nonneg p i (y i))⟩
  · apply le_ciInf
    intro y
    exact Finset.sum_le_sum (fun i _ => hz i (y i))

#print axioms joint_transport_minimum_attained
end
end OddCliquePaper
