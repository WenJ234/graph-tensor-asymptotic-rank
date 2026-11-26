import CliqueWires
import RankPowerCore
import Lemmata.TensorRank.Main
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-! A spectral wire sum of a complete binary clique is bounded by the
independently verified rank bound; no copositivity premise is used here. -/
namespace GraphTensorVerification
open OAI OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators NNReal
noncomputable section
variable {n : ℕ} {K : Type} [Field K] [Nonempty (Fin n)]

abbrev NSpec (n : ℕ) (K : Type) [Field K] [Nonempty (Fin n)] :=
  normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin n) K → _ → Prop)

private theorem clique_wire_nz (e : SortedEdge n) :
    ofRaw (cliqueWire K e) ≠ 0 := by
  have hd : (Raw.diagonal (Fin 2) K (Fin 2)).coeff ≠ 0 := by
    intro h
    have hh := congrFun h (fun _ => (0 : Fin 2))
    change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at hh
    simpa [Raw.diagonal_coeff_at (K := K) (0 : Fin 2)] using hh
  exact fun h => ((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff
    (sortedEndpoints e)).mpr hd ((ofRaw_eq_zero_iff _).mp h)

private theorem wire_cost (φ : NSpec n K) (e : SortedEdge n) :
    Real.logb 2 (φ.val (ofRaw (cliqueWire K e)) : ℝ) =
    rawWireDistance φ 1 e.val.1 e.val.2 := by
  have h : sortedEndpoints e = ![e.val.1,e.val.2] := by
    funext j
    fin_cases j <;> simp [sortedEndpoints]
  simp [rawWireDistance, rawLogPrice, cliqueWire, h]

theorem clique_wire_sum_le (hn : 2 ≤ n) (φ : NSpec n K) :
    (∑ e : SortedEdge n, rawWireDistance φ 1 e.val.1 e.val.2) ≤ (n : ℝ)^2 / 4 := by
  classical
  let T := ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2)
  let f := normalizedSpectrum.toRingHom φ
  have hprod : (f T : ℝ) = ∏ e : SortedEdge n, (f (ofRaw (cliqueWire K e)) : ℝ) := by
    unfold T
    rw [completeGraph_eq_wires, map_prod, NNReal.coe_prod]
  have hposWire (e : SortedEdge n) : 0 < (f (ofRaw (cliqueWire K e)) : ℝ) := by
    exact_mod_cast spectral_value_pos φ (clique_wire_nz (K := K) e)
  have hpos : 0 < (f T : ℝ) := by
    rw [hprod]
    exact Finset.prod_pos fun i _ => hposWire i
  have hlog : Real.logb 2 (f T : ℝ) = ∑ e : SortedEdge n, rawWireDistance φ 1 e.val.1 e.val.2 := by
    rw [hprod, Real.logb_prod _ _ (fun i _ => (hposWire i).ne')]
    exact Finset.sum_congr rfl fun e _ => wire_cost φ e
  have hr : Lemmata.TensorRank.Tensor.asymptoticRank (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2) ≤ (2 : ℝ)^((n : ℝ)^2 / 4) := by
    exact (Lemmata.TensorRank.completeGraphBounds (𝕜 := K) n 2 hn (by decide)).2.1
  rw [← hlog, ← Real.logb_rpow (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num) (x := (n : ℝ)^2 / 4)]
  exact Real.logb_le_logb_of_le (by norm_num) hpos
    ((spectral_le_lemmata φ (Lemmata.TensorRank.completeGraph (𝕜 := K) n 2)).trans hr)

#print axioms clique_wire_sum_le
end
end GraphTensorVerification
