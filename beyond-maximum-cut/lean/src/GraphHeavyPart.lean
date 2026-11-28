import GraphCliqueRestriction
import HeavyPartPrice

namespace WenJ.GraphTensor.MaxCut
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open WheelVerification GraphTensorVerification
open scoped BigOperators NNReal
noncomputable section

theorem graph_wire_log_eval {K : Type} [Field K] {n : ℕ} [Nonempty (Fin n)]
    (φ : NSpec n K) (E : Finset (SortedEdge n)) :
    Real.logb 2 (φ.val (simpleGraphWire K E) : ℝ) =
      ∑ e ∈ E, rawWireDistance φ 1 e.val.1 e.val.2 := by
  have hprod : ((normalizedSpectrum.toRingHom φ) (simpleGraphWire K E) : ℝ) =
      ∏ e ∈ E, ((normalizedSpectrum.toRingHom φ) (wireAt K e.val.1 e.val.2) : ℝ) := by
    rw [simpleGraphWire,map_prod,NNReal.coe_prod]
  change Real.logb 2 ((normalizedSpectrum.toRingHom φ) (simpleGraphWire K E) : ℝ) = _
  rw [hprod, Real.logb_prod]
  · apply Finset.sum_congr rfl
    intro e he
    simp only [rawWireDistance, rawLogPrice, wireAt, one_mul]
    rfl
  · intro e he
    have h : 1 ≤ (φ.val (wireAt K e.val.1 e.val.2) : ℝ) := by
      unfold wireAt
      exact_mod_cast one_le_raw_spectralValue φ _ (by
        rw [Raw.group_ne_zero_iff]
        intro h
        have hh := congrFun h (fun _ => (0 : Fin 2))
        change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0:K) at hh
        simpa [Raw.diagonal_coeff_at (K := K) (0 : Fin 2)] using hh)
    exact (zero_lt_one.trans_le h).ne'

theorem graph_heavy_part_exponent_upper {K : Type} [Field K] {n : ℕ} [Nonempty (Fin n)]
    (E : Finset (SortedEdge n)) (H : Finset (Fin n)) (edge : Fin n → Fin n → Bool)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hH : (H.card:ℝ) = b)
    (hO : ((Finset.univ \ H).card:ℝ) = a)
    (hno : ∀ i ∈ H, ∀ j ∈ H, edge i j = false)
    (hcount : ∀ d : Fin n → Fin n → ℝ, (∀ i j, d i j = d j i) →
      (∑ i, ∑ j, if edge i j then d i j else 0) =
        2*(∑ e ∈ E, d e.val.1 e.val.2)) :
    Real.logb 2 (SiteTensor.asymptoticRank (simpleGraphWire K E)) ≤ a*b := by
  have hsz : (Finset.univ \ H).card + H.card = n := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H)]
    simp
  have ho : 0 < (Finset.univ \ H).card := by
    exact_mod_cast (show (0:ℝ) < ((Finset.univ \ H).card:ℝ) by rw [hO]; exact ha)
  have hh : 0 < H.card := by
    exact_mod_cast (show (0:ℝ) < (H.card:ℝ) by rw [hH]; exact ha.trans_le hab)
  letI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < n by omega))
  obtain ⟨φ,hφ⟩ := exists_spectral_value_eq_asymptoticRank (simpleGraphWire K E)
  rw [← hφ,graph_wire_log_eval]
  have h := heavy_part_wire_price_le φ H edge a b ha hab hH hO hno
  rw [hcount _ (rawWireDistance_symm φ 1)] at h
  linarith only [h]

#print axioms graph_wire_log_eval
#print axioms graph_heavy_part_exponent_upper
end
end WenJ.GraphTensor.MaxCut
