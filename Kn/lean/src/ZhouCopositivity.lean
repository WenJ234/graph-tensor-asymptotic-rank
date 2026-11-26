import PricePullback
import CliqueSum
import SpectralCliqueBound
import GeneralCopositivity

/-! Zhou's spectral copositivity, from the verified complete-clique rank
bound via clone grouping, counting, and real closure. -/
namespace GraphTensorVerification
open OAI OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

noncomputable section
variable {I K : Type} [Fintype I] [Nonempty I] [Field K]

theorem spectral_cp_pos_nat
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (a : I → ℕ) (ha : ∀ i, 0 < a i) :
    0 ≤ ∑ i, ∑ j, (a i : ℝ) * (1 - 2 * rawWireDistance φ 1 i j) * (a j : ℝ) := by
  classical
  let C := Σ i : I, Fin (2*a i)
  let N := Fintype.card C
  let e : C ≃ Fin N := Fintype.equivFin C
  let f (u : Fin N) : I := (e.symm u).1
  let i₀ : I := Classical.choice inferInstance
  have hcard : N = ∑ i, 2*a i := by
    simp [N, C, Fintype.card_sigma]
  have hi : 2*a i₀ ≤ ∑ i, 2*a i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (2*a i)) (Finset.mem_univ i₀)
  have hn : 2 ≤ N := by
    have hpos := ha i₀
    omega
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hf : Function.Surjective f := by
    intro i
    have hs := ha i
    refine ⟨e ⟨i,⟨0,by omega⟩⟩, ?_⟩
    simp [f]
  let ψ := groupSpectralPoint f hf φ
  let d := rawWireDistance ψ 1
  have hb := clique_wire_sum_le (K := K) hn ψ
  have hordered := ordered_clique_sum d
    (rawWireDistance_self ψ 1 zero_le_one) (rawWireDistance_symm ψ 1)
  have hd : (∑ u : Fin N, ∑ v : Fin N, d u v) ≤ (N : ℝ)^2/2 := by
    rw [← hordered]
    linarith only [hb]
  have hcopy :
      (∑ u : Fin N, ∑ v : Fin N, d u v) =
      ∑ u : C, ∑ v : C, rawWireDistance φ 1 u.1 v.1 := by
    apply Fintype.sum_equiv e.symm
    intro u
    apply Fintype.sum_equiv e.symm
    intro v
    exact pullback_wire_distance φ f hf 1 u v
  rw [hcopy] at hd
  apply cp_from_even_clones a (rawWireDistance φ 1)
  have hreal : (N : ℝ) = 2 * ∑ i, (a i : ℝ) := by
    rw [hcard]
    push_cast
    rw [Finset.mul_sum]
  rw [hreal] at hd
  change _ ≤ _ at hd
  nlinarith only [hd]

theorem spectral_copositive
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ i, ∑ j, w i * (1 - 2 * rawWireDistance φ 1 i j) * w j :=
  copositive_of_pos_nat _ (spectral_cp_pos_nat φ) w hw

#print axioms spectral_copositive
end
end GraphTensorVerification
