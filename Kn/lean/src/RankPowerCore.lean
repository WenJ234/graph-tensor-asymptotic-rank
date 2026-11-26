import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import Lemmata.TensorRank.Def.Asymptotic
import Mathlib.Algebra.BigOperators.Fin

/-! Coefficient-level bridge from the fixed-format Lemmata rank to
    the OAI restriction preorder. This is not a complete-graph exponent theorem. -/
open scoped BigOperators NNReal
open OAI.LinearAlgebra.SpectralBooks

namespace GraphTensorVerification
open SiteTensor
variable {I K : Type} [Fintype I] [Nonempty I] [Field K]
variable {A : I → Type} [∀ i, Fintype (A i)]

theorem rankLE_iff_restrict_diag (T : (∀ i, A i) → K) (r : ℕ) :
    Lemmata.TensorRank.Tensor.RankLE T r ↔
      ofCoeffs T ≤ (r : TensorClass I K) := by
  classical
  rw [← ofRaw_diagonal_fin_eq_natCast I K r]
  change Lemmata.TensorRank.Tensor.RankLE T r ↔
    ofRaw (⟨A, inferInstance, T⟩ : Raw I K) ≤ ofRaw (Raw.diagonal I K (Fin r))
  rw [ofRaw_le_iff]
  have reduce (M : ∀ i, A i → Fin r → K) (x : ∀ i, A i) :
      (∑ a : I → Fin r, (Raw.diagonal I K (Fin r)).coeff a * ∏ i, M i (x i) (a i)) =
        ∑ j : Fin r, ∏ i, M i (x i) j := by
    simp_rw [Raw.diagonal, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single (fun _ => j)]
    · simp
    · intro a _ h
      simp [h]
    · simp
  change _ ↔ ∃ M : ∀ i, A i → Fin r → K, ∀ x : ∀ i, A i,
    T x = ∑ a : I → Fin r, (Raw.diagonal I K (Fin r)).coeff a * ∏ i, M i (x i) (a i)
  simp_rw [reduce]
  constructor
  · rintro ⟨c,v,h⟩
    let i₀ : I := Classical.choice inferInstance
    refine ⟨fun i x j => (if i = i₀ then c j else 1) * v j i x, fun x => ?_⟩
    rw [congrFun h x]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.prod_mul_distrib]
    simp [Lemmata.TensorRank.Tensor.pure]
  · rintro ⟨M,h⟩
    refine ⟨fun _ => 1, fun j i x => M i x j, ?_⟩
    funext x
    simpa [Lemmata.TensorRank.Tensor.pure] using h x

theorem ofCoeffs_power (T : (∀ i, A i) → K) (n : ℕ) :
    ofCoeffs (Lemmata.TensorRank.Tensor.power T n) = (ofCoeffs T)^n := by
  classical
  let Traw : Raw I K := ⟨A, inferInstance, T⟩
  let P (m : ℕ) : Raw I K :=
    ⟨fun i => Fin m → A i, inferInstance, Lemmata.TensorRank.Tensor.power T m⟩
  change ofRaw (P n) = (ofRaw Traw)^n
  induction n with
  | zero =>
    rw [pow_zero, ← ofRaw_one (I := I) (K := K)]
    apply ofRaw_eq_iff.mpr
    let e (i : I) : (Fin 0 → A i) ≃ PUnit :=
      ⟨fun _ => PUnit.unit, fun _ => Fin.elim0, fun x => funext fun j => Fin.elim0 j,
        fun p => by cases p; rfl⟩
    refine Raw.reindex_equivalent e fun x => ?_
    simp [P, Lemmata.TensorRank.Tensor.power, Raw.one]
  | succ n ih =>
    rw [pow_succ', ← ih, ← ofRaw_mul]
    apply ofRaw_eq_iff.mpr
    let e (i : I) : (Fin (n+1) → A i) ≃ A i × (Fin n → A i) :=
      (Fin.consEquiv (fun _ : Fin (n+1) => A i)).symm
    refine Raw.reindex_equivalent e fun x => ?_
    change (∏ j : Fin (n+1), T (fun i => x i j)) =
      T (fun i => (e i (x i)).1) *
      ∏ j : Fin n, T (fun i => (e i (x i)).2 j)
    rw [Fin.prod_univ_succ] <;> rfl

/-- Every normalized spectral point is bounded by the independently defined
    Lemmata asymptotic rank, without needing the converse spectral theorem. -/
theorem spectral_le_lemmata (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (T : (∀ i, A i) → K) :
    (φ.val (ofCoeffs T) : ℝ) ≤ Lemmata.TensorRank.Tensor.asymptoticRank T := by
  unfold Lemmata.TensorRank.Tensor.asymptoticRank
  apply le_ciInf
  intro n
  unfold Lemmata.TensorRank.Tensor.rankRoot
  let r := Lemmata.TensorRank.Tensor.rank (Lemmata.TensorRank.Tensor.power T (n+1))
  have hr : ofCoeffs (Lemmata.TensorRank.Tensor.power T (n+1)) ≤ (r : TensorClass I K) :=
    (rankLE_iff_restrict_diag _ _).1 (Lemmata.TensorRank.Tensor.rankLE_rank _)
  rw [ofCoeffs_power] at hr
  let f := normalizedSpectrum.toRingHom φ
  have h : f ((ofCoeffs T)^(n+1)) ≤ f (r : TensorClass I K) :=
    φ.property.2.2.2.2 _ _ hr
  rw [map_pow, map_natCast] at h
  have hreal : (f (ofCoeffs T) : ℝ) ^ (n+1) ≤ (r : ℝ) := by exact_mod_cast h
  change (f (ofCoeffs T) : ℝ) ≤ (r : ℝ) ^ ((n + 1 : ℝ)⁻¹)
  simpa only [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), Nat.cast_succ,
    mul_inv_cancel₀ (by positivity : (n+1:ℝ) ≠ 0), Real.rpow_one] using
    Real.rpow_le_rpow (pow_nonneg (NNReal.coe_nonneg _) _) hreal
      (by positivity : (0:ℝ) ≤ (n+1:ℝ)⁻¹)

#print axioms spectral_le_lemmata
#print axioms rankLE_iff_restrict_diag
#print axioms ofCoeffs_power
end GraphTensorVerification
