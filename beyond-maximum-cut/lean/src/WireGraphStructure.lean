import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose
import OAI.LinearAlgebra.SpectralBooks.StrassenRank
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! Bridge from a finite edge multilist to the upstream graph-tensor rank model.
Edge multiplicities are deliberate (used after vertex grouping). -/
namespace WenJ.GraphTensor.MaxCut
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped NNReal
noncomputable section

variable {A B K : Type} [Fintype A] [Fintype B] [Field K]

def binaryWireRaw (i j : A) : Raw.{0} A K :=
  (Raw.diagonal (Fin 2) K (Fin 2)).group ![i,j]

def wireClass (i j : A) : TensorClass.{0} A K := ofRaw (binaryWireRaw i j)

def graphClass (edges : List (A × A)) : TensorClass.{0} A K :=
  (edges.map fun e => wireClass e.1 e.2).prod

theorem binaryWireRaw_ne_zero (i j : A) :
    (binaryWireRaw (K := K) i j).coeff ≠ 0 := by
  unfold binaryWireRaw
  apply ((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff _).mpr
  intro hz
  have h := congrFun hz (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at h
  simp [Raw.diagonal, funext_iff] at h

theorem group_wireClass (f : A → B) (i j : A) :
    groupClass f (wireClass (K := K) i j) = wireClass (f i) (f j) := by
  unfold wireClass binaryWireRaw
  rw [groupClass_ofRaw]
  have hf : (f ∘ (![i,j] : Fin 2 → A)) = (![f i, f j] : Fin 2 → B) := by
    funext k
    fin_cases k <;> rfl
  rw [← hf]
  exact ofRaw_eq_iff.mpr (Raw.group_group_equivalent _ _ _)

theorem group_graphClass [Nonempty A] [Nonempty B] (f : A → B)
    (edges : List (A × A)) :
    groupClass f (graphClass (K := K) edges) =
      graphClass (edges.map fun e => (f e.1, f e.2)) := by
  induction edges with
  | nil => exact (groupMulHom f).map_one
  | cons e es ih =>
    change groupMulHom f (wireClass (K := K) e.1 e.2 * graphClass es) = _
    rw [map_mul]
    change groupClass f (wireClass (K := K) e.1 e.2) * groupClass f (graphClass es) = _
    rw [group_wireClass,ih]
    rfl

theorem wireClass_ne_zero (i j : A) : wireClass (K := K) i j ≠ 0 :=
  fun hz => binaryWireRaw_ne_zero i j ((ofRaw_eq_zero_iff _).mp hz)

theorem graphClass_ne_zero [Nonempty A] (edges : List (A × A)) :
    graphClass (K := K) edges ≠ 0 := by
  induction edges with
  | nil => exact one_ne_zero
  | cons e es ih => exact mul_ne_zero (wireClass_ne_zero e.1 e.2) ih

theorem spectral_graph_log_price [Nonempty A]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} A K → _ → Prop))
    (edges : List (A × A)) :
    Real.logb 2 (φ.val (graphClass edges) : ℝ) =
      (edges.map fun e => rawWireDistance φ 1 e.1 e.2).sum := by
  induction edges with
  | nil => simp [graphClass,φ.property.2.1]
  | cons e es ih =>
    have h1 : (φ.val (wireClass e.1 e.2) : ℝ) ≠ 0 := by
      exact_mod_cast (spectral_value_pos φ (wireClass_ne_zero e.1 e.2)).ne'
    have h2 : (φ.val (graphClass es) : ℝ) ≠ 0 := by
      exact_mod_cast (spectral_value_pos φ (graphClass_ne_zero es)).ne'
    change Real.logb 2 (φ.val (wireClass e.1 e.2 * graphClass es) : ℝ) = _
    rw [φ.property.2.2.2.1, NNReal.coe_mul, Real.logb_mul h1 h2, ih]
    simp [rawWireDistance, rawLogPrice, wireClass, binaryWireRaw]

theorem group_rank_le [Nonempty A] [Nonempty B] (f : A → B)
    (hf : Function.Surjective f) (T : TensorClass.{0} A K) :
    rank (groupClass f T) ≤ rank T := by
  apply rank_le_of_le
  have h := groupClass_mono f (le_rank T)
  have he : groupClass f (rank T : TensorClass.{0} A K) =
      (rank T : TensorClass.{0} B K) := map_natCast (groupRingHom f hf) _
  simpa only [he] using h

theorem group_asymptoticRank_le [Nonempty A] [Nonempty B] (f : A → B)
    (hf : Function.Surjective f) (T : TensorClass.{0} A K) :
    asymptoticRank (groupClass f T) ≤ asymptoticRank T := by
  unfold SiteTensor.asymptoticRank
  apply le_ciInf
  intro n
  have hb (k : ℕ) : 0 ≤ (rank ((groupClass f T) ^ (k+1)) : ℝ) ^ ((k+1 : ℝ)⁻¹) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply (ciInf_le ⟨0, by rintro _ ⟨k,rfl⟩; exact hb k⟩ n).trans
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast (show rank ((groupClass f T) ^ (n+1)) ≤ rank (T ^ (n+1)) from by
      have he : groupClass f (T ^ (n+1)) = (groupClass f T) ^ (n+1) :=
        map_pow (groupRingHom f hf) _ _
      rw [←he]
      exact group_rank_le f hf _)
  · positivity

end
end WenJ.GraphTensor.MaxCut
#print axioms WenJ.GraphTensor.MaxCut.spectral_graph_log_price
#print axioms WenJ.GraphTensor.MaxCut.group_asymptoticRank_le
