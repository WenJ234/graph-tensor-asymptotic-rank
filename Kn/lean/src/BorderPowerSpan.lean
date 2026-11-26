import Lemmata.TensorRank.Proof.Products
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! A coordinate model of Zariski closure and a polynomial-size span of tensor powers. -/
namespace OddCliquePaper
open Lemmata.TensorRank Lemmata.TensorRank.Tensor
open scoped BigOperators
noncomputable section

/-- Set-theoretic Zariski closure on affine points, via all polynomial equations. -/
def InAffineZariskiClosure {F A : Type*} [Field F] (S : Set (A → F)) (x : A → F) : Prop :=
  ∀ p : MvPolynomial A F, (∀ y ∈ S, MvPolynomial.eval y p = 0) → MvPolynomial.eval x p = 0

theorem eval_mem_span_of_zariski {F A B : Type*} [Field F] [Fintype B]
    (p : B → MvPolynomial A F) (S : Set (A → F)) {x : A → F}
    (hx : InAffineZariskiClosure S x) :
    (fun b => MvPolynomial.eval x (p b)) ∈
      Submodule.span F ((fun y b => MvPolynomial.eval y (p b)) '' S) := by
  classical
  let V := Submodule.span F ((fun y b => MvPolynomial.eval y (p b)) '' S)
  change _ ∈ V
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := V),
    Submodule.mem_dualCoannihilator]
  intro φ hφ
  let f : MvPolynomial A F :=
    ∑ b : B, MvPolynomial.C (φ (Pi.single b 1)) * p b
  have eval_f (y : A → F) : MvPolynomial.eval y f = φ (fun b => MvPolynomial.eval y (p b)) := by
    have hdecomp : ∑ b : B, MvPolynomial.eval y (p b) • Pi.single b (1 : F) =
        (fun b => MvPolynomial.eval y (p b)) := by
      ext b
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [← hdecomp]
    simp only [f, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      map_sum, LinearMap.map_smul, smul_eq_mul, mul_comm]
  rw [← eval_f]
  apply hx f
  intro y hy
  rw [eval_f]
  exact (Submodule.mem_dualAnnihilator _).mp hφ _
    (Submodule.subset_span (Set.mem_image_of_mem _ hy))

variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I] {V : I → Type*} [∀ i, Fintype (V i)]

private def expIndex (t : ℕ) (x : ∀ i, Fin t → V i) (a : ∀ i, V i) : Fin (t+1) := by
  classical
  let s : Finset (Fin t) := Finset.univ.filter (fun j => (fun i => x i j) = a)
  have hs : s.card ≤ t := by
    simpa [s] using (Finset.card_filter_le (Finset.univ : Finset (Fin t)) (fun j => (fun i => x i j) = a))
  exact ⟨s.card, Nat.lt_succ_of_le hs⟩

private def expPolynomial (t : ℕ) (e : (∀ i, V i) → Fin (t+1)) :
    MvPolynomial (∀ i, V i) F :=
  ∏ a, MvPolynomial.X a ^ (e a).val

private def expReadout (t : ℕ) :
    ((((∀ i, V i) → Fin (t+1)) → F)) →ₗ[F] Tensor F I (fun i => Fin t → V i) where
  toFun c := fun x => c (expIndex t x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem power_eq_expReadout (t : ℕ) (T : Tensor F I V) :
    power T t = expReadout t (fun e => MvPolynomial.eval T (expPolynomial t e)) := by
  classical
  funext x
  change (∏ j : Fin t, T (fun i => x i j)) = MvPolynomial.eval T (expPolynomial t (expIndex t x))
  rw [expPolynomial, MvPolynomial.eval_prod]
  simp only [MvPolynomial.eval_pow, MvPolynomial.eval_X, expIndex]
  rw [← Finset.prod_fiberwise' (s := Finset.univ) (g := fun j : Fin t => (fun i => x i j)) T]
  simp only [Finset.prod_const]

private theorem rank_smul_le {W : I → Type*} [∀ i, Fintype (W i)]
    (a : F) (Y : Tensor F I W) : rank (a • Y) ≤ rank Y := by
  obtain ⟨c, v, h⟩ := rankLE_rank Y
  apply (rank_le_iff _ _).mpr
  refine ⟨(fun j => a*c j), v, ?_⟩
  funext x
  change a * Y x = _
  rw [congrFun h x, Finset.mul_sum]
  simp_rw [mul_assoc]

private theorem rank_sum_le {B : Type*} {W : I → Type*} [∀ i, Fintype (W i)]
    (s : Finset B) (Y : B → Tensor F I W) :
    rank (∑ b ∈ s, Y b) ≤ ∑ b ∈ s, rank (Y b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem rank_power_le_of_zariski (t r : ℕ) (T : Tensor F I V)
    (h : InAffineZariskiClosure {X : Tensor F I V | rank X ≤ r} T) :
    rank (power T t) ≤ (t+1)^Fintype.card (∀ i, V i) * r^t := by
  classical
  let M := (∀ i, V i) → Fin (t+1)
  let vec (X : Tensor F I V) : M → F := fun e => MvPolynomial.eval X (expPolynomial t e)
  let S : Set (M → F) := vec '' {X : Tensor F I V | rank X ≤ r}
  have hv : vec T ∈ Submodule.span F S :=
    eval_mem_span_of_zariski (expPolynomial (F := F) (V := V) t) _ h
  obtain ⟨c, hc, hs, hsum⟩ := Submodule.mem_span_set_iff_exists_finsupp_le_finrank.mp hv
  let L := expReadout (F := F) (V := V) t
  have hp : power T t = ∑ y ∈ c.support, c y • L y := by
    rw [power_eq_expReadout]
    change L (vec T) = _
    rw [← hsum]
    simp only [Finsupp.sum, map_sum, map_smul]
  rw [hp]
  have hb : ∀ y ∈ c.support, rank (c y • L y) ≤ r^t := by
    intro y hy
    obtain ⟨X, hX, rfl⟩ := hs hy
    have hLX : L (vec X) = power X t := (power_eq_expReadout t X).symm
    rw [hLX]
    exact (rank_smul_le _ _).trans ((rank_power_le _ _).trans (Nat.pow_le_pow_left hX _))
  have hc' : c.support.card ≤ (t+1)^Fintype.card (∀ i, V i) := by
    have hsub := Submodule.finrank_le (Submodule.span F S)
    exact hc.trans (by simpa [M, Module.finrank_pi] using hsub)
  exact (rank_sum_le _ _).trans <| (Finset.sum_le_sum hb).trans (by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ hc')

#print axioms eval_mem_span_of_zariski
#print axioms rank_power_le_of_zariski
end
end OddCliquePaper
