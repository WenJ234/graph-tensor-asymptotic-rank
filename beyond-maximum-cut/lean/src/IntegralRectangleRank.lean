import OAI.LinearAlgebra.SpectralBooks.ExactExponent
import OAI.LinearAlgebra.MatrixExponent.Integral.UpperBound

/-! Finite lower bound from the pinned division-free exponent, for every
    natural triple of wire widths (cyclic orientation a,b,c). -/
namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

private theorem rankLE_matrix (F : Type*) [Field F] (a b c : ℕ) :
    OAI.LinearAlgebra.MatrixExponent.Rectangle.RankLE F c b a
      (tensorRank (matrixTensor F a b c)) := by
  classical
  obtain ⟨x,y,z,h⟩ := rankAtMost_tensorRank (matrixTensor F a b c)
  refine ⟨x,y,fun l u => z l (u.2,u.1),?_⟩
  intro u v w
  have hh := congrFun (congrFun (congrFun h u) v) (w.2,w.1)
  simpa only [Tensor.rankOne, Tensor.matrixCoefficients, eq_comm, and_comm, and_left_comm,
    and_assoc] using hh.symm

private theorem side_int (n a : ℕ) :
    OAI.LinearAlgebra.MatrixExponent.Rectangle.side n a = n^a := by
  unfold OAI.LinearAlgebra.MatrixExponent.Rectangle.side
  rw [Real.rpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast]

theorem integral_rectangular_rank_lower (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n)
    (a b c : ℕ) :
    (n : ℝ) ^ formalOmega F a b c ≤ tensorRank (matrixTensor F (n^a) (n^b) (n^c)) := by
  apply le_of_not_gt
  intro hh
  let s := OAI.LinearAlgebra.MatrixExponent.Rectangle.side n
  let r := tensorRank (matrixTensor F (n^a) (n^b) (n^c))
  have hr : OAI.LinearAlgebra.MatrixExponent.Rectangle.RankLE F (s c) (s b) (s a) r := by
    simpa only [s,side_int] using rankLE_matrix F (n^a) (n^b) (n^c)
  have hu := OAI.LinearAlgebra.MatrixExponent.Rectangle.exponent_lt_of_rank
    (a := (c : ℝ)) (b := (b : ℝ)) (c := (a : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn hr hh
  have he : OAI.LinearAlgebra.MatrixExponent.Rectangle.exponent F c b a = formalOmega F a b c := by
    rw [← OAI.LinearAlgebra.MatrixExponent.Integral.agreement F
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ← formalOmega_eq_integral F a b c]
  rw [he] at hu
  exact (lt_irrefl _ hu)

#print axioms integral_rectangular_rank_lower
end WheelVerification
