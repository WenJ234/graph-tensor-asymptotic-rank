import OAI.LinearAlgebra.SpectralBooks.ExactExponent

/-! The rectangular specialization for the odd-complete-graph partition. -/
namespace OddCliquePaper
open OAI.LinearAlgebra.SpectralBooks

theorem odd_clique_rectangle_value (K : Type) [Field K] (m : ℝ) (hm : 1 ≤ m) :
    formalOmega K (m ^ 2) m m = (2*m+1)^2/4 := by
  have hpos : 0 < m := by linarith
  have hn : 0 ≤ m := hpos.le
  have hs : 0 ≤ m ^ 2 := sq_nonneg _
  have horder : m ≤ m ^ 2 := by
    nlinarith only [mul_nonneg hn (sub_nonneg.mpr hm)]
  rw [rectangular_exponent]
  dsimp only
  rw [max_eq_left hs, max_eq_left hn, min_self, max_self, max_eq_left horder,
    min_eq_right horder]
  have he : m ^ 2 + m + m - m ^ 2 - m = m := by ring
  rw [he]
  have hr : (m ^ 2 + m) * m - m ^ 2 * m = m^2 := by ring
  rw [hr, max_eq_left hs]
  field_simp [hpos.ne']
  <;> ring

#print axioms odd_clique_rectangle_value
end OddCliquePaper
