import OddCliqueGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OddCliquePaper
open GraphTensorVerification
noncomputable section

abbrev ColorClass {n : ℕ} (c : Fin n → Fin 3) (i : Fin 3) := {v : Fin n // c v = i}

theorem pairCount_eq_product {n : ℕ} (c : Fin n → Fin 3) (i j : Fin 3) (hij : i ≠ j) :
    pairCount c i j = Fintype.card (ColorClass c i) * Fintype.card (ColorClass c j) := by
  classical
  let P (e : SortedEdge n) := (c e.val.1 = i ∧ c e.val.2 = j) ∨
    (c e.val.1 = j ∧ c e.val.2 = i)
  let E := {e : SortedEdge n // P e}
  let toEdge (xy : ColorClass c i × ColorClass c j) : E := by
    rcases xy with ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have hn : x ≠ y := fun h => hij (hx.symm.trans (congrArg c h |>.trans hy))
    exact if h : x < y then ⟨⟨(x,y),h⟩,Or.inl ⟨hx,hy⟩⟩
      else ⟨⟨(y,x),lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hn)⟩,Or.inr ⟨hy,hx⟩⟩
  let fromEdge (e : E) : ColorClass c i × ColorClass c j :=
    if h : c e.val.val.1 = i then
      (⟨e.val.val.1,h⟩,⟨e.val.val.2,by
        rcases e.property with hh | hh
        · exact hh.2
        · exact (hij (h.symm.trans hh.1)).elim⟩)
    else
      (⟨e.val.val.2,by
        rcases e.property with hh | hh
        · exact (h hh.1).elim
        · exact hh.2⟩,⟨e.val.val.1,by
        rcases e.property with hh | hh
        · exact (h hh.1).elim
        · exact hh.1⟩)
  let eqv : (ColorClass c i × ColorClass c j) ≃ E := {
    toFun := toEdge
    invFun := fromEdge
    left_inv := by
      rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
      by_cases h : x < y
      · simp [toEdge,fromEdge,h,hx]
      · have hyi : c y ≠ i := fun hc => hij (hc.symm.trans hy)
        simp [toEdge,fromEdge,h,hyi]
    right_inv := by
      rintro ⟨⟨⟨x,y⟩,hxy⟩,hp⟩
      have hn : ¬ y < x := not_lt_of_ge hxy.le
      by_cases hx : c x = i
      · simp [toEdge,fromEdge,hx,hxy]
      · simp [toEdge,fromEdge,hx,hn] }
  rw [← Fintype.card_prod, Fintype.card_congr eqv]
  change (∑ e : SortedEdge n, if P e then 1 else 0) = Fintype.card E
  rw [Finset.sum_boole]
  exact (Fintype.card_of_subtype (Finset.univ.filter P) (fun x => by simp)).symm

#print axioms pairCount_eq_product
end
end OddCliquePaper
