import OddCliquePairCount

namespace OddCliquePaper
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open GraphTensorVerification WheelVerification
noncomputable section

def balancedColor (m : ℕ) (v : Fin (2*m+1)) : Fin 3 :=
  if v.val < m then 0 else if v.val < 2*m then 1 else 2

theorem balancedColor_surjective {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (balancedColor m) := by
  intro i
  fin_cases i
  · exact ⟨⟨0,by omega⟩, if_pos (by change 0 < m; omega)⟩
  · refine ⟨⟨m,by omega⟩,?_⟩
    simp [balancedColor,show m < 2*m by omega]
  · exact ⟨⟨2*m,by omega⟩,by simp [balancedColor,show ¬ 2*m < m by omega]⟩

private theorem color0_iff (m : ℕ) (v : Fin (2*m+1)) :
    balancedColor m v = 0 ↔ v.val < m := by
  unfold balancedColor
  split <;> rename_i h
  · simp [h]
  · by_cases g : v.val < 2*m <;> simp [g,h]

private theorem color1_iff (m : ℕ) (v : Fin (2*m+1)) :
    balancedColor m v = 1 ↔ m ≤ v.val ∧ v.val < 2*m := by
  unfold balancedColor
  by_cases h : v.val < m
  · simp [h,show ¬m ≤ v.val by omega]
  · simp [h,show m ≤ v.val by omega]

private theorem color2_iff (m : ℕ) (v : Fin (2*m+1)) :
    balancedColor m v = 2 ↔ v.val = 2*m := by
  have hv := v.isLt
  unfold balancedColor
  split <;> rename_i h
  · simp [show v.val ≠ 2*m by omega]
  · split <;> rename_i g
    · simp [show v.val ≠ 2*m by omega]
    · simp [show v.val = 2*m by omega]

theorem balanced_color0_card (m : ℕ) :
    Fintype.card (ColorClass (balancedColor m) 0) = m := by
  let e : ColorClass (balancedColor m) 0 ≃ Fin m := {
    toFun := fun v => ⟨v.val.val,(color0_iff m v.val).mp v.property⟩
    invFun := fun v => ⟨⟨v.val,by have := v.isLt; omega⟩,(color0_iff _ _).mpr v.isLt⟩
    left_inv := fun v => Subtype.ext (Fin.ext rfl)
    right_inv := fun v => Fin.ext rfl }
  simpa using Fintype.card_congr e

theorem balanced_color1_card (m : ℕ) :
    Fintype.card (ColorClass (balancedColor m) 1) = m := by
  let e : ColorClass (balancedColor m) 1 ≃ Fin m := {
    toFun := fun v => ⟨v.val.val-m,by have := (color1_iff m v.val).mp v.property; omega⟩
    invFun := fun v => ⟨⟨m+v.val,by have := v.isLt; omega⟩,
      (color1_iff _ _).mpr (by have := v.isLt; change m ≤ m+v.val ∧ m+v.val < 2*m; omega)⟩
    left_inv := fun v => Subtype.ext (Fin.ext (by
      have hh := (color1_iff m v.val).mp v.property
      change m + (v.val.val - m) = v.val.val
      omega))
    right_inv := fun v => Fin.ext (by change m+v.val-m=v.val; omega) }
  simpa using Fintype.card_congr e

theorem balanced_color2_card (m : ℕ) :
    Fintype.card (ColorClass (balancedColor m) 2) = 1 := by
  let e : ColorClass (balancedColor m) 2 ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨⟨2*m,by omega⟩,(color2_iff _ _).mpr rfl⟩
    left_inv := fun v => Subtype.ext (Fin.ext ((color2_iff m v.val).mp v.property).symm)
    right_inv := by intro u; cases u; rfl }
  simpa using Fintype.card_congr e

theorem grouped_balanced_clique (K : Type) [Field K] (m : ℕ) :
    groupClass (balancedColor m)
      (ofCoeffs (Lemmata.TensorRank.completeGraph (𝕜 := K) (2*m+1) 2)) =
      triangleWires K (m^2) m m := by
  rw [grouped_clique_eq_triangle,
    pairCount_eq_product _ 0 1 (by decide),
    pairCount_eq_product _ 2 0 (by decide),
    pairCount_eq_product _ 2 1 (by decide),
    balanced_color0_card, balanced_color1_card, balanced_color2_card]
  simp [pow_two]

#print axioms grouped_balanced_clique
#print axioms balancedColor_surjective
end
end OddCliquePaper
