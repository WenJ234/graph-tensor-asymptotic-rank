import WheelGram

namespace WheelVerification
open scoped BigOperators

noncomputable def cutDistance {I : Type} (f : I → Bool) (x y : I) : ℝ :=
  if f x = f y then 0 else 1

theorem cutDistance_triangle {I : Type} (f : I → Bool) (x y z : I) :
    cutDistance f x z ≤ cutDistance f x y + cutDistance f y z := by
  unfold cutDistance
  cases f x <;> cases f y <;> cases f z <;> norm_num

noncomputable def evenWheelCandidate {I : Type} (f : I → Bool) :
    Option I → Option I → ℝ
  | none, none => 0
  | some x, some y => 15/16 * cutDistance f x y
  | _, _ => 5/8

private noncomputable def evenZ {I : Type} : Option I → ℝ
  | none => 1
  | some _ => -1/4

private noncomputable def evenV {I : Type} (f : I → Bool) : Option I → ℝ
  | none => 0
  | some x => if f x then 1 else -1

theorem evenWheelCandidate_psd {I : Type} [Fintype I] (f : I → Bool) (u : Option I → ℝ) :
    0 ≤ ∑ i, ∑ j, u i*(1-2*evenWheelCandidate f i j)*u j := by
  have h (i j : Option I) : 1-2*evenWheelCandidate f i j =
      evenZ i * evenZ j + (15/16)*(∑ _ : Unit, evenV f i * evenV f j) := by
    cases i with
    | none => cases j <;> norm_num [evenWheelCandidate,evenZ,evenV]
    | some x =>
      cases j with
      | none => norm_num [evenWheelCandidate,evenZ,evenV]
      | some y =>
        cases hx : f x <;> cases hy : f y <;> norm_num [evenWheelCandidate,evenZ,evenV,cutDistance,hx,hy]
  simp_rw [h]
  exact psd_of_rank_one_family evenZ (fun _ : Unit => evenV f) (15/16) (by norm_num) u

theorem evenWheelCandidate_triangle {I : Type} (f : I → Bool) (x y z : Option I) :
    evenWheelCandidate f x z ≤ evenWheelCandidate f x y + evenWheelCandidate f y z := by
  have h (a b : I) : 0 ≤ cutDistance f a b ∧ cutDistance f a b ≤ 1 := by
    unfold cutDistance
    split <;> norm_num
  cases x <;> cases y <;> cases z <;> simp only [evenWheelCandidate]
  all_goals try norm_num
  all_goals try (apply add_le_add; positivity)
  all_goals try (rename_i a b; linarith [(h a b).1, (h a b).2])
  rename_i a b c
  simpa only [mul_add] using
    mul_le_mul_of_nonneg_left (cutDistance_triangle f a b c) (by norm_num : (0:ℝ) ≤ 15/16)

#print axioms evenWheelCandidate_psd
#print axioms evenWheelCandidate_triangle
end WheelVerification
