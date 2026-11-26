import OddWheelCovariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import EvenWheelSDP

namespace WheelVerification
open scoped BigOperators
noncomputable section

def cutSign {I J : Type} (f : J → I → Bool) (h : J) (i : I) : ℝ :=
  if f h i then 1 else -1

theorem cutSign_mul {I J : Type} (f : J → I → Bool) (h : J) (i j : I) :
    cutSign f h i * cutSign f h j = 1-2*cutDistance (f h) i j := by
  cases hi : f h i <;> cases hj : f h j <;> norm_num [cutSign,cutDistance,hi,hj]

def oddWheelCandidate {I J : Type} [Fintype J] (f : J → I → Bool) (s a : ℝ) :
    Option I → Option I → ℝ
  | none, none => 0
  | none, some _ | some _, none => (1+s)/2
  | some i, some j => a/(Fintype.card J : ℝ) * ∑ h, cutDistance (f h) i j

theorem oddWheelCandidate_psd {I J : Type} [Fintype I] [Fintype J] [Nonempty J]
    (f : J → I → Bool) (m s a : ℝ) (ha : 0 ≤ a)
    (hm : ∀ i, (∑ h, cutSign f h i) = (Fintype.card J : ℝ)*m)
    (hscale : s^2+a*(1-m^2)=1) (u : Option I → ℝ) :
    0 ≤ ∑ i, ∑ j, u i*(1-2*oddWheelCandidate f s a i j)*u j := by
  have hcard : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have he (i j : Option I) : 1-2*oddWheelCandidate f s a i j =
      oddWheelGram (cutSign f) m s (a/(Fintype.card J : ℝ)) i j := by
    cases i with
    | none => cases j <;> simp [oddWheelCandidate,oddWheelGram] <;> ring
    | some i =>
      cases j with
      | none => simp [oddWheelCandidate,oddWheelGram]; ring
      | some j =>
        simp only [oddWheelCandidate,oddWheelGram,cutSign_mul,
          Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
          nsmul_eq_mul,mul_one]
        have hh : s^2+a-a*m^2=1 := by linarith only [hscale]
        field_simp [hcard.ne']
        linear_combination -(Fintype.card J : ℝ)*hh
  simp_rw [he]
  exact oddWheelGram_psd (cutSign f) m s _ (div_nonneg ha hcard.le) hm u

#print axioms oddWheelCandidate_psd
end
end WheelVerification
