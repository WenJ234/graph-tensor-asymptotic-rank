import WheelGram

namespace WheelVerification
open scoped BigOperators
noncomputable section

/-- Centering a family at its common mean subtracts the constant Gram term. -/
theorem centered_gram_sum {I J : Type} [Fintype J]
    (v : J → I → ℝ) (m : ℝ)
    (hv : ∀ i, (∑ h, v h i) = (Fintype.card J : ℝ) * m) (i j : I) :
    (∑ h, (v h i - m)*(v h j - m)) =
      (∑ h, v h i*v h j) - (Fintype.card J : ℝ)*m^2 := by
  have he (h : J) : (v h i-m)*(v h j-m) =
      v h i*v h j-v h i*m-m*v h j+m^2 := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hv]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

def oddHubVector {I : Type} (s : ℝ) : Option I → ℝ
  | none => 1
  | some _ => -s

def oddRimCentered {I J : Type} (v : J → I → ℝ) (m : ℝ) (h : J) :
    Option I → ℝ
  | none => 0
  | some i => v h i-m

def oddWheelGram {I J : Type} [Fintype J] (v : J → I → ℝ) (m s c : ℝ) :
    Option I → Option I → ℝ
  | none, none => 1
  | none, some _ | some _, none => -s
  | some i, some j => s^2+c*((∑ h, v h i*v h j) - (Fintype.card J : ℝ)*m^2)

theorem oddWheelGram_psd {I J : Type} [Fintype I] [Fintype J]
    (v : J → I → ℝ) (m s c : ℝ) (hc : 0 ≤ c)
    (hv : ∀ i, (∑ h, v h i) = (Fintype.card J : ℝ) * m) (u : Option I → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * oddWheelGram v m s c i j * u j := by
  have he (i j : Option I) : oddWheelGram v m s c i j =
      oddHubVector s i*oddHubVector s j+
        c*(∑ h, oddRimCentered v m h i*oddRimCentered v m h j) := by
    cases i <;> cases j <;> simp [oddWheelGram,oddHubVector,oddRimCentered,
      centered_gram_sum v m hv, pow_two]
  simp_rw [he]
  exact psd_of_rank_one_family (oddHubVector s) (oddRimCentered v m) c hc u

#print axioms centered_gram_sum
#print axioms oddWheelGram_psd
end
end WheelVerification
