import WheelGroupedCounts

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

def between (i j u v : Fin 3) : ℕ :=
  if (u = i ∧ v = j) ∨ (u = j ∧ v = i) then 1 else 0

def wheelBetween {r : ℕ} [NeZero r] (σ : Option (ZMod r) → Fin 3) (i j : Fin 3) : ℕ :=
  (∑ v : ZMod r, between i j (σ (some v)) (σ (some (v+1)))) +
  (∑ v : ZMod r, between i j (σ none) (σ (some v)))

private theorem wire_decomposition (K : Type) [Field K] (u v : Fin 3) :
    wireAt K u v = triangleWires K (between 0 1 u v) (between 2 0 u v) (between 2 1 u v) := by
  fin_cases u <;> fin_cases v <;>
    simp [between,triangleWires,wireAt_self,wireAt_symm (K := K) (1 : Fin 3) 0,
      wireAt_symm (K := K) (0 : Fin 3) 2, wireAt_symm (K := K) (1 : Fin 3) 2]

private theorem prod_triangleWires {A : Type} [Fintype A] (K : Type) [Field K]
    (a b c : A → ℕ) :
    (∏ v, triangleWires K (a v) (b v) (c v)) =
      triangleWires K (∑ v, a v) (∑ v, b v) (∑ v, c v) := by
  simp_rw [triangleWires,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem grouped_wheel_arbitrary (K : Type) [Field K] (r : ℕ) [NeZero r]
    (σ : Option (ZMod r) → Fin 3) :
    groupClass σ (wheelTensor K r) =
      triangleWires K (wheelBetween σ 0 1) (wheelBetween σ 2 0) (wheelBetween σ 2 1) := by
  change groupMulHom σ (rimTensor K r * spokeTensor K r) = _
  rw [map_mul]
  unfold rimTensor spokeTensor
  simp only [map_prod]
  simp_rw [show ∀ a b, groupMulHom σ (wireAt K a b) = wireAt K (σ a) (σ b) from group_wireAt σ,
    wire_decomposition, prod_triangleWires]
  simp only [wheelBetween,triangleWires,pow_add]
  ac_rfl

#print axioms grouped_wheel_arbitrary
end
end WheelVerification
