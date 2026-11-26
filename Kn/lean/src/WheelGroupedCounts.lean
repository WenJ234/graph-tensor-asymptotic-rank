import WheelGroup
import Mathlib.Data.Fintype.BigOperators

namespace WheelVerification
open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

def triangleWires (K : Type) [Field K] (a b c : ℕ) : TensorClass.{0} (Fin 3) K :=
  wireAt K 0 1 ^ a * (wireAt K 2 0 ^ b * wireAt K 2 1 ^ c)

private theorem sum_zmod_val (f : ℕ → ℕ) (r : ℕ) [NeZero r] :
    (∑ v : ZMod r, f v.val) = ∑ i ∈ Finset.range r, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv (ZMod.finEquiv r).symm.toEquiv _ _ ?_
  intro v
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem grouped_wheel_eq_triangle (K : Type) [Field K] (r : ℕ) [NeZero r] :
    groupClass (wheelGroup r) (wheelTensor K r) =
      triangleWires K (crossRim r) (spokeClass r 0) (spokeClass r 1) := by
  change groupMulHom (wheelGroup r) (rimTensor K r * spokeTensor K r) = _
  rw [map_mul, rimTensor, spokeTensor, map_prod, map_prod]
  simp_rw [show ∀ a b, groupMulHom (wheelGroup r) (wireAt K a b) =
    wireAt K (wheelGroup r a) (wheelGroup r b) from group_wireAt (wheelGroup r)]
  let cr (v : ZMod r) : ℕ := if v.val%2 ≠ rimNext' r v.val%2 then 1 else 0
  let z (v : ZMod r) : ℕ := if v.val%2 = 0 then 1 else 0
  let o (v : ZMod r) : ℕ := if v.val%2 = 1 then 1 else 0
  have hrim (v : ZMod r) : wireAt K (wheelGroup r (some v))
      (wheelGroup r (some (v+1))) = wireAt K (0 : Fin 3) 1 ^ cr v := by
    unfold wheelGroup rimGroup cr
    rw [← rim_val_next]
    have a : v.val%2 = 0 ∨ v.val%2 = 1 := by omega
    have b : (v+1).val%2 = 0 ∨ (v+1).val%2 = 1 := by omega
    rcases a with a | a <;> rcases b with b | b
    · simp [a,b,wireAt_self]
    · simp [a,b]
    · simp [a,b,wireAt_symm (K := K) (1 : Fin 3) 0]
    · simp [a,b,wireAt_self]
  have hs (v : ZMod r) : wireAt K (wheelGroup r none) (wheelGroup r (some v)) =
      wireAt K (2 : Fin 3) 0 ^ z v * wireAt K (2 : Fin 3) 1 ^ o v := by
    have h : v.val%2 = 0 ∨ v.val%2 = 1 := by omega
    rcases h with a|a <;> simp [wheelGroup,rimGroup,z,o,a]
  simp_rw [hrim,hs,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have hc : (∑ v : ZMod r, cr v) = crossRim r :=
    sum_zmod_val (fun i => if i%2 ≠ rimNext' r i%2 then 1 else 0) r
  have h0 : (∑ v : ZMod r, z v) = spokeClass r 0 := sum_zmod_val (fun i => if i%2 = 0 then 1 else 0) r
  have h1 : (∑ v : ZMod r, o v) = spokeClass r 1 := sum_zmod_val (fun i => if i%2 = 1 then 1 else 0) r
  rw [hc,h0,h1]
  rfl

theorem grouped_even_wheel_eq_triangle (K : Type) [Field K] (k : ℕ) [NeZero (2*k)] :
    groupClass (wheelGroup (2*k)) (wheelTensor K (2*k)) = triangleWires K (2*k) k k := by
  rw [grouped_wheel_eq_triangle,crossRim_even,spokeClass_even k 0 (by omega),
    spokeClass_even k 1 (by omega)]

theorem grouped_odd_wheel_eq_triangle (K : Type) [Field K] (k : ℕ) :
    groupClass (wheelGroup (2*k+1)) (wheelTensor K (2*k+1)) = triangleWires K (2*k) (k+1) k := by
  rw [grouped_wheel_eq_triangle,crossRim_odd,spokeClass_odd_zero,spokeClass_odd_one]

#print axioms grouped_even_wheel_eq_triangle
#print axioms grouped_odd_wheel_eq_triangle
end
end WheelVerification
