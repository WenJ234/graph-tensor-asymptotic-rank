import C5.OddCyclePairRows
import Mathlib.Data.ZMod.Basic

namespace C5GeneralCycles
open scoped BigOperators

/-- Translate a complete residue system by a fixed starting vertex. -/
theorem zmod_row_offsets (N : ℕ) [NeZero N] (f : ZMod N → ℝ) (i : ZMod N) :
    (∑ j, f j) = ∑ j ∈ Finset.range N, f (i+(j:ZMod N)) := by
  classical
  let e : ZMod N ≃ ZMod N := Equiv.addLeft i
  have ha : (∑ j : ZMod N, f (i+j)) = ∑ j : ZMod N, f j :=
    e.sum_comp f
  rw [← ha, ← (ZMod.finEquiv N).toEquiv.sum_comp (fun j => f (i+j))]
  calc
    _ = ∑ j : Fin N, f (i+(j.val:ZMod N)) := by
      apply Finset.sum_congr rfl
      intro j _
      have hh : (ZMod.finEquiv N).toEquiv j = (j.val : ZMod N) := by
        have hv : ((ZMod.finEquiv N).toEquiv j).val = j.val := by
          cases N with
          | zero => exact (NeZero.ne 0 rfl).elim
          | succ N => rfl
        simpa only [hv] using (ZMod.natCast_zmod_val ((ZMod.finEquiv N).toEquiv j)).symm
      rw [hh]
    _ = _ := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]

#print axioms zmod_row_offsets
end C5GeneralCycles
