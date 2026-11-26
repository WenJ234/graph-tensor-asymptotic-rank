import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
namespace GraphTensorVerification
open Filter
open scoped Topology BigOperators
variable {I : Type} [Fintype I]

private def quad (M:I→I→ℝ) (w:I→ℝ) : ℝ :=
 ∑ i,∑ j,w i*M i j*w j
private theorem quad_scale (M:I→I→ℝ) (w:I→ℝ) (a:ℝ) :
 quad M (fun i=>a*w i)=a^2*quad M w := by
  unfold quad
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  refine Finset.sum_congr rfl fun j _=>?_
  ring

private theorem rat_scale (q:I→ℚ) (h:∀ i,0≤q i) :
 ∃ (D:ℕ) (a:I→ℕ), 0<D ∧ ∀ i, (a i:ℝ)=(D:ℝ)*(q i:ℝ) := by
  classical
  let D:ℕ := ∏ i,(q i).den
  let W (i:I):ℕ := (q i).num.toNat * ∏ j ∈ Finset.univ.erase i, (q j).den
  have hp : 0<D := Finset.prod_pos fun i _=>Rat.den_pos _
  refine ⟨D,W,hp,fun i=>?_⟩
  have hn : 0≤(q i).num := Rat.num_nonneg.mpr (h i)
  have hn' : ((q i).num.toNat:ℝ)=((q i).num:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have hD : (D:ℝ)=((q i).den:ℝ)*(((∏ j ∈ Finset.univ.erase i,(q j).den):ℕ):ℝ) := by
    exact_mod_cast (Finset.mul_prod_erase Finset.univ (fun j=>(q j).den) (Finset.mem_univ i)).symm
  dsimp only [W]
  rw [Nat.cast_mul,hn',hD,Rat.cast_def]
  field_simp [show ((q i).den:ℝ) ≠ 0 by exact_mod_cast (Rat.den_pos (q i)).ne'] <;> ring

private theorem quad_rat (M:I→I→ℝ) (h:∀ a:I→ℕ, (∀ i, 0<a i) → 0≤quad M (fun i=>a i))
 (q:I→ℚ) (hq:∀ i,0<q i) : 0≤quad M (fun i=>(q i:ℝ)) := by
  obtain ⟨D,a,hD,ha⟩ := rat_scale q (fun i=>(hq i).le)
  have hpos (i:I) : 0 < a i := by
    have H : (0:ℝ) < a i := by
      rw [ha i]
      exact mul_pos (by exact_mod_cast hD) (by exact_mod_cast hq i)
    exact_mod_cast H
  have p := h a hpos
  have e : (fun i=>(a i:ℝ)) = fun i=>(D:ℝ)*(q i:ℝ) := funext ha
  rw [e,quad_scale] at p
  exact (mul_nonneg_iff_of_pos_left (show (0:ℝ)<(D:ℝ)^2 by positivity)).mp p

theorem copositive_of_pos_nat (M:I→I→ℝ)
 (h:∀ a:I→ℕ,(∀ i,0<a i) → 0≤∑ i,∑ j,(a i:ℝ)*M i j*(a j:ℝ))
 (w:I→ℝ) (hw:∀ i,0≤w i) : 0≤∑ i,∑ j,w i*M i j*w j := by
  change 0≤quad M w
  choose u _hu hs hl using fun i=>Real.exists_seq_rat_strictAnti_tendsto (w i)
  have positive_u (n:ℕ) (i:I) : 0<u i n := by
    exact_mod_cast (hw i).trans_lt (hs i n)
  have lim : Tendsto (fun n:ℕ=>quad M (fun i=>(u i n:ℝ))) atTop (𝓝 (quad M w)) := by
    unfold quad
    exact tendsto_finsetSum _ fun i _=>tendsto_finsetSum _ fun j _=>
      ((hl i).mul tendsto_const_nhds).mul (hl j)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds lim
    (fun n=>quad_rat M h (fun i=>u i n) (positive_u n))

theorem copositive_of_nat (M:I→I→ℝ)
 (h:∀ a:I→ℕ,0≤∑ i,∑ j,(a i:ℝ)*M i j*(a j:ℝ))
 (w:I→ℝ) (hw:∀ i,0≤w i) : 0≤∑ i,∑ j,w i*M i j*w j :=
 copositive_of_pos_nat M (fun a _=>h a) w hw
#print axioms copositive_of_pos_nat
#print axioms copositive_of_nat
end GraphTensorVerification
