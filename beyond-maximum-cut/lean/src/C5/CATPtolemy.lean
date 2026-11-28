import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace C5Certificate

private theorem amgm {A B K X Y : ℝ} (ha : 0<A) (e : A*B=K^2) :
 2*K*X*Y ≤ A*X^2+B*Y^2 := by
  have h : A*((A*X^2+B*Y^2)-2*K*X*Y)=(A*X-K*Y)^2 := by
    calc
      _ = (A*X)^2-2*(A*X)*(K*Y)+(A*B)*Y^2 := by ring
      _ = _ := by rw [e]; ring
  have hz : 0 ≤ A*((A*X^2+B*Y^2)-2*K*X*Y) := by
    rw [h]
    exact sq_nonneg _
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hz)

private theorem weights {a c d f X Y : ℝ}
 (ha : 0<a) (hc : 0<c) (hd : 0<d) (hf : 0<f)
 (h : ∀ s t : ℝ, 0≤s → s≤1 → 0≤t → t≤1 →
    s*(1-s)*X^2+t*(1-t)*Y^2 ≤
      (1-s)*(1-t)*a^2+s*(1-t)*d^2+(1-s)*t*c^2+s*t*f^2) :
 X*Y ≤ a*f+c*d := by
  have hfd := mul_pos hf hd
  have hac := mul_pos ha hc
  have hfc := mul_pos hf hc
  have had := mul_pos ha hd
  let P := f*d+a*c
  let Q := f*c+a*d
  have hP : 0<P := add_pos hfd hac
  have hQ : 0<Q := add_pos hfc had
  let s := a*c/P
  let t := a*d/Q
  let K := a*f*c*d/(P*Q)
  have hs0 : 0<s := div_pos hac hP
  have hs1 : s<1 := (div_lt_iff₀ hP).2 (by dsimp [P]; linarith only [hfd])
  have ht0 : 0<t := div_pos had hQ
  have ht1 : t<1 := (div_lt_iff₀ hQ).2 (by dsimp [Q]; linarith only [hfc])
  have hK : 0<K := div_pos (mul_pos (mul_pos (mul_pos ha hf) hc) hd) (mul_pos hP hQ)
  have ew : (s*(1-s))*(t*(1-t))=K^2 := by
    dsimp only [s,t,K]
    field_simp [ne_of_gt hP,ne_of_gt hQ]
    dsimp only [P,Q] <;> ring
  have es : (1-s)*(1-t)*a^2+s*(1-t)*d^2+(1-s)*t*c^2+s*t*f^2=2*K*(a*f+c*d) := by
    dsimp only [s,t,K]
    field_simp [ne_of_gt hP,ne_of_gt hQ]
    dsimp only [P,Q] <;> ring
  have hi := h s t hs0.le hs1.le ht0.le ht1.le
  rw [es] at hi
  have lo := amgm (mul_pos hs0 (sub_pos.mpr hs1)) ew (X:=X) (Y:=Y)
  have hh : (2*K)*(X*Y) ≤ (2*K)*(a*f+c*d) := by
    simpa only [mul_assoc] using lo.trans hi
  exact le_of_mul_le_mul_left hh (mul_pos (by norm_num) hK)

theorem ptolemy_of_CN {X : Type*} [MetricSpace X]
 (cn : ∀ (U V : X) (s : ℝ), 0≤s → s≤1 → ∃ P : X, ∀ W : X,
   dist P W ^ 2 ≤ (1-s)*dist U W ^ 2+s*dist V W ^ 2-s*(1-s)*dist U V ^ 2)
 (A B C D : X) : dist A C*dist B D ≤ dist A B*dist C D+dist A D*dist B C := by
  by_cases hAB : A=B
  · subst B; simp only [dist_self,mul_zero,zero_add,mul_comm,le_refl]
  by_cases hBC : B=C
  · subst C; simp only [dist_self,mul_zero,add_zero,le_refl]
  by_cases hCD : C=D
  · subst D; simp only [dist_self,mul_zero,zero_add,le_refl]
  by_cases hAD : A=D
  · subst D; simp only [dist_self,mul_zero,add_zero,dist_comm B A,dist_comm C A,mul_comm,le_refl]
  apply weights (dist_pos.mpr hAB) (dist_pos.mpr hAD) (dist_pos.mpr hBC) (dist_pos.mpr hCD)
  intro s t hs0 hs1 ht0 ht1
  obtain ⟨p,hp⟩ := cn A C s hs0 hs1
  obtain ⟨q,hq⟩ := cn B D t ht0 ht1
  have hpq := hp q
  have hva := hq A
  have hvc := hq C
  rw [dist_comm q A, dist_comm B A, dist_comm D A] at hva
  rw [dist_comm q C, dist_comm D C] at hvc
  have e1 := mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr hs1)
  have e2 := mul_le_mul_of_nonneg_left hvc hs0
  nlinarith only [hpq,e1,e2,sq_nonneg (dist p q)]
#print axioms ptolemy_of_CN
end C5Certificate
