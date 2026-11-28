import C5.OddZModRows
import C5.CopoTightRows
import C5.OddCATCycle

namespace C5GeneralCycles
open OAI.HyperbolicObstruction
open scoped BigOperators
set_option maxHeartbeats 2000000

/-- The strict odd-cycle bound on actual CAT(0) distances satisfying the
normalized copositivity constraint, indexed in cyclic order. -/
theorem odd_cyclic_copo_strict {X : Type*} [MetricSpace X] (hc : CATZero X)
    (k : ℕ) (hk : 1 ≤ k)
    (x : ZMod (2*(k+1)+1) → X)
    (hcp : ∀ p : ZMod (2*(k+1)+1) → ℝ, (∀ i, 0 ≤ p i) →
      0 ≤ ∑ i, ∑ j, (1-2*dist (x i) (x j))*p i*p j) :
    ((k:ℝ)+2)*(∑ i, dist (x i) (x (i+1))) <
      ((2*(k+1)+1:ℕ):ℝ)^2 / 2 := by
  classical
  let N := 2*(k+1)+1
  letI : NeZero N := ⟨by dsimp [N]; omega⟩
  let I := ZMod N
  have hcard : Fintype.card I = N := ZMod.card N
  let d (i j : I) := dist (x i) (x j)
  let R (i : I) := ∑ j, d i j
  let A (i : I) := d i (i+1)
  let U := (N:ℝ)^2/2
  let prev : I ≃ I := Equiv.addRight (-1)
  let rot (r : ℕ) : I ≃ I := Equiv.addRight (((2*r+2:ℕ): ZMod N))
  have hprev (i : I) : d i (i+((2*(k+1):ℕ):ZMod N)) = A (prev i) := by
    have h : (((2*(k+1):ℕ):ZMod N)) + 1 = 0 := by
      rw [← Nat.cast_succ]
      exact ZMod.natCast_self N
    have he : (((2*(k+1):ℕ):ZMod N)) = -1 := eq_neg_of_add_eq_zero_left h
    rw [he]
    change d i (i + (-1)) = d (i+(-1)) (i+(-1)+1)
    have h₂ : i + (-1) + 1 = i := by abel
    rw [h₂]
    exact dist_comm _ _
  have htriangle (i : I) (r : ℕ) :
      A (rot r i) ≤ d i (i+((2*r+2:ℕ):ZMod N)) + d i (i+((2*r+3:ℕ):ZMod N)) := by
    have he : i+((2*r+2:ℕ):ZMod N)+1 = i+((2*r+3:ℕ):ZMod N) := by
      rw [add_assoc, ← Nat.cast_succ]
    change d (i+((2*r+2:ℕ):ZMod N)) (i+((2*r+2:ℕ):ZMod N)+1) ≤ _
    rw [he]
    simpa only [d, dist_comm (x (i+((2*r+2:ℕ):ZMod N))) (x i)] using
      dist_triangle (x (i+((2*r+2:ℕ):ZMod N))) (x i) (x (i+((2*r+3:ℕ):ZMod N)))
  have hrow (i : I) : A (prev i) + A i + (∑ r ∈ Finset.range k, A (rot r i)) ≤ R i := by
    have hh := pairing_row_slack (fun j : ℕ => d i (i+(j:ZMod N)))
      (fun r => A (rot r i)) k (by simp [d]) (fun r _ => htriangle i r)
    change d i (i+(1:ℕ)) + d i (i+((2*(k+1):ℕ):ZMod N)) + _ ≤ _ at hh
    rw [hprev, ← zmod_row_offsets N (d i) i] at hh
    simpa [A,R,add_comm] using hh
  have hsum : (∑ i, ∑ j, (1-2*d i j)) = (N:ℝ)^2 - 2*(∑ i,R i) := by
    simp only [R, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    ring
  have hglobal : (∑ i,R i) ≤ U := by
    have hg := hcp (fun _ => 1) (fun _ => zero_le_one)
    simp only [mul_one] at hg
    change 0 ≤ (∑ i, ∑ j, (1-2*d i j)) at hg
    rw [hsum] at hg
    dsimp [U]
    linarith
  have hb := pairing_budget_tight prev rot A R k U hrow hglobal
  change ((k:ℝ)+2)*(∑ i,A i) < U
  apply lt_of_le_of_ne hb.1
  intro heq
  obtain ⟨hs,ht⟩ := hb.2 heq
  have hQ : ∀ i : I, R i = (N:ℝ)/2 := by
    have h0 : (∑ i, ∑ j, (1-2*d i j)) = 0 := by
      rw [hsum,hs]
      dsimp [U]
      ring
    have ha := copo_rows_at_ones (fun i j => 1-2*d i j)
      (fun i j => by rw [show d i j = d j i from dist_comm _ _])
      (fun i => by simp [d]) h0 hcp
    intro i
    have h := ha i
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, hcard,nsmul_eq_mul,mul_one] at h
    change (N:ℝ)-2*R i=0 at h
    linarith
  have hT (i : I) (r : ℕ) (hr : r < k) :
      A (rot r i) = d i (i+((2*r+2:ℕ):ZMod N)) + d i (i+((2*r+3:ℕ):ZMod N)) := by
    apply pairing_row_eq_implies_tight (fun j : ℕ => d i (i+(j:ZMod N)))
      (fun r => A (rot r i)) k (by simp [d]) (fun r _ => htriangle i r) _ r hr
    rw [Nat.cast_one,hprev, ← zmod_row_offsets N (d i) i]
    simpa only [A,R,add_comm (A i)] using ht i
  let lift (i : ℤ) : X := x (i:ZMod N)
  let a (i : ℤ) := dist (lift i) (lift (i+1))
  have hper (i : ℤ) : lift (i+(2*((k+1:ℕ):ℤ)+1)) = lift i := by
    have h : (2*((k+1:ℕ):ℤ)+1) = (N:ℤ) := by dsimp [N] <;> push_cast
    rw [h]
    simp [lift]
  have ha (i : ℤ) : a i = A (i:ZMod N) := by
    simp [a,lift,A,d]
  have hp (i : ℤ) : a (i + (2*((k+1:ℕ):ℤ)+1)) = a i := by
    have h : i + (2*((k+1:ℕ):ℤ)+1)+1 = (i+1)+(2*((k+1:ℕ):ℤ)+1) := by omega
    unfold a
    rw [h,hper,hper]
  have hpair (i : ℤ) :
      a (i-1) + (∑ r ∈ Finset.range (k+1), a (i+2*(r:ℤ))) = (N:ℝ)/2 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero,mul_zero,add_zero]
    rw [← add_assoc]
    simp_rw [ha]
    have hhprev : ((i-1:ℤ):ZMod N) = prev (i:ZMod N) := by
      change ((i-1:ℤ):ZMod N) = (i:ZMod N)+(-1)
      simp [sub_eq_add_neg]
    have hhrot (r : ℕ) : ((i+2*(r+1:ℕ):ℤ):ZMod N) = rot r (i:ZMod N) := by
      change ((i+2*(r+1:ℕ):ℤ):ZMod N) = (i:ZMod N)+((2*r+2:ℕ):ZMod N)
      push_cast
      ring
    simp_rw [hhprev,hhrot]
    simpa only [add_right_comm (A (prev (i:ZMod N)))] using
      (ht (i:ZMod N)).trans (hQ (i:ZMod N))
  have hstep := pairing_constant_adjacent a (k+1) hp
    (fun i => (by simpa [hp] using (hpair (i+2)).trans (hpair i).symm))
  have ha_const := int_translate_constant a hstep
  have hA (i : ZMod N) : A i = a 0 := by
    have h := ha_const (i.val:ℤ)
    simpa [ha,ZMod.natCast_zmod_val] using h
  have hpos : 0 < a 0 := by
    have h := heq
    simp only [hA,Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at h
    have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
    have hU : 0 < U := by dsimp [U]; positivity
    by_contra! hle
    have h0 : ((k:ℝ)+2)*((N:ℝ)*a 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos hN.le hle)
    linarith
  exfalso
  apply no_paired_odd_cat_cycle hc lift (k+1) (by omega) (a 0) hpos hper ha_const
  intro i r hr hrk
  let q := (r-1).toNat
  have hq : (q:ℤ)+1 = r := by dsimp [q]; omega
  have hqk : q < k := by omega
  have h := (hT (i:ZMod N) q hqk)
  rw [hA] at h
  have ht1 : ((i+2*r:ℤ):ZMod N) = (i:ZMod N)+((2*q+2:ℕ):ZMod N) := by
    have he : i+2*r=i+((2*q+2:ℕ):ℤ) := by push_cast; omega
    rw [he,Int.cast_add,Int.cast_natCast]
  have ht2 : ((i+2*r+1:ℤ):ZMod N) = (i:ZMod N)+((2*q+3:ℕ):ZMod N) := by
    have he : i+2*r+1=i+((2*q+3:ℕ):ℤ) := by push_cast; omega
    rw [he,Int.cast_add,Int.cast_natCast]
  simpa only [lift,ht1,ht2,d,dist_comm (x ((i:ZMod N)+((2*q+3:ℕ):ZMod N))) (x (i:ZMod N))] using h.symm

#print axioms odd_cyclic_copo_strict
end C5GeneralCycles
