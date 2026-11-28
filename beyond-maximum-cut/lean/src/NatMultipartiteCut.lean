import Lean
namespace WenJ.GraphTensor.MaxCut.NatModel

def leftMass (xs : List (Nat × Nat)) : Nat := (xs.map Prod.fst).sum
def rightMass (xs : List (Nat × Nat)) : Nat := (xs.map Prod.snd).sum
def partSizes (xs : List (Nat × Nat)) : List Nat := xs.map fun p => p.1 + p.2

def cross : List (Nat × Nat) → Nat
  | [] => 0
  | (l,r) :: xs => l * rightMass xs + r * leftMass xs + cross xs

def score (L R : Nat) (xs : List (Nat × Nat)) : Nat :=
  L * rightMass xs + R * leftMass xs + cross xs

theorem score_head (L R l r : Nat) (xs : List (Nat × Nat)) :
    score L R ((l,r) :: xs) =
      score L R xs + l * (R + rightMass xs) + r * (L + leftMass xs) := by
  simp [score, cross, leftMass, rightMass, Nat.mul_add]
  ac_rfl

theorem score_push (L R l r : Nat) (xs : List (Nat × Nat)) :
    score L R ((l,r) :: xs) = l * R + r * L + score (L+l) (R+r) xs := by
  simp [score, cross, leftMass, rightMass, Nat.mul_add, Nat.add_mul]
  ac_rfl

theorem round_parts (xs : List (Nat × Nat)) (L R : Nat) :
    ∃ ys : List (Nat × Nat), partSizes ys = partSizes xs ∧
      (∀ p ∈ ys, p.1 = 0 ∨ p.2 = 0) ∧ score L R xs ≤ score L R ys := by
  induction xs generalizing L R with
  | nil => exact ⟨[],rfl,by simp,Nat.le_refl _⟩
  | cons p xs ih =>
    obtain ⟨l,r⟩ := p
    by_cases h : L + leftMass xs ≤ R + rightMass xs
    · have hm := Nat.mul_le_mul_left r h
      have hstep : score L R ((l,r) :: xs) ≤ score L R ((l+r,0) :: xs) := by
        simp only [score_head, Nat.add_mul, Nat.zero_mul, Nat.add_zero]
        omega
      obtain ⟨ys,heq,hwhole,hbetter⟩ := ih (L + (l+r)) R
      refine ⟨(l+r,0) :: ys, ?_, ?_, Nat.le_trans hstep ?_⟩
      · simpa [partSizes] using heq
      · intro i hi
        rcases List.mem_cons.mp hi with hi | hi
        · subst i
          exact Or.inr rfl
        · exact hwhole i hi
      · simp only [score_push, Nat.zero_mul, Nat.add_zero]
        exact Nat.add_le_add_left hbetter _
    · have hm := Nat.mul_le_mul_left l (show R + rightMass xs ≤ L + leftMass xs by omega)
      have hstep : score L R ((l,r) :: xs) ≤ score L R ((0,l+r) :: xs) := by
        simp only [score_head, Nat.add_mul, Nat.zero_mul, Nat.add_zero]
        omega
      obtain ⟨ys,heq,hwhole,hbetter⟩ := ih L (R + (l+r))
      refine ⟨(0,l+r) :: ys, ?_, ?_, Nat.le_trans hstep ?_⟩
      · simpa [partSizes] using heq
      · intro i hi
        rcases List.mem_cons.mp hi with hi | hi
        · subst i
          exact Or.inl rfl
        · exact hwhole i hi
      · simp only [score_push, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
        exact Nat.add_le_add_left hbetter _

theorem cross_eq_mass_mul (xs : List (Nat × Nat))
    (h : ∀ p ∈ xs, p.1 = 0 ∨ p.2 = 0) :
    cross xs = leftMass xs * rightMass xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨l,r⟩ := p
    have h0 : l = 0 ∨ r = 0 := h (l,r) (by simp)
    have ht : ∀ p ∈ xs, p.1 = 0 ∨ p.2 = 0 := fun p hp => h p (by simp [hp])
    rcases h0 with hl | hr
    · subst l
      simp [cross, leftMass, rightMass, ih ht, Nat.mul_add] <;> ac_rfl
    · subst r
      simp [cross, leftMass, rightMass, ih ht, Nat.add_mul] <;> ac_rfl

theorem masses_add (xs : List (Nat × Nat)) :
    leftMass xs + rightMass xs = (partSizes xs).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [leftMass, rightMass, partSizes, List.map_cons, List.sum_cons] at ih ⊢
    omega

private theorem le_sum_of_mem {a : Nat} {xs : List Nat} (h : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | hx
    · omega
    · have hh := ih hx
      omega

theorem whole_part_fits (xs : List (Nat × Nat))
    (hpure : ∀ p ∈ xs, p.1 = 0 ∨ p.2 = 0) {b : Nat} (hb : b ∈ partSizes xs) :
      b ≤ leftMass xs ∨ b ≤ rightMass xs := by
  obtain ⟨p,hp,hb'⟩ := List.mem_map.mp hb
  rcases hpure p hp with hl | hr
  · right
    have hv : p.2 ∈ xs.map Prod.snd := List.mem_map.mpr ⟨p,hp,rfl⟩
    unfold rightMass
    rw [← hb', hl, Nat.zero_add]
    exact le_sum_of_mem hv
  · left
    have hv : p.1 ∈ xs.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
    unfold leftMass
    rw [← hb', hr, Nat.add_zero]
    exact le_sum_of_mem hv

theorem four_cut_le_square (l r : Nat) : 4*(l*r) ≤ (l+r)*(l+r) := by
  by_cases h : l ≤ r
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
    grind
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (show r ≤ l by omega)
    grind

theorem four_cut_eq_square_iff (l r : Nat) :
    4*(l*r) = (l+r)*(l+r) ↔ l = r := by
  constructor
  · intro h
    by_cases hle : l ≤ r
    · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
      have hd : d*d = 0 := by grind
      have hd' : d = 0 := (Nat.mul_eq_zero.mp hd).elim id id
      simp [hd']
    · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (show r ≤ l by omega)
      have hd : d*d = 0 := by grind
      have hd' : d = 0 := (Nat.mul_eq_zero.mp hd).elim id id
      simp [hd']
  · rintro rfl
    grind

theorem heavy_part_cut_bound (l r b N : Nat) (hN : l+r = N)
    (hb : N ≤ b+b) (hfits : b ≤ l ∨ b ≤ r) : l*r ≤ b*(N-b) := by
  rcases hfits with h | h
  · have hr : r ≤ b := by omega
    obtain ⟨x,rb⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨y,bl⟩ := Nat.exists_eq_add_of_le h
    have hn : N-b = r+y := by omega
    rw [hn,bl,rb]
    grind
  · have hl : l ≤ b := by omega
    obtain ⟨x,lb⟩ := Nat.exists_eq_add_of_le hl
    obtain ⟨y,br⟩ := Nat.exists_eq_add_of_le h
    have hn : N-b = l+y := by omega
    rw [hn,br,lb]
    grind

theorem heavy_part_bound_for_any_cut (xs : List (Nat × Nat)) {b N : Nat}
    (hN : (partSizes xs).sum = N) (hb : N ≤ b+b) (hmem : b ∈ partSizes xs) :
    cross xs ≤ b*(N-b) := by
  obtain ⟨ys,heq,hpure,hbetter⟩ := round_parts xs 0 0
  have hfits := whole_part_fits ys hpure (heq.symm ▸ hmem)
  have hny : leftMass ys + rightMass ys = N := (masses_add ys).trans (heq ▸ hN)
  have hr : cross ys ≤ b*(N-b) := by
    rw [cross_eq_mass_mul ys hpure]
    exact heavy_part_cut_bound _ _ _ _ hny hb hfits
  exact Nat.le_trans (by simpa [score] using hbetter) hr

theorem quarter_attainable_iff_whole_balanced (sizes : List Nat) :
    (∃ xs, partSizes xs = sizes ∧ 4 * cross xs = sizes.sum * sizes.sum) ↔
    (∃ ys, partSizes ys = sizes ∧ (∀ p ∈ ys, p.1 = 0 ∨ p.2 = 0) ∧
      leftMass ys = rightMass ys) := by
  constructor
  · rintro ⟨xs,hx,hcross⟩
    obtain ⟨ys,hs,hpure,hbetter⟩ := round_parts xs 0 0
    have hcy : cross xs ≤ cross ys := by simpa [score] using hbetter
    have hys := hs.trans hx
    have hmass : leftMass ys + rightMass ys = sizes.sum := by rw [masses_add,hys]
    have hmin : sizes.sum * sizes.sum ≤ 4 * (leftMass ys * rightMass ys) := by
      rw [← hcross, ← cross_eq_mass_mul ys hpure]
      exact Nat.mul_le_mul_left _ hcy
    have hmax := four_cut_le_square (leftMass ys) (rightMass ys)
    rw [hmass] at hmax
    have h := Nat.le_antisymm hmax hmin
    rw [← hmass] at h
    exact ⟨ys,hys,hpure,(four_cut_eq_square_iff _ _).mp h⟩
  · rintro ⟨ys,hs,hpure,hbal⟩
    have h := (four_cut_eq_square_iff _ _).mpr hbal
    rw [masses_add, hs, ← cross_eq_mass_mul ys hpure] at h
    exact ⟨ys,hs,h⟩

private theorem all_right (sizes : List Nat) :
    ∃ ys, partSizes ys = sizes ∧
      (∀ p ∈ ys, p.1 = 0) ∧ leftMass ys = 0 ∧ rightMass ys = sizes.sum := by
  induction sizes with
  | nil => exact ⟨[],rfl,by simp,rfl,rfl⟩
  | cons b sizes ih =>
    obtain ⟨ys,hs,hp,hl,hr⟩ := ih
    refine ⟨(0,b) :: ys, ?_, ?_, ?_, ?_⟩
    · simpa [partSizes] using hs
    · intro p h
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ rfl
      · exact hp p h
    · simpa [leftMass] using hl
    · simpa [rightMass] using hr

theorem isolate_part (sizes : List Nat) {b : Nat} (hb : b ∈ sizes) :
    ∃ ys, partSizes ys = sizes ∧
      (∀ p ∈ ys, p.1 = 0 ∨ p.2 = 0) ∧ leftMass ys = b := by
  induction sizes with
  | nil => contradiction
  | cons c sizes ih =>
    rcases List.mem_cons.mp hb with hbc | ht
    · subst c
      obtain ⟨ys,hs,hp,hl,_⟩ := all_right sizes
      refine ⟨(b,0) :: ys, by simpa [partSizes] using hs, ?_, ?_⟩
      · intro p hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact Or.inr (hm ▸ rfl)
        · exact Or.inl (hp p hm)
      · simp only [leftMass, List.map_cons, List.sum_cons] at hl ⊢
        rw [hl,Nat.add_zero]
    · obtain ⟨ys,hs,hp,hl⟩ := ih ht
      refine ⟨(0,c) :: ys, by simpa [partSizes] using hs, ?_, ?_⟩
      · intro p hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact Or.inl (hm ▸ rfl)
        · exact hp p hm
      · simpa [leftMass] using hl

theorem heavy_part_bound_attained (sizes : List Nat) {b : Nat} (hb : b ∈ sizes) :
    ∃ ys, partSizes ys = sizes ∧ cross ys = b*(sizes.sum-b) := by
  obtain ⟨ys,hs,hpure,hl⟩ := isolate_part sizes hb
  have hm := masses_add ys
  rw [hl,hs] at hm
  exact ⟨ys,hs,by rw [cross_eq_mass_mul ys hpure,hl,show rightMass ys = sizes.sum-b by omega]⟩
end WenJ.GraphTensor.MaxCut.NatModel
#print axioms WenJ.GraphTensor.MaxCut.NatModel.round_parts
#print axioms WenJ.GraphTensor.MaxCut.NatModel.cross_eq_mass_mul
#print axioms WenJ.GraphTensor.MaxCut.NatModel.heavy_part_bound_for_any_cut
#print axioms WenJ.GraphTensor.MaxCut.NatModel.four_cut_eq_square_iff
#print axioms WenJ.GraphTensor.MaxCut.NatModel.quarter_attainable_iff_whole_balanced
#print axioms WenJ.GraphTensor.MaxCut.NatModel.heavy_part_bound_attained
