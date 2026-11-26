import WireDimension
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.Tensor
import RankPowerCore

namespace WheelVerification
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators
noncomputable section

abbrev Slot (u v i : Fin 3) := {j : Fin 2 // (![u,v] : Fin 2 → Fin 3) j = i}

private def firstSlot (u v : Fin 3) (h : u ≠ v) (A : Type) :
    (Slot u v u → A) ≃ A :=
  ⟨fun f => f ⟨0,rfl⟩, fun x _ => x,
    fun f => by
      funext ⟨j,hj⟩
      fin_cases j
      · rfl
      · exact (h hj.symm).elim,
    fun _ => rfl⟩

private def secondSlot (u v : Fin 3) (h : u ≠ v) (A : Type) :
    (Slot u v v → A) ≃ A :=
  ⟨fun f => f ⟨1,rfl⟩, fun x _ => x,
    fun f => by
      funext ⟨j,hj⟩
      fin_cases j
      · exact (h hj).elim
      · rfl,
    fun _ => rfl⟩

private def emptySlot (u v i : Fin 3) (hu : u ≠ i) (hv : v ≠ i) (A : Type) :
    (Slot u v i → A) ≃ PUnit :=
  ⟨fun _ => (), fun _ j => by
      obtain ⟨j,hj⟩ := j
      revert hj
      refine Fin.cases (fun h => (hu h).elim) (fun j => ?_) j
      exact Fin.cases (fun h => (hv h).elim) (fun z => Fin.elim0 z) j,
    fun _ => by
      funext ⟨j,hj⟩
      fin_cases j
      · exact (hu hj).elim
      · exact (hv hj).elim,
    fun p => by cases p; rfl⟩

private def mergeLeft {A B : Type} : A × (B × PUnit) ≃ B × A :=
  ⟨fun x => (x.2.1,x.1), fun x => (x.2,x.1,()),
    fun ⟨a,b,p⟩ => by cases p; rfl, fun _ => rfl⟩

private def mergeMid {A B : Type} : A × (PUnit × B) ≃ A × B :=
  ⟨fun x => (x.1,x.2.2), fun x => (x.1,(),x.2),
    fun ⟨a,p,b⟩ => by cases p; rfl, fun _ => rfl⟩

private def mergeRight {A B : Type} : PUnit × (A × B) ≃ B × A :=
  ⟨fun x => (x.2.2,x.2.1), fun x => ((),x.2,x.1),
    fun ⟨p,a,b⟩ => by cases p; rfl, fun _ => rfl⟩

def matrixLeg (a b c : ℕ) : Fin 3 → Type :=
  ![Fin c × Fin a, Fin a × Fin b, Fin b × Fin c]

instance (a b c : ℕ) (i : Fin 3) : Fintype (matrixLeg a b c i) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i) i
  · exact inferInstanceAs (Fintype (Fin c × Fin a))
  · exact inferInstanceAs (Fintype (Fin a × Fin b))
  · exact inferInstanceAs (Fintype (Fin b × Fin c))

def matrixCoeff (K : Type) [Field K] (a b c : ℕ) (x : ∀ i, matrixLeg a b c i) : K :=
  matrixTensor K a b c (x 0) (x 1) (x 2)

def rectWire (K : Type) [Field K] (a b c : ℕ) : TensorClass.{0} (Fin 3) K :=
  wireDimension K (0 : Fin 3) 1 a *
    (wireDimension K (2 : Fin 3) 0 c * wireDimension K (2 : Fin 3) 1 b)

def rectRawWire (K : Type) [Field K] (a b c : ℕ) : Raw (Fin 3) K :=
  ((Raw.diagonal (Fin 2) K (Fin a)).group ![0,1]).mul
    (((Raw.diagonal (Fin 2) K (Fin c)).group ![2,0]).mul
     ((Raw.diagonal (Fin 2) K (Fin b)).group ![2,1]))

private def pack (K : Type) [Field K] (a b c : ℕ) (i : Fin 3) :
    (rectRawWire K a b c).Leg i ≃ matrixLeg a b c i := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i) i
  · exact ((firstSlot 0 1 (by decide) (Fin a)).prodCongr
      ((secondSlot 2 0 (by decide) (Fin c)).prodCongr
       (emptySlot 2 1 0 (by decide) (by decide) (Fin b)))).trans mergeLeft
  · exact ((secondSlot 0 1 (by decide) (Fin a)).prodCongr
      ((emptySlot 2 0 1 (by decide) (by decide) (Fin c)).prodCongr
       (secondSlot 2 1 (by decide) (Fin b)))).trans mergeMid
  · exact ((emptySlot 0 1 2 (by decide) (by decide) (Fin a)).prodCongr
      ((firstSlot 2 0 (by decide) (Fin c)).prodCongr
       (firstSlot 2 1 (by decide) (Fin b)))).trans mergeRight

private theorem diag_two (K : Type) [Field K] {m : ℕ} (f : Fin 2 → Fin m) :
    (Raw.diagonal (Fin 2) K (Fin m)).coeff f = if f 0 = f 1 then 1 else 0 := by
  rw [Raw.diagonal_coeff_at 0]
  have he : (∀ i, f i = f 0) ↔ f 0 = f 1 := by
    constructor
    · exact fun hh => (hh 1).symm
    · intro hh i
      fin_cases i
      · rfl
      · exact hh.symm
  simp only [he]

theorem rectWire_eq_coeff (K : Type) [Field K] (a b c : ℕ) :
    rectWire K a b c = ofCoeffs (matrixCoeff K a b c) := by
  classical
  have hr : rectWire K a b c = ofRaw (rectRawWire K a b c) := by
    simp only [rectWire,wireDimension,rectRawWire,ofRaw_mul]
  rw [hr]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (pack K a b c)
  intro x
  change (rectRawWire K a b c).coeff x = matrixCoeff K a b c (fun i => pack K a b c i (x i))
  unfold rectRawWire
  simp only [Raw.mul, Raw.group, matrixCoeff, matrixTensor,
    OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients]
  let fa : Fin 2 → Fin a := fun i => (x (![0,1] i)).1 ⟨i,rfl⟩
  let fc : Fin 2 → Fin c := fun i => (x (![2,0] i)).2.1 ⟨i,rfl⟩
  let fb : Fin 2 → Fin b := fun i => (x (![2,1] i)).2.2 ⟨i,rfl⟩
  change (Raw.diagonal (Fin 2) K (Fin a)).coeff fa *
    ((Raw.diagonal (Fin 2) K (Fin c)).coeff fc *
      (Raw.diagonal (Fin 2) K (Fin b)).coeff fb) = _
  rw [diag_two K fa, diag_two K fc, diag_two K fb]
  let P : Prop := (pack K a b c 0 (x 0)).2 = (pack K a b c 1 (x 1)).1 ∧
    (pack K a b c 1 (x 1)).2 = (pack K a b c 2 (x 2)).1 ∧
    (pack K a b c 2 (x 2)).2 = (pack K a b c 0 (x 0)).1
  have hp : P ↔ fa 0 = fa 1 ∧ fb 0 = fb 1 ∧ fc 0 = fc 1 := by
    change (fa 0 = fa 1 ∧ fb 1 = fb 0 ∧ fc 0 = fc 1) ↔ _
    exact ⟨fun ⟨a,b,c⟩ => ⟨a,b.symm,c⟩, fun ⟨a,b,c⟩ => ⟨a,b.symm,c⟩⟩
  calc
    _ = (if fa 0 = fa 1 ∧ fb 0 = fb 1 ∧ fc 0 = fc 1 then (1:K) else 0) := by
      by_cases ha : fa 0 = fa 1 <;> by_cases hb : fb 0 = fb 1 <;>
        by_cases hc : fc 0 = fc 1 <;> simp [ha,hb,hc]
    _ = _ := by
      change (if fa 0 = fa 1 ∧ fb 0 = fb 1 ∧ fc 0 = fc 1 then (1:K) else 0) =
        (if P then 1 else 0)
      exact if_congr hp.symm rfl rfl

#print axioms rectWire_eq_coeff
end
end WheelVerification
