import C5.MatrixBridge
import C5.Copositivity
import OAI.LinearAlgebra.SpectralBooks.FinitePriceSpace
import OAI.LinearAlgebra.SpectralBooks.Theorem
import OAI.LinearAlgebra.SpectralBooks.StrassenRank
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordWiring

namespace C5Certificate
open OAI OAI.HyperbolicObstruction
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open OAI.LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators NNReal
noncomputable section
set_option maxHeartbeats 0
variable {K : Type*} [Field K]

abbrev FiveTensor (K:Type*) [Field K] := TensorClass.{0} (Fin 5) K
abbrev FivePoint (K:Type*) [Field K] :=
  normalizedSpectrum ((· ≤ ·) : FiveTensor K → _ → Prop)

private theorem ptolemy_of_catZero {X:Type*} [MetricSpace X] (h:CATZero X) (A B C D:X) :
 dist A C*dist B D ≤ dist A B*dist C D+dist A D*dist B C := by
  apply ptolemy_of_CN _ A B C D
  intro U V s slo shi
  obtain ⟨γ,_,hs⟩ := h U V
  refine ⟨γ s,fun W=>?_⟩
  have hw := hs W s ⟨slo,shi⟩
  rwa [dist_comm W (γ s),dist_comm W U,dist_comm W V] at hw
private theorem wire_nonzero (e:Chord 5) : wire K e ≠ 0 := by
  intro hz
  have hp := (ofRaw_eq_zero_iff _).mp hz
  have he : (Raw.diagonal (Fin 2) K (Fin 2)).coeff = 0 := by
    by_contra hn
    exact (((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff ![e.1.1,e.1.2]).mpr hn) hp
  have hx := congrFun he (fun _=>(0:Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _=>(0:Fin 2))=0 at hx
  simp [Raw.diagonal,funext_iff] at hx
private theorem eval_pos (φ:FivePoint K) {T:FiveTensor K} (hT:T≠0) :
 0 < (φ.val T:ℝ) := by exact_mod_cast spectral_value_pos φ hT
private theorem log_mul (φ:FivePoint K) {T U:FiveTensor K} (hT:T≠0) (hU:U≠0) :
 Real.logb 2 (φ.val (T*U):ℝ) = Real.logb 2 (φ.val T:ℝ)+Real.logb 2 (φ.val U:ℝ) := by
  rw [φ.property.2.2.2.1, NNReal.coe_mul, Real.logb_mul (eval_pos φ hT).ne' (eval_pos φ hU).ne']
private theorem wire_dist_eval (φ:FivePoint K) (e:Chord 5) :
 rawWireDistance φ 1 e.1.1 e.1.2=Real.logb 2 (φ.val (wire K e):ℝ) := by
  simp [rawWireDistance,rawLogPrice,wire]
private theorem wire_distance_le_one (φ:FivePoint K) (i j:Fin 5) :
 rawWireDistance φ 1 i j ≤ 1 := by
  have sorted (e:Chord 5) : rawWireDistance φ 1 e.1.1 e.1.2 ≤ 1 := by
    rw [wire_dist_eval φ e,← Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    have h := φ.property.2.2.2.2 _ _ (wire_le_two K e)
    have h2 : φ.val (2:FiveTensor K)=(2:ℝ≥0) := map_ofNat (normalizedSpectrum.toRingHom φ) 2
    rw [h2] at h
    apply Real.logb_le_logb_of_le (by norm_num) (eval_pos φ (wire_nonzero e))
    exact_mod_cast h
  rcases lt_trichotomy i j with h|h|h
  · exact sorted (edge i j h)
  · subst j; rw [rawWireDistance_self φ 1 zero_le_one]; norm_num
  · rw [rawWireDistance_symm φ 1]; exact sorted (edge j i h)

/-- This premise is explicit and is not supplied by a user-added axiom. -/
def ZhouCP (φ:FivePoint K) : Prop :=
 ∀ w:Fin 5→ℝ, (∀ i, 0≤w i) →
  0≤∑ i,∑ j,w i*(1-2*rawWireDistance φ 1 i j)*w j

theorem spectral_metric_of_cp (φ:FivePoint K) (hcp:ZhouCP φ) :
 MatrixMetric (rawWireDistance φ 1) := by
  refine ⟨?_,rawWireDistance_self φ 1 zero_le_one,rawWireDistance_symm φ 1,?_,?_,hcp⟩
  · intro i j
    exact ⟨rawLogPrice_nonneg φ zero_le_one _,wire_distance_le_one φ i j⟩
  · exact rawWireDistance_triangle φ 1 zero_le_one
  · obtain ⟨X,met,P,f,_,eq,_⟩ := exists_metric_price_realization φ 1 zero_le_one
    letI := met
    obtain ⟨Y,metY,Q,⟨e⟩,_,cat⟩ := P.exists_complete_catZero_extension
    letI := metY
    intro a b c d
    have hp := ptolemy_of_catZero cat (e.map (f a)) (e.map (f c)) (e.map (f b)) (e.map (f d))
    simpa only [e.isometry.dist_eq,eq,rawWireDistance_symm φ 1 c b] using hp

private def cycleEdges : List (Chord 5) :=
 [edge 0 2 (by decide),edge 1 3 (by decide),edge 2 4 (by decide),edge 0 3 (by decide),edge 1 4 (by decide)]
def binaryCycle (K:Type*) [Field K] : FiveTensor K := (cycleEdges.map (wire K)).prod
private theorem wires_ne (l:List (Chord 5)) : (l.map (wire K)).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons e l ih => exact mul_ne_zero (wire_nonzero e) ih
private theorem wires_log (φ:FivePoint K) (l:List (Chord 5)) :
 Real.logb 2 (φ.val (l.map (wire K)).prod:ℝ) =
 (l.map fun e=>rawWireDistance φ 1 e.1.1 e.1.2).sum := by
  induction l with
  | nil => simp [φ.property.2.1]
  | cons e l ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [log_mul φ (wire_nonzero e) (wires_ne l),ih,wire_dist_eval]
theorem binary_cycle_upper (cp : ∀ φ:FivePoint K, ZhouCP φ) :
 Real.logb 2 (asymptoticRank (binaryCycle K)) ≤ (49:ℝ)/12 := by
  obtain ⟨φ,eq⟩ := exists_spectral_value_eq_asymptoticRank (binaryCycle K)
  rw [← eq,binaryCycle,wires_log]
  have h := matrix_objective_le (rawWireDistance φ 1) (spectral_metric_of_cp φ (cp φ))
  simpa [cycleEdges,edge,add_assoc] using h
theorem binary_cycle_upper_of_pos_nat
 (h : ∀ (φ:FivePoint K) (a:Fin 5→ℕ), (∀ i,0<a i) →
    0≤∑ i,∑ j,(a i:ℝ)*(1-2*rawWireDistance φ 1 i j)*(a j:ℝ)) :
 Real.logb 2 (asymptoticRank (binaryCycle K)) ≤ (49:ℝ)/12 := by
  apply binary_cycle_upper
  intro φ
  exact copositive_of_pos_nat (fun i j => 1-2*rawWireDistance φ 1 i j) (h φ)
#print axioms binary_cycle_upper_of_pos_nat
#print axioms binary_cycle_upper
end
end C5Certificate
