import MathlibProbe.HeisenbergDampedTraceLimit
import MathlibProbe.HeisenbergEulerGateProduct
import MathlibProbe.HeisenbergSiteSymmetrization
import MathlibProbe.HeisenbergSpinorConePath

/-! # Finite-graph Lee–Yang nonvanishing for the classical Heisenberg spin

The measure is the product of uniform area measures on the unit two-sphere.
The actual directed coupling matrix enters the real energy with a factor
of one half. Separate binary legs are attached even to the two ends of a
self-interaction. Both the positive site normalization and the Euler bond
shift are retained in the passage to the physical partition function.
-/

noncomputable section
open Filter Set
open scoped Topology Classical
namespace IsingScaling.Rotor.HeisenbergField.FerromagneticLeeYang
open ComplexPartition SpinorGates EulerGates
open MathlibProbe.HeisenbergAsanoWire

/-- Closing all binary wires at unit weight gives the trace on physical
leg assignments, independently of the enumeration. -/
private theorem trace_dense_one {L : Type*} [Fintype (L → Bool)] {d : ℕ}
    (e : Fin d ≃ L) (M : Matrix (L → Bool) (L → Bool) ℂ) :
    denseTrace d (SiteSymmetrization.denseCoeff e M) (fun _ => 1) = Matrix.trace M := by
  classical
  rw [denseTrace_one]
  let E := e.arrowCongr (Equiv.refl Bool)
  exact E.sum_comp (fun b => M b b)

/-- Matrix multiplication may use the constructive enumeration of Euler
port assignments or the generic enumeration on an abstract finite leg set. -/
private theorem stable_with_enumeration {V L : Type*} [Fintype L] [Fintype V]
    [f : Fintype (L → Bool)] {d : ℕ} (loc : L → V) (e : Fin d ≃ L)
    (M : SiteSymmetrization.BitMatrix L) (hm : SiteSymmetrization.Stable e M) :
    SiteSymmetrization.Stable e (EulerTensor.siteSym loc * M) := by
  have same : f = @Pi.instFintype L (fun _ => Bool) (Classical.decEq L)
      inferInstance (fun _ => Bool.fintype) := Subsingleton.elim _ _
  subst f
  exact SiteSymmetrization.siteSym_mul_stable loc e M hm

/-- Multiplication by the field-independent site projections preserves
holomorphy entry by entry. -/
private theorem entire_sym_entry {V : Type*} [Fintype V] (J : V → V → ℝ)
    (H : ComplexPartition.Field V) (n : ℕ) (r c : Port V n → Bool) :
    Differentiable ℂ (fun z => (EulerTensor.siteSym (loc (V := V) (n := n)) *
      productMatrix J (fieldPath H z) n) r c) := by
  classical
  simp only [Matrix.mul_apply]
  apply Differentiable.fun_sum
  intro i _
  exact (differentiable_const _).mul (differentiable_productMatrix_affine J
    (unitAnchor V) (H - unitAnchor V) n i c)

set_option maxHeartbeats 1200000 in
/-- At every site the three complex field components may vary independently.
All finite nonnegative coupling matrices, including the empty graph, obey
the physical zero-free cone. -/
theorem partition_ne_zero {V : Type*} [Fintype V] (J : V → V → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) (H : ComplexPartition.Field V)
    (hc : ∀ x, ‖H x 1‖ + ‖H x 2‖ < (H x 0).re) : partition J H ≠ 0 := by
  classical
  obtain ⟨U,ho,hconn,_,h0,h1,_,_,ev⟩ := exists_euler_gate_path H hc
  let q (n : ℕ) := Fintype.card (Port V n)
  let e (n : ℕ) : Fin (q n) ≃ Port V n := (Fintype.equivFin _).symm
  let T (n : ℕ) (z : ℂ) := EulerTensor.siteSym (loc (V := V) (n := n)) * productMatrix J (fieldPath H z) n
  let M (n : ℕ) (b : Fin (q n) → Bool × Bool) (z : ℂ) :=
    SiteSymmetrization.denseCoeff (e n) (T n z) b
  let c (n : ℕ) : ℂ := EulerTensor.dimensionFactor (loc (V := V) (n := n))
  have anchor : uniform (V := V) ((1 : ℝ) : ℂ) = unitAnchor V := by
    funext x i
    simp only [uniform,unitAnchor,Complex.ofReal_one]
  have hz := DampedTraceLimit.physical_partition_of_dense_network J hJ
    (h₀ := 1) (by norm_num) (H - unitAnchor V) ho hconn.isPreconnected h0 h1 q M c
  rw [anchor] at hz
  rw [← fieldPath_one H]
  apply hz
  filter_upwards [ev] with n gate
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Complex.ofReal_ne_zero.mpr (EulerTensor.dimensionFactor_pos _).ne'
  · intro b
    exact (entire_sym_entry J H n _ _).differentiableOn
  · intro z hz v hv
    have hgate := stable_of_field_gates J hJ (fieldPath H z) n
      (fun x => gate x z hz) (e n)
    have hs := stable_with_enumeration (loc (V := V) (n := n)) (e n)
      (productMatrix J (fieldPath H z) n) hgate
    exact hs v hv
  · intro z _
    change c n * denseTrace (q n) (SiteSymmetrization.denseCoeff (e n) (T n z))
      (fun _ => 1) = ClassicalEuler.approximant J (fieldPath H z) n
    rw [trace_dense_one, approximant_eq_trace]

#print axioms partition_ne_zero
end IsingScaling.Rotor.HeisenbergField.FerromagneticLeeYang
