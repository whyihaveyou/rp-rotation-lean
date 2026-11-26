import MathlibProbe.HeisenbergSpinorPhysicalGates
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected

/-! # A single complex tube and discretization for the finite Heisenberg field

The physical target is joined to the uniform unit longitudinal field by affine
interpolation. The transverse norms on the real segment scale linearly, so its
strict margin is the convex combination of the two endpoint margins. A closed
thickening of that compact segment still lies in every site's open cone. Its
open thickening is connected, and the physically uniform Euler gate theorem
on the closed thickening gives one cutoff throughout the open tube.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace IsingScaling.Rotor.HeisenbergField.SpinorGates

def unitAnchor (V : Type*) : ComplexPartition.Field V :=
  fun _ j => if j=0 then 1 else 0

/-- Parameter zero is the real positive anchor and parameter one is the
prescribed full complex field. -/
def fieldPath {V : Type*} (H : ComplexPartition.Field V) (z : ℂ) :
    ComplexPartition.Field V :=
  ComplexPartition.affine (unitAnchor V) (H-unitAnchor V) z

@[simp] theorem fieldPath_zero {V : Type*} (H : ComplexPartition.Field V) :
    fieldPath H 0 = unitAnchor V := by
  funext v j
  simp [fieldPath,ComplexPartition.affine]

@[simp] theorem fieldPath_one {V : Type*} (H : ComplexPartition.Field V) :
    fieldPath H 1 = H := by
  funext v j
  simp [fieldPath,ComplexPartition.affine]

theorem fieldPath_continuous {V : Type*} (H : ComplexPartition.Field V) (v : V) (j : Fin 3) :
    Continuous (fun z => fieldPath H z v j) := by
  unfold fieldPath ComplexPartition.affine
  fun_prop

private theorem real_segment_cone {V : Type*} {H : ComplexPartition.Field V} (v : V)
    (strict : ‖H v 1‖+‖H v 2‖ < (H v 0).re) {r : ℝ} (hr : r ∈ Icc 0 1) :
    ‖fieldPath H (r:ℂ) v 1‖+‖fieldPath H (r:ℂ) v 2‖ < (fieldPath H (r:ℂ) v 0).re := by
  have axis : (fieldPath H (r:ℂ) v 0).re = 1-r+r*(H v 0).re := by
    simp [fieldPath,unitAnchor,ComplexPartition.affine,Complex.mul_re]
    ring
  have off (j : Fin 3) (hj : j ≠ 0) : ‖fieldPath H (r:ℂ) v j‖ = r*‖H v j‖ := by
    simp [fieldPath,unitAnchor,ComplexPartition.affine,hj,norm_mul,abs_of_nonneg hr.1]
  rw [axis,off 1 (by decide),off 2 (by decide)]
  rcases hr.1.eq_or_lt with he | hp
  · rw [← he]
    norm_num
  · linarith [mul_lt_mul_of_pos_left strict hp,hr.2]

/-- One bounded connected open set contains the full real interpolation,
stays in the cone, and admits a *single* natural cutoff for the disk stability
of all Euler field gates at all sites. -/
theorem exists_euler_gate_path {V : Type*} [Finite V] (H : ComplexPartition.Field V)
    (cone : ∀ v, ‖H v 1‖+‖H v 2‖ < (H v 0).re) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      (0:ℂ) ∈ U ∧ (1:ℂ) ∈ U ∧ (∀ r ∈ Icc (0:ℝ) 1, (r:ℂ) ∈ U) ∧
      (∀ z ∈ U, ∀ v, ‖fieldPath H z v 1‖+‖fieldPath H z v 2‖ < (fieldPath H z v 0).re) ∧
      ∀ᶠ n : ℕ in atTop, ∀ v, ∀ z ∈ U, ∀ x y : ℂ, ‖x‖<1 → ‖y‖<1 →
        oneLegSymbol (fieldEntry (1/(n:ℝ)) (fieldPath H z v)) x y ≠ 0 := by
  let S : Set ℂ := Complex.ofReal '' Icc (0:ℝ) 1
  have compact : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have convex : Convex ℝ S := (convex_Icc (0:ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap
  let O : Set ℂ := ⋂ v : V, {z | ‖fieldPath H z v 1‖+‖fieldPath H z v 2‖ <
    (fieldPath H z v 0).re}
  have op : IsOpen O := isOpen_iInter_of_finite fun v =>
    isOpen_lt ((fieldPath_continuous H v 1).norm.add (fieldPath_continuous H v 2).norm)
      (Complex.continuous_re.comp (fieldPath_continuous H v 0))
  have inside : S ⊆ O := by
    rintro _ ⟨r,hr,rfl⟩
    exact mem_iInter.mpr fun v => real_segment_cone v (cone v) hr
  obtain ⟨δ,hδ,closedInside⟩ := compact.exists_cthickening_subset_open op inside
  let U := Metric.thickening δ S
  let C := Metric.cthickening δ S
  have sc : S ⊆ U := Metric.self_subset_thickening hδ S
  have uc : U ⊆ C := Metric.thickening_subset_cthickening δ S
  have segmentIn (r : ℝ) (hr : r ∈ Icc 0 1) : (r:ℂ) ∈ U := sc ⟨r,hr,rfl⟩
  have u0 : (0:ℂ) ∈ U := by simpa using segmentIn 0 ⟨le_rfl,zero_le_one⟩
  have u1 : (1:ℂ) ∈ U := by simpa using segmentIn 1 ⟨zero_le_one,le_rfl⟩
  have allCone (z : ℂ) (hz : z ∈ C) (v : V) :
      ‖fieldPath H z v 1‖+‖fieldPath H z v 2‖ < (fieldPath H z v 0).re :=
    mem_iInter.mp (closedInside hz) v
  refine ⟨U,Metric.isOpen_thickening,(convex.thickening δ).isConnected ⟨0,u0⟩,
    compact.isBounded.thickening,u0,u1,segmentIn,fun z hz => allCone z (uc hz),?_⟩
  have gates := field_gates_eventually_on_compact (C := C) compact.cthickening (fieldPath H)
    (fun v j => (fieldPath_continuous H v j).continuousOn) allCone
  filter_upwards [gates] with n hn
  exact fun v z hz => hn v z (uc hz)

#print axioms exists_euler_gate_path

end IsingScaling.Rotor.HeisenbergField.SpinorGates
