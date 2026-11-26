import MathlibProbe.RotorPhysicalMirrorSelection
import MathlibProbe.RotorPhysicalStateSymmetries

/-!
# The O(N) two-point rotation package

This file records the dimension-uniform scope of the selected-state
construction.  The sphere spin dimension `N` is arbitrary, while the
physical lattice remains three-dimensional.  The theorem is an alias with
an explicit `N` binder for the already proved selected-state construction.
It therefore does not add a critical free-boundary comparison: that input is
only needed by the separate Heisenberg free-boundary bridge.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace IsingScaling.Rotor.PressureSelection.ONFamily
open IsingScaling.Rotor.PressureSelection
open PhysicalMirrorSelection Packet

/-- For every positive spin dimension, one nearest-neighbour sphere-spin Gibbs
law has the complete spatial two-point rotation package.  Internal O(N)
invariance is supplied separately by `InternalOrthogonal`; the conclusion
here is the spatial isotropy of every susceptibility-normalized tangent and
the raw angular readout for arbitrary lattice rotations. -/
theorem exists_on_family_rotation (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField N), ShiftInvariant P ∧
      LocalGibbs.IsNearestGibbs N β P ∧
      ThreeMirrors (fieldPair P) ∧
      (∀ R : ℕ → ℕ, NormalizedPacketSource (fieldPair P) R 0) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧
          IsLocallyFiniteMeasure μ ∧
          ModelPackets.VaguePairLimit (fieldPair P) (R ∘ u) μ ∧
          ModelPackets.IsotropicPairMeasure μ) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
          ModelPackets.VaguePairLimit (fieldPair P) R μ →
          ModelPackets.IsotropicPairMeasure μ) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x ≠ 0 →
          ∀ k l : ℕ → Site,
            Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
            Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
            Tendsto (fun n => normalization (fieldPair P) (R n) *
              (fieldPair P (k n) - fieldPair P (l n))) atTop (𝓝 0)) := by
  exact exists_nearest_with_rotational_two_point N hβ

/-! A named proposition for the full end-to-end package.  The short
dimension-specific corollaries below retain the old law-only names for
backwards compatibility.  The `_full` names expose every field of the
generic theorem, so a citation cannot silently drop tangent and spatial
rotation conclusions. -/
def FullONRotationPackage (N : ℕ) [NeZero N] (β : ℝ) (P : ProbabilityMeasure (SpinField N)) : Prop :=
  ShiftInvariant P ∧
    LocalGibbs.IsNearestGibbs N β P ∧
    (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
      PeriodicHorizontal.FixedBy P (signedPerm p s)) ∧
    InternalOrthogonal.AllInternalInvariant P ∧
    ThreeMirrors (fieldPair P) ∧
    (∀ R : ℕ → ℕ, NormalizedPacketSource (fieldPair P) R 0) ∧
    (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
      ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧
        IsLocallyFiniteMeasure μ ∧
        ModelPackets.VaguePairLimit (fieldPair P) (R ∘ u) μ ∧
        ModelPackets.IsotropicPairMeasure μ) ∧
    (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
      ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
        ModelPackets.VaguePairLimit (fieldPair P) R μ →
        ModelPackets.IsotropicPairMeasure μ) ∧
    (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
      ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x ≠ 0 →
        ∀ k l : ℕ → Site,
          Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
          Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
          Tendsto (fun n => normalization (fieldPair P) (R n) *
            (fieldPair P (k n) - fieldPair P (l n))) atTop (𝓝 0))

theorem exists_on_family_rotation_full (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField N), FullONRotationPackage N β P := by
  obtain ⟨P, h⟩ :=
    PhysicalStateSymmetries.exists_symmetric_nearest_with_rotational_two_point N hβ
  exact ⟨P, by
    simpa [FullONRotationPackage] using h⟩

/-- The XY, Heisenberg, and higher-spin instances are all direct instances of
the same dimension-uniform theorem.  These are named corollaries so that a
downstream manuscript can cite the family result without silently changing
the quantifiers. -/
theorem exists_xy_rotation {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField 2),
      ShiftInvariant P ∧ LocalGibbs.IsNearestGibbs 2 β P :=
  let h := exists_on_family_rotation 2 hβ
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1⟩

theorem exists_heisenberg_rotation {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField 3),
      ShiftInvariant P ∧ LocalGibbs.IsNearestGibbs 3 β P :=
  let h := exists_on_family_rotation 3 hβ
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1⟩

theorem exists_on4_rotation {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField 4),
      ShiftInvariant P ∧ LocalGibbs.IsNearestGibbs 4 β P :=
  let h := exists_on_family_rotation 4 hβ
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1⟩

theorem exists_xy_rotation_full {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField 2), FullONRotationPackage 2 β P := by
  simpa using (exists_on_family_rotation_full 2 hβ)

theorem exists_heisenberg_rotation_full {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField 3), FullONRotationPackage 3 β P := by
  simpa using (exists_on_family_rotation_full 3 hβ)

theorem exists_on4_rotation_full {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField 4), FullONRotationPackage 4 β P := by
  simpa using (exists_on_family_rotation_full 4 hβ)

#print axioms exists_on_family_rotation
#print axioms exists_xy_rotation
#print axioms exists_heisenberg_rotation
#print axioms exists_on4_rotation
#print axioms exists_on_family_rotation_full
#print axioms exists_xy_rotation_full
#print axioms exists_heisenberg_rotation_full
#print axioms exists_on4_rotation_full

end IsingScaling.Rotor.PressureSelection.ONFamily
