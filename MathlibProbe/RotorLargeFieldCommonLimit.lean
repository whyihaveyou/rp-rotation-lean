import MathlibProbe.RotorLargeFieldUniqueness
import MathlibProbe.RotorFieldFreeExhaustion
import MathlibProbe.RotorHeisenbergCorrelationInput
import MathlibProbe.RotorHeisenbergFreeFieldLimit

/-! # A physical large-field interval for the Heisenberg dot-pair readouts

Fix a nonnegative nearest-neighbour coupling. On the large-field interval the
one-site Dobrushin theorem gives a unique Gibbs law. Free cubes, their
translates, and bond-centred rectangles have this same stationary limit by
free-domain exhaustion. The site and bond reflection forms of its dot pair
therefore come from these actual finite spin integrals. Applying the angular
theorem to this pair gives the rotation of every susceptibility-normalized
tangent, including its normalization and cube ratios along that subsequence.
Here the limit in field is towards positive infinity, at fixed coupling.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace IsingScaling.Rotor.HeisenbergField.LargeField
open PressureSelection ModelPackets

/-- At sufficiently high field the unique Gibbs probability is the prescribed
free thermodynamic limit for both shapes. -/
theorem common_free_limit_eventually {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ h : ℝ in atTop, ∃ P : ProbabilityMeasure (SpinField 3),
      IsFieldGibbs β h P ∧ (∀ Q, IsFieldGibbs β h Q → Q=P) ∧ CommonFreeLimit β h P := by
  filter_upwards [exists_unique_fieldGibbs_eventually hβ] with h H
  obtain ⟨P,hP,unique⟩ := H
  exact ⟨P,hP,unique,FreeInduced.commonFreeLimit_of_unique P unique⟩

/-- All fixed coordinate moments of the original free-cube laws converge;
the translation and bond-rectangle comparisons also converge on this tail. -/
theorem scalar_thermodynamic_limit_eventually {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ h : ℝ in atTop, ScalarThermodynamicLimit β h := by
  filter_upwards [common_free_limit_eventually hβ] with h ⟨P,_,_,hP⟩
  exact hP.scalarThermodynamicLimit

/-- Direct lattice evaluations at any pair of rotated macroscopic points
have vanishing normalized difference for this same free Heisenberg law. -/
theorem angular_eventually {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ h : ℝ in atTop, ∃ P : ProbabilityMeasure (SpinField 3),
      IsFieldGibbs β h P ∧ CommonFreeLimit β h P ∧
      ∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (O : Space ≃ₗᵢ[ℝ] Space)
        (x : Space), x ≠ 0 → ∀ (k l : ℕ → Site),
        Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
        Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
        Tendsto (fun n => Packet.normalization (fieldPair P) (R n) *
          (fieldPair P (k n)-fieldPair P (l n))) atTop (𝓝 0) := by
  filter_upwards [common_free_limit_eventually hβ, eventually_ge_atTop (0 : ℝ)]
    with h ⟨P,hP,_,hcommon⟩ hh
  exact ⟨P,hP,hcommon,fun _R hR O _x hx _k _l hk hl =>
    (hcommon.forms hβ hh).toDotForms.angular hR O hx hk hl⟩

/-- Every diverging scale sequence in the large-field free Gibbs state has a
rotational subsequential tangent. Every realizing tangent of this same dot
correlation is rotational and gives the cube susceptibility readouts. -/
theorem tangent_readouts_eventually {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ h : ℝ in atTop, ∃ P : ProbabilityMeasure (SpinField 3),
      IsFieldGibbs β h P ∧ CommonFreeLimit β h P ∧
      ∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        (∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
          VaguePairLimit (fieldPair P) (R ∘ u) μ ∧ IsotropicPairMeasure μ) ∧
        (∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ], VaguePairLimit (fieldPair P) R μ →
          IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
            Tendsto (fun n => susceptibility (fieldPair P) (s * R n) /
              susceptibility (fieldPair P) (R n)) atTop (𝓝 (μ.real (observationCube s)))) := by
  filter_upwards [common_free_limit_eventually hβ, eventually_ge_atTop (0 : ℝ)]
    with h ⟨P,hP,_,hcommon⟩ hh
  have forms := (hcommon.forms hβ hh).toDotForms
  exact ⟨P,hP,hcommon,fun _R hR =>
    ⟨forms.exists_isotropic_tangent hR, fun _μ _ hv => forms.tangent_readout hR hv⟩⟩

#print axioms common_free_limit_eventually
#print axioms scalar_thermodynamic_limit_eventually
#print axioms angular_eventually
#print axioms tangent_readouts_eventually

end IsingScaling.Rotor.HeisenbergField.LargeField
