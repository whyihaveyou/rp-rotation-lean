import MathlibProbe.HeisenbergFerromagneticLeeYang
import MathlibProbe.RotorPositiveFieldCoordinateLaw

/-! # Spatial rotation for the prescribed Heisenberg free-field state

At each fixed positive field the free-cube Gibbs probabilities converge
through the entire sequence of volumes. Subsequently one may take any weak
accumulation law while the field tends to zero. All spatial conclusions refer
to the two-point function of this same probability law.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace IsingScaling.Rotor.HeisenbergField.PhysicalRotation
open PressureSelection LocalGibbs ModelPackets ComplexPartition PositiveFieldContinuation

private theorem cube_zero_free {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    FiniteLeeYangRotation.FiniteLeeYang (cubeCoupling n β) := by
  apply FerromagneticLeeYang.partition_ne_zero
  intro x y
  unfold cubeCoupling
  split <;> first | exact hβ | exact le_rfl

private theorem rectangle_zero_free {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    FiniteLeeYangRotation.FiniteLeeYang (rectangleCoupling n β) := by
  apply FerromagneticLeeYang.partition_ne_zero
  intro x y
  unfold rectangleCoupling nearestCoupling
  split <;> first | exact hβ | exact le_rfl

/-- The full spin law at fixed positive field, with the prescribed free
exhaustion. Uniqueness here is among laws with this common free limit. -/
theorem unique_positive_free_limit {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 < h) :
    ∃! P : ProbabilityMeasure (SpinField 3), IsFieldGibbs β h P ∧ CommonFreeLimit β h P :=
  PositiveFieldLaw.existsUnique_gibbs_common_free_limit_of_finiteLeeYang hβ
    (cube_zero_free hβ) (rectangle_zero_free hβ) hh

def positiveFreeLaw {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 < h) : ProbabilityMeasure (SpinField 3) :=
  (unique_positive_free_limit hβ hh).exists.choose

theorem positiveFreeLaw_spec {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 < h) :
    IsFieldGibbs β h (positiveFreeLaw hβ hh) ∧ CommonFreeLimit β h (positiveFreeLaw hβ hh) :=
  (unique_positive_free_limit hβ hh).exists.choose_spec

theorem free_boxes_tendsto {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 < h) :
    Tendsto (fun n => cubeLaw β h n) atTop (𝓝 (positiveFreeLaw hβ hh)) :=
  (positiveFreeLaw_spec hβ hh).2.centered

private theorem actual_origin {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto (fun j => positiveFreeLaw hβ (hp j)) atTop (𝓝 Q)) :
    VanishingFieldOrigin β Q :=
  ⟨h, _, hp, hz, fun j => (positiveFreeLaw_spec hβ (hp j)).2, hQ⟩

/-- A physical limiting law exists on a subsequence of every prescribed
positive-field schedule, and satisfies the original zero-field DLR equations. -/
theorem exists_vanishing_limit {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (u : ℕ → ℕ) (Q : ProbabilityMeasure (SpinField 3)), StrictMono u ∧
      Tendsto (fun j => positiveFreeLaw hβ (hp (u j))) atTop (𝓝 Q) ∧ IsNearestGibbs 3 β Q := by
  obtain ⟨Q,u,hu,hQ,_⟩ := spinField_subsequence 3 (fun j => positiveFreeLaw hβ (hp j))
  refine ⟨u,Q,hu,hQ,?_⟩
  exact (actual_origin hβ (fun j => hp (u j)) (hz.comp hu.tendsto_atTop) hQ).gibbs

/-- The same extracted zero-field limit carries the complete dot-pair
    rotation package. This exposes the pair-form input together with the
    zero-field Gibbs equation, instead of requiring callers to reconstruct
    the private witness from the convergence clause. -/
theorem exists_vanishing_limit_with_pairForms {β : ℝ} (hβ : 0 ≤ β)
    {h : ℕ → ℝ} (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (u : ℕ → ℕ) (Q : ProbabilityMeasure (SpinField 3)), StrictMono u ∧
      Tendsto (fun j => positiveFreeLaw hβ (hp (u j))) atTop (𝓝 Q) ∧
      IsNearestGibbs 3 β Q ∧ PairForms Q := by
  obtain ⟨u,Q,hu,hQ,hg⟩ := exists_vanishing_limit hβ hp hz
  refine ⟨u,Q,hu,hQ,hg,?_⟩
  exact (actual_origin hβ (fun j => hp (u j)) (hz.comp hu.tendsto_atTop) hQ).forms hβ

/-- Every spatial tangent of the dot pair of every such physical limit is
orthogonally invariant. Its normalization and cube likelihoods use its own
pair. Each divergent scale sequence has an isotropic tangent subsequence. -/
theorem sharp_rotation {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto (fun j => positiveFreeLaw hβ (hp j)) atTop (𝓝 Q))
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    IsNearestGibbs 3 β Q ∧
      (∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
        VaguePairLimit (fieldPair Q) (R ∘ u) μ ∧ IsotropicPairMeasure μ) ∧
      (∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ], VaguePairLimit (fieldPair Q) R μ →
        IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
          Tendsto (fun n => susceptibility (fieldPair Q) (s * R n) /
            susceptibility (fieldPair Q) (R n)) atTop (𝓝 (μ.real (observationCube s)))) := by
  have origin := actual_origin hβ hp hz hQ
  have forms := (origin.forms hβ).toDotForms
  exact ⟨origin.gibbs, forms.exists_isotropic_tangent hR, fun _ _ hv => forms.tangent_readout hR hv⟩

/-- Angular comparison on all integer lattice displacements approaching two
rotated points on a nonzero spatial sphere. -/
theorem rounded_rotation {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto (fun j => positiveFreeLaw hβ (hp j)) atTop (𝓝 Q))
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => Packet.normalization (fieldPair Q) (R n) *
      (fieldPair Q (k n) - fieldPair Q (l n))) atTop (𝓝 0) :=
  (actual_origin hβ hp hz hQ).angular hβ hR O hx hk hl

#print axioms unique_positive_free_limit
#print axioms free_boxes_tendsto
#print axioms exists_vanishing_limit
#print axioms sharp_rotation
#print axioms rounded_rotation
end IsingScaling.Rotor.HeisenbergField.PhysicalRotation
