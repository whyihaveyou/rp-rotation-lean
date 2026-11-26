import MathlibProbe.RotorHeisenbergComplexMomentBound
import MathlibProbe.RotorHeisenbergFieldCone
import MathlibProbe.RotorDotPositiveFieldContinuation

/-! # From finite Heisenberg Lee–Yang nonvanishing to spatial rotation

For the two families of physical finite free graphs, the input is
nonvanishing of the sphere-spin partition in the standard three-component
Lee–Yang cone. Disk estimates give a volume-uniform bound for two spin
insertions. Large real field uniqueness and holomorphic continuation then
identify the two finite-shape limits used in the spatial rotation theorem.
The volume, field, and scaling limits occur in that order.
-/

noncomputable section
open Filter MeasureTheory Metric
open scoped Topology
namespace IsingScaling.Rotor.HeisenbergField.FiniteLeeYangRotation
open ComplexPartition ComplexBounds FieldCone PositiveFieldContinuation
open PressureSelection LocalGibbs ModelPackets

/-- The physical finite graph statement, in the one fixed spin coordinate
system used in the published multivariate Lee–Yang theorem. -/
def FiniteLeeYang {V : Type*} [Fintype V] (J : V → V → ℝ) : Prop :=
  ∀ H : ComplexPartition.Field V, (∀ x, ‖H x 1‖ + ‖H x 2‖ < (H x 0).re) →
    partition J H ≠ 0

theorem freeDotControl_of_finiteLeeYang (W : ℕ → Type) [∀ n, Fintype (W n)]
    (J : (n : ℕ) → W n → W n → ℝ) (hLY : ∀ n, FiniteLeeYang (J n)) :
    FreeDotControl W J := by
  constructor
  · intro n z hz
    apply hLY n
    intro x
    simpa [uniform, rightHalfPlane] using hz
  · intro K hK hpos
    obtain ⟨h₀,ρ,δ,t,_,hρ,hδ,cones⟩ := disk_cones hK (fun z hz => hpos hz)
    let M := 1 + 6 / (ρ - 1)
    refine ⟨t.dotCost * (M / δ + M^2), ?_⟩
    intro n x y h hh
    apply t.norm_dot_ratio
    intro i j
    apply directional_pair_bound (J n) h₀ _ x y (t.axis i) (t.axis j) hρ hδ
    · intro z hz w hw v hv
      exact partition_ne_zero_of_cone (J n) (hLY n) _ _
        (cones h hh x y i (t.axis j) (mem_closedBall_zero_iff.mp hz)
          (mem_ball_zero_iff.mp hw).le hv)
    · intro w hw v hv
      have hc := cones h hh y y j (t.axis j) (z := 0) (w := w) (l := v)
        (by simpa using hδ.le) (mem_ball_zero_iff.mp hw).le hv
      exact partition_ne_zero_of_cone (J n) (hLY n) _ _
        (by simpa only [addAt_zero] using hc)

/-- Any weak accumulation law of the prescribed successive free-box and
positive-field limits has the zero-field DLR property and all the sharp
two-point tangent readouts, with no further hypothesis on a limiting state. -/
theorem prescribed_limit_rotation {β : ℝ} (hβ : 0 ≤ β)
    (hcube : ∀ n, FiniteLeeYang (cubeCoupling n β))
    (hrect : ∀ n, FiniteLeeYang (rectangleCoupling n β))
    {h : ℕ → ℝ} (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (inner : ∀ j, ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) :
    IsNearestGibbs 3 β Q ∧
      ∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        (∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
          VaguePairLimit (fieldPair Q) (R ∘ u) μ ∧ IsotropicPairMeasure μ) ∧
        (∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ], VaguePairLimit (fieldPair Q) R μ →
          IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
            Tendsto (fun n => susceptibility (fieldPair Q) (s * R n) /
              susceptibility (fieldPair Q) (R n)) atTop (𝓝 (μ.real (observationCube s)))) := by
  obtain ⟨gibbs, forms⟩ := gibbs_dotForms_of_complex_control hβ
    (freeDotControl_of_finiteLeeYang _ _ hcube) (freeDotControl_of_finiteLeeYang _ _ hrect)
    hp hz hQ inner
  exact ⟨gibbs, fun _ hR => ⟨forms.exists_isotropic_tangent hR, fun _ _ hv => forms.tangent_readout hR hv⟩⟩

/-- Existence of the iterated free limit and its physical reflection forms
for every vanishing positive-field schedule. -/
theorem exists_prescribed_limit {β : ℝ} (hβ : 0 ≤ β)
    (hcube : ∀ n, FiniteLeeYang (cubeCoupling n β))
    (hrect : ∀ n, FiniteLeeYang (rectangleCoupling n β))
    {h : ℕ → ℝ} (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (Q : ProbabilityMeasure (SpinField 3)) (u : ℕ → ℕ) (P : ℕ → ProbabilityMeasure (SpinField 3)),
      StrictMono u ∧ Tendsto (P ∘ u) atTop (𝓝 Q) ∧
      (∀ j, ∃ L : ℕ → ℕ, StrictMono L ∧ Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) ∧
      IsNearestGibbs 3 β Q ∧ DotForms Q :=
  exists_gibbs_dotForms_of_complex_control hβ (freeDotControl_of_finiteLeeYang _ _ hcube)
    (freeDotControl_of_finiteLeeYang _ _ hrect) hp hz

#print axioms freeDotControl_of_finiteLeeYang
#print axioms prescribed_limit_rotation
#print axioms exists_prescribed_limit
end IsingScaling.Rotor.HeisenbergField.FiniteLeeYangRotation
