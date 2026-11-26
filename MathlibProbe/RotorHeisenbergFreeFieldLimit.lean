import MathlibProbe.RotorHeisenbergFreeCubeDLR
import MathlibProbe.RotorHighTemperatureUniqueness

/-! # Heisenberg rotation from two finite-volume dot comparisons

Along free cubes approaching a fixed positive-field law, compare the dot
at two sites to its translate rooted at zero. Compare the bond-centred
rectangle reading to the corresponding cube reading. Convergence of these
two differences to zero suffices for the spatial conclusions for every
subsequent zero-field accumulation point. Compactness supplies the required
subsequences even if the finite spin laws have several weak limits.

For a unique zero-field Gibbs law, simultaneous volume and field limits
converge to that law along every schedule. The explicit high-temperature
interval gives an instance starting solely from the finite Gibbs integrals.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace IsingScaling.Rotor.HeisenbergField
open PressureSelection LocalGibbs

/-- Two comparisons of physical finite-volume dot products at fixed sites.
The same box radius and the same on-site field occur in each difference. -/
structure FreeDotComparison (β h : ℝ) (L : ℕ → ℕ) : Prop where
  translate : ∀ x y : Site,
    Tendsto (fun n => (∫ s, fieldDot 3 x y s ∂(cubeLaw β h (L n) : Measure _)) -
      ∫ s, fieldDot 3 0 (x-y) s ∂(cubeLaw β h (L n) : Measure _)) atTop (𝓝 0)
  rectangle : ∀ x y : Site, 0 < x 0 → 0 < y 0 →
    Tendsto (fun n => BondRectangle.crossPair (fieldPrior h) β
      (BondMirror.port (L n) x) (BondMirror.port (L n) y) -
      ∫ s, fieldDot 3 x (BondMirror.reflected y) s ∂(cubeLaw β h (L n) : Measure _)) atTop (𝓝 0)

theorem FreeDotComparison.subsequence {β h : ℝ} {L j : ℕ → ℕ}
    (H : FreeDotComparison β h L) (hj : Tendsto j atTop atTop) :
    FreeDotComparison β h (L ∘ j) :=
  ⟨fun x y => (H.translate x y).comp hj, fun x y hx hy => (H.rectangle x y hx hy).comp hj⟩

/-- Comparison with the earlier input requiring a full stationary common law. -/
theorem CommonFreeLimit.dotComparison {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)}
    (H : CommonFreeLimit β h P) : FreeDotComparison β h id := by
  have test (x y : Site) : Tendsto (fun L => ∫ s, fieldDot 3 x y s ∂(cubeLaw β h L : Measure _))
      atTop (𝓝 (∫ s, fieldDot 3 x y s ∂(P : Measure _))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot 3 x y)).continuousAt.tendsto.comp H.centered
  constructor
  · intro x y
    have a := test x y
    rw [stationary_dot_integral H.stationary] at a
    have b : Tendsto (fun L => ∫ s, fieldDot 3 0 (x-y) s ∂(cubeLaw β h L : Measure _))
        atTop (𝓝 (fieldPair P (x-y))) := test 0 (x-y)
    simpa only [id_eq, sub_self] using a.sub b
  · intro x y hx hy
    have a := test x (BondMirror.reflected y)
    rw [stationary_dot_integral H.stationary] at a
    simpa only [id_eq, sub_self] using (H.rectangle x y hx hy).sub a

/-- The measured pair in every realizing cube accumulation point has the two
site and the bond reflection forms, positive type and nonnegative values. -/
theorem FreeDotComparison.forms {β h : ℝ} {L : ℕ → ℕ} {P : ProbabilityMeasure (SpinField 3)}
    (H : FreeDotComparison β h L) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hL : Tendsto L atTop atTop)
    (hP : Tendsto (fun n => cubeLaw β h (L n)) atTop (𝓝 P)) : DotForms P := by
  have test (x y : Site) : Tendsto
      (fun n => ∫ s, fieldDot 3 x y s ∂(cubeLaw β h (L n) : Measure _))
      atTop (𝓝 (∫ s, fieldDot 3 x y s ∂(P : Measure _))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot 3 x y)).continuousAt.tendsto.comp hP
  have dots (x y : Site) : (∫ s, fieldDot 3 x y s ∂(P : Measure _)) = fieldPair P (x-y) :=
    sub_eq_zero.mp (tendsto_nhds_unique ((test x y).sub (test 0 (x-y))) (H.translate x y))
  apply dotForms_of_free_pairs hβ hh hL dots
  · intro x y
    have hp := test x y
    rw [dots] at hp
    apply hp.congr'
    filter_upwards [hL.eventually (BondMirror.ev_cube x), hL.eventually (BondMirror.ev_cube y)] with n hx hy
    exact cubeLaw_pair β h (L n) hx hy
  · intro x y hx hy
    have pair := test x (BondMirror.reflected y)
    rw [dots] at pair
    simpa only [sub_add_cancel, zero_add] using (H.rectangle x y hx hy).add pair

/-- The inner field laws may each be weak limits along their own free-cube
exhaustion. Their dot comparisons suffice for all angular readouts of the
same outer weak limit that satisfies the zero-field Gibbs equations. -/
theorem gibbs_dotForms_of_free_field_limits {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 ≤ h j) (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (inner : ∀ j, ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j)) ∧ FreeDotComparison β (h j) L) :
    IsNearestGibbs 3 β Q ∧ DotForms Q := by
  choose L hL hP hdot using inner
  exact ⟨nearest_gibbs_of_vanishing_field hz hQ (fun j => field_gibbs_of_free_cube_limit (hL j) (hP j)),
    DotForms.of_weak_limit hQ (fun j => (hdot j).forms hβ (hp j) (hL j) (hP j))⟩

/-- Every realizing tangent has the spatial rotation symmetry and reads the
susceptibility of this very dot pair on each integer dilate of the cube. -/
theorem DotForms.tangent_readout {Q : ProbabilityMeasure (SpinField 3)} (H : DotForms Q)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (hv : ModelPackets.VaguePairLimit (fieldPair Q) R μ) :
    ModelPackets.IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧
      ∀ s : ℕ, 0 < s → Tendsto (fun n => susceptibility (fieldPair Q) (s * R n) /
        susceptibility (fieldPair Q) (R n)) atTop (𝓝 (μ.real (observationCube s))) := by
  have rot := H.isotropic hR hv
  exact ⟨rot, rot.real_unit_cube_eq_one H.nonnegative (by rw [fieldPair_zero]; norm_num) hR hv,
    fun _ hs => rot.susceptibility_ratio_tendsto H.nonnegative hR hv hs⟩

/-- Given the two finite dot comparisons for a prescribed field sequence,
the actual box integrals supply all spin laws and both subsequences. -/
theorem exists_free_field_limit_of_dot_comparisons {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 ≤ h j) (hz : Tendsto h atTop (𝓝 0))
    (H : ∀ j, FreeDotComparison β (h j) id) :
    ∃ (Q : ProbabilityMeasure (SpinField 3)) (u : ℕ → ℕ) (P : ℕ → ProbabilityMeasure (SpinField 3)),
      StrictMono u ∧ Tendsto (P ∘ u) atTop (𝓝 Q) ∧
      (∀ j, ∃ L : ℕ → ℕ, StrictMono L ∧ Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) ∧
      IsNearestGibbs 3 β Q ∧ DotForms Q := by
  choose P L hL hP _ using fun j => spinField_subsequence 3 (cubeLaw β (h j))
  obtain ⟨Q,u,hu,hQ,_⟩ := spinField_subsequence 3 P
  have ans := gibbs_dotForms_of_free_field_limits hβ (fun j => hp (u j)) (hz.comp hu.tendsto_atTop) hQ
    (fun j => ⟨L (u j), (hL (u j)).tendsto_atTop, hP (u j),
      (H (u j)).subsequence (hL (u j)).tendsto_atTop⟩)
  exact ⟨Q,u,P,hu,hQ,fun j => ⟨L j,hL j,hP j⟩,ans⟩

/-- For every simultaneous schedule of increasing free cubes and decreasing
field magnitudes, uniqueness of the zero-field specification determines
the full law. The sign and speed of the fields can vary with volume. -/
theorem joint_free_cube_tendsto_of_unique {β : ℝ} {Q : ProbabilityMeasure (SpinField 3)}
    (unique : ∀ P, IsNearestGibbs 3 β P → P = Q) {L : ℕ → ℕ} {h : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun j => cubeLaw β (h j) (L j)) atTop (𝓝 Q) := by
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨P,u,hu,ha,_⟩ := spinField_subsequence 3 (fun j => cubeLaw β (h (f j)) (L (f j)))
  have hi := hf.comp hu.tendsto_atTop
  have hg := gibbs_of_joint_free_cube_limit (hL.comp hi) (hz.comp hi) ha
  exact ⟨u,unique P hg ▸ ha⟩

/-- In the six-neighbour Dobrushin interval one Gibbs law, chosen before the
volume and field schedules, realizes every such limit and every two-point
rotation readout of the selected nearest-neighbour state. -/
theorem high_temperature_joint_free_cube_tendsto {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * Real.tanh β < 1) :
    ∃ Q : ProbabilityMeasure (SpinField 3), PhysicalMirrorSelection.Selected 3 β Q ∧
      ∀ (L : ℕ → ℕ) (h : ℕ → ℝ), Tendsto L atTop atTop → Tendsto h atTop (𝓝 0) →
        Tendsto (fun j => cubeLaw β (h j) (L j)) atTop (𝓝 Q) := by
  obtain ⟨Q,H⟩ := PhysicalMirrorSelection.exists_state 3 hβ
  exact ⟨Q,H,fun _ _ hL hz => joint_free_cube_tendsto_of_unique
    (fun _ hP => HighTemperature.nearest_gibbs_eq_tanh hβ hsmall hP H.gibbs) hL hz⟩

#print axioms gibbs_dotForms_of_free_field_limits
#print axioms DotForms.tangent_readout
#print axioms exists_free_field_limit_of_dot_comparisons
#print axioms high_temperature_joint_free_cube_tendsto
end IsingScaling.Rotor.HeisenbergField
