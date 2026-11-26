import MathlibProbe.RotorHeisenbergFieldFinite
import MathlibProbe.RotorLocalGibbsLimit

/-! # The nearest-neighbour Heisenberg specification as the field vanishes

The uniform source adds h times the first spin coordinate at every
replacement site. On a window Λ its absolute value is at most |Λ| |h|.
Comparing the two normalized Boltzmann integrals controls the error in
each local conditional expectation uniformly in all exterior spins. Weak
limits of positive-field Gibbs laws at h tending to zero therefore obey
the original zero-field DLR equations.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace IsingScaling.Rotor.HeisenbergField
open PressureSelection LocalGibbs

/-- Field energy contributed by exactly the sites being resampled. -/
def windowSource (h : ℝ) (Λ : Finset Site) : C(SpinField 3, ℝ) where
  toFun s := ∑ x : Λ, siteField h (s x)
  continuous_toFun := continuous_finsetSum _ fun x _ => by unfold siteField; fun_prop

abbrev nearestEnergy (β : ℝ) (Λ : Finset Site) : C(SpinField 3, ℝ) :=
  windowEnergy 3 Λ (nearestCoupling β) (summable_abs_nearest β)

/-- The field and the pair interaction in a finite window, using the
ordinary sphere surface law for every replacement spin. -/
def localFieldEnergy (β h : ℝ) (Λ : Finset Site) : C(SpinField 3, ℝ) :=
  nearestEnergy β Λ + windowSource h Λ

theorem abs_windowSource (h : ℝ) (Λ : Finset Site) (s : SpinField 3) :
    |windowSource h Λ s| ≤ Λ.card * |h| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact (Finset.sum_le_sum (s := (Finset.univ : Finset Λ)) (fun x _ => abs_siteField_le h (s x))).trans_eq
    (by simp)

/-- Oscillation under any two records of replacement and exterior spins. -/
theorem windowSource_oscillation (h : ℝ) (Λ : Finset Site) (s t : SpinField 3) :
    |windowSource h Λ s - windowSource h Λ t| ≤ 2 * (Λ.card * |h|) := by
  simpa only [two_mul] using (abs_sub _ _).trans (add_le_add (abs_windowSource h Λ s) (abs_windowSource h Λ t))

theorem field_readout_error (β h : ℝ) (Λ : Finset Site) (F : C(SpinField 3, ℝ)) (s : SpinField 3) :
    |readout Λ (localFieldEnergy β h Λ) F s - readout Λ (nearestEnergy β Λ) F s| ≤
      (Real.exp (2 * (Λ.card * |h|)) - 1) * (2*‖F‖) := by
  apply readout_error _ _ _ _ (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg h)) _ s
  intro t
  simpa only [localFieldEnergy, ContinuousMap.add_apply, add_sub_cancel_left] using abs_windowSource h Λ t

/-- DLR for the literal nearest-neighbour interaction with the added
uniform source. The expectation tests are all continuous field readings. -/
def IsFieldGibbs (β h : ℝ) (P : ProbabilityMeasure (SpinField 3)) : Prop :=
  ∀ (Λ : Finset Site) (F : C(SpinField 3, ℝ)), (∫ s, F s ∂(P : Measure _)) =
    ∫ s, readout Λ (localFieldEnergy β h Λ) F s ∂(P : Measure _)

/-- For each fixed window the positive-field resampling equation need
only hold eventually. This permits the volume and field to vary together. -/
theorem nearest_gibbs_of_eventual_field_windows {β : ℝ} {h : ℕ → ℝ} (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (hg : ∀ (Λ : Finset Site) (F : C(SpinField 3, ℝ)), ∀ᶠ n in atTop,
      (∫ s, F s ∂(P n : Measure _)) =
        ∫ s, readout Λ (localFieldEnergy β (h n) Λ) F s ∂(P n : Measure _)) :
    IsNearestGibbs 3 β Q := by
  intro Λ F
  let B := readout Λ (nearestEnergy β Λ) F
  let A (n : ℕ) := readout Λ (localFieldEnergy β (h n) Λ) F
  have bound : ∀ᶠ n : ℕ in atTop, |(∫ s, F s ∂(P n : Measure _)) - ∫ s, B s ∂(P n : Measure _)| ≤
      (Real.exp (2 * (Λ.card * |h n|)) - 1) * (2*‖F‖) := by
    filter_upwards [hg Λ F] with n hn
    rw [hn]
    change |(∫ s, A n s ∂(P n : Measure _)) - ∫ s, B s ∂(P n : Measure _)| ≤ _
    rw [← integral_sub ((A n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (B.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    simpa [Real.norm_eq_abs, measureReal_def] using norm_integral_le_of_norm_le_const
      (μ := (P n : Measure _)) (f := fun s => A n s - B s)
      (Eventually.of_forall fun s => field_readout_error β (h n) Λ F s)
  have err := (((hz.abs.const_mul (Λ.card : ℝ)).const_mul 2).rexp.sub_const 1).mul_const (2*‖F‖)
  have vanishes : Tendsto (fun n => (∫ s, F s ∂(P n : Measure _)) - ∫ s, B s ∂(P n : Measure _))
      atTop (𝓝 0) := squeeze_zero_norm' bound (by simpa using err)
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hQ
  have hB := (ProbabilityMeasure.continuous_integral_continuousMap B).continuousAt.tendsto.comp hQ
  exact sub_eq_zero.mp (tendsto_nhds_unique (hF.sub hB) vanishes)

theorem nearest_gibbs_of_vanishing_field {β : ℝ} {h : ℕ → ℝ} (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q)) (hg : ∀ n, IsFieldGibbs β (h n) (P n)) :
    IsNearestGibbs 3 β Q :=
  nearest_gibbs_of_eventual_field_windows hz hQ fun Λ F => Eventually.of_forall fun n => hg n Λ F

#print axioms windowSource_oscillation
#print axioms field_readout_error
#print axioms nearest_gibbs_of_vanishing_field

end IsingScaling.Rotor.HeisenbergField
