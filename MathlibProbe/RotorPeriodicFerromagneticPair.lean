import MathlibProbe.RotorFreePairNonneg
import MathlibProbe.RotorPeriodicSpinState
import MathlibProbe.RotorPhysicalAdmissibleVariations

/-! # Ferromagnetic two-point positivity for the genuine periodic rotor law

At fixed amplitudes a sitewise coordinate-flip orbit averages the dot
numerator in a ferromagnetic Ising sign system. The finite matrix may have
self-couplings and parallel bonds. Use both directed copies with half
weight; these are exactly the couplings in the periodic pressure. Average
over the root and pass to a specified weak spin-state limit by continuity
of the original two-site dot observable.
-/

noncomputable section
open MeasureTheory Finset Filter
open scoped InnerProductSpace Topology
namespace IsingScaling.Rotor.PressureSelection.FerromagneticPair

theorem dotPair_nonneg (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (H : V → V → ℝ) (hH : ∀ v w, 0 ≤ H v w) (v w : V) :
    0 ≤ dotPair N H v w := by
  classical
  let μ := Measure.pi (fun _ : V => SiteReflection.surfacePrior N)
  change 0 ≤ (∫ s : V → Spin N, Real.exp (energy H s) * ⟪(s v).val,(s w).val⟫_ℝ ∂μ) /
    (∫ s : V → Spin N, Real.exp (energy H s) ∂μ)
  apply div_nonneg _ (integral_nonneg (fun _ => (Real.exp_pos _).le))
  let K (e : V × V) := H e.1 e.2/2
  have he (s : V → Spin N) : energy H s = ∑ e : V × V, K e * ⟪(s e.1).val,(s e.2).val⟫_ℝ := by
    simp only [energy,Fintype.sum_prod_type,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [K]
    ring
  simp_rw [he]
  exact surface_bond_dot_numerator_nonneg N K (fun e => div_nonneg (hH e.1 e.2) (by norm_num)) v w

theorem periodize_nonneg {V : Type*} [DecidableEq V] (D : Site → V → V)
    (J : Site → ℝ) (hJ : ∀ z, 0≤J z) (v w : V) : 0≤Seam.periodizeSeries D J v w := by
  unfold Seam.periodizeSeries
  exact tsum_nonneg fun z => by split <;> first | exact hJ z | exact le_rfl

theorem rooted_pair_nonneg (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (h0 : ∀ v, D 0 v=v) (H : V → V → ℝ) (hH : ∀ v w, 0≤H v w)
    (z : Site) : 0≤fieldPair (rootedLaw N D H) z := by
  rw [fieldPair_rootedLaw N D h0 H,averagedDot]
  exact div_nonneg (Finset.sum_nonneg fun v _ => dotPair_nonneg N H hH _ _) (Nat.cast_nonneg _)

theorem fieldPair_nonneg_of_tendsto {N : ℕ} {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (hQ : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n z, 0≤fieldPair (P n) z) (z : Site) : 0≤fieldPair Q z := by
  have h := (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot N 0 z)).continuousAt.tendsto.comp hQ
  exact ge_of_tendsto h (Eventually.of_forall fun n => hP n z)

theorem cubic_limit_pair_nonneg (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : Site → ℝ) (hJ : ∀ z, 0≤J z) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides n) J))
      atTop (𝓝 P)) (z : Site) : 0≤fieldPair P z := by
  apply fieldPair_nonneg_of_tendsto hP _ z
  exact fun n zz => rooted_pair_nonneg N _ (Seam.cubic_displacement_action (sides n)).zero _
    (periodize_nonneg _ J hJ) zz

theorem adapted_limit_pair_nonneg (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : Site → ℝ) (hJ : ∀ z, 0≤J z) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.adaptedDestination (Seam.adaptedSeries (sides n) J))
      atTop (𝓝 P)) (z : Site) : 0≤fieldPair P z := by
  apply fieldPair_nonneg_of_tendsto hP _ z
  exact fun n zz => rooted_pair_nonneg N _ (Seam.adapted_displacement_action (sides n)).zero _
    (periodize_nonneg _ J hJ) zz

/-- Positivity in the actual positive, rational-resolvent interaction used
for pressure selection. Both coupling positivity and the Gibbs correlation
on each approximant are conclusions of the construction. -/
theorem physical_base_pair_nonneg (N : ℕ) [NeZero N] {β δ : ℝ} (hβ : 0≤β) (hδ : 0≤δ)
    (sides : ℕ → ℕ) [∀ n, NeZero (sides n)] (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove
      (Seam.ordinarySeries (sides n) (PhysicalVariations.J β δ))) atTop (𝓝 P))
    (z : Site) : 0≤fieldPair P z := by
  have h := mem_of_mem_nhds (PhysicalVariations.eventually_perturbed_nonneg hβ hδ 0)
  change ∀ z, 0≤PhysicalVariations.perturbed β δ 0 0 z at h
  rw [PhysicalVariations.perturbed_zero] at h
  exact cubic_limit_pair_nonneg N sides _ h P hP z

#print axioms physical_base_pair_nonneg
#print axioms dotPair_nonneg
#print axioms cubic_limit_pair_nonneg
#print axioms adapted_limit_pair_nonneg
#print axioms fieldPair_nonneg_of_tendsto
end IsingScaling.Rotor.PressureSelection.FerromagneticPair

