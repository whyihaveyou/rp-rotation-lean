import MathlibProbe.RotorPhysicalStateSymmetries
import Mathlib.Probability.ProductMeasure

/-! # Realizing the selected rotor law on a single sequence of finite tori

At each positive auxiliary strength, the pressure comparison gives a spin
law which is approximated by finite even cubic tori and has all three
reflected two-point forms. For any prescribed strengths decreasing to zero,
choose a convergent subsequence of these infinite-volume laws. At its nth
term choose a finite torus within weak distance 1/(n+1) of that law, with
side larger than the preceding side. The resulting finite Gibbs laws
converge to the same nearest-neighbour Gibbs state. This choice precedes
all observables and all measurement scales.

In a uniqueness region one can take the ordinary periodic nearest-neighbour
coupling directly. More generally, summably small changes of its coupling
do not change the limiting law, since every subsequential limit satisfies
the same nearest-neighbour specification.
-/

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace IsingScaling.Rotor.PressureSelection.PeriodicStateRealization
open PhysicalMirrorSelection PhysicalVariations IsingRotation Packet LatticeWalk

/-- The full lattice spin field seen from a uniform root of the even cubic
torus of side 2(m+1), at the physical auxiliary coupling. -/
abbrev evenLaw (N : ℕ) [NeZero N] (β δ : ℝ) (m : ℕ) : ProbabilityMeasure (SpinField N) :=
  rootedLaw N Seam.baseMove (Seam.ordinarySeries (2*(m+1)) (J β δ))

/-- The zero-to-displacement pair readout in this finite law is exactly
the original finite periodic sphere-spin expectation. -/
theorem finite_pair_tendsto {N : ℕ} [NeZero N] {β : ℝ} {δ : ℕ → ℝ} {m : ℕ → ℕ}
    {Q : ProbabilityMeasure (SpinField N)}
    (h : Tendsto (fun n => evenLaw N β (δ n) (m n)) atTop (𝓝 Q)) (z : Site) :
    Tendsto (fun n => cubicPair N (2*(m n+1)) (J β (δ n)) z) atTop (𝓝 (fieldPair Q z)) := by
  have hp : Tendsto (fun n => fieldPair (evenLaw N β (δ n) (m n)) z) atTop (𝓝 (fieldPair Q z)) :=
    (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot N 0 z)).continuousAt.tendsto.comp h
  exact hp.congr' (Eventually.of_forall fun n =>
    fieldPair_rootedLaw N Seam.baseMove (Seam.cubic_displacement_action (2*(m n+1))).zero _ z)

private theorem diagonalize {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
    (A : ℕ → ℕ → X) (P : ℕ → X) {Q : X} (hQ : Tendsto P atTop (𝓝 Q))
    (origin : ∀ n, ∃ l : ℕ → ℕ, StrictMono l ∧ Tendsto (fun k => A n (l k)) atTop (𝓝 (P n)))
    (lower : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, lower n ≤ m n) ∧
      Tendsto (fun n => A n (m n)) atTop (𝓝 Q) := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have pick (n B : ℕ) : ∃ m, B ≤ m ∧ dist (P n) (A n m) < ε n := by
    obtain ⟨l, hl, hP⟩ := origin n
    have near := Metric.tendsto_nhds.mp hP (ε n) (hε n)
    obtain ⟨k, hB, hk⟩ := ((hl.tendsto_atTop.eventually (eventually_ge_atTop B)).and near).exists
    exact ⟨l k, hB, (dist_comm (P n) (A n (l k))).trans_lt hk⟩
  choose next bound close using pick
  let m : ℕ → ℕ := Nat.rec (next 0 (lower 0))
    (fun n prev => next (n+1) (max (lower (n+1)) (prev+1)))
  have grow : StrictMono m := strictMono_nat_of_lt_succ fun n =>
    (le_max_right _ (m n+1)).trans (bound _ _)
  refine ⟨m, grow, ?_, hQ.congr_dist ?_⟩
  · intro n
    cases n with
    | zero => exact bound _ _
    | succ k => exact (le_max_left _ (m k+1)).trans (bound _ _)
  · apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    cases n with
    | zero => exact (close _ _).le
    | succ k => exact (close _ _).le

/-- One sequence of actual finite Gibbs laws for any prescribed positive
auxiliary strengths tending to zero and any requested lower bounds on the
torus sizes. The same limit has the three pair forms, full spin symmetry,
lattice symmetry and the original nearest-neighbour DLR equations. -/
theorem exists_selected_periodic_sequence (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hzero : Tendsto δ atTop (𝓝 0)) (lower : ℕ → ℕ) :
    ∃ (Q : ProbabilityMeasure (SpinField N)) (u m : ℕ → ℕ),
      StrictMono u ∧ StrictMono m ∧ (∀ n, lower n ≤ m n) ∧
      Tendsto (fun n => evenLaw N β (δ (u n)) (m n)) atTop (𝓝 Q) ∧
      Selected N β Q ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), PeriodicHorizontal.FixedBy Q (signedPerm p s)) ∧
      InternalOrthogonal.AllInternalInvariant Q := by
  choose P origin _ _ nonnegative _ mirrors using
    (fun n => auxiliary_state_with_origin N hβ (hδ n))
  obtain ⟨Q, u, hu, hQ, hF⟩ := spinField_subsequence N P
  obtain ⟨m, hm, hlow, hfinite⟩ := diagonalize
    (fun n => evenLaw N β (δ (u n))) (P ∘ u) hQ (fun n => origin (u n)) lower
  let side (n : ℕ) := 2*(m n+1)
  let (n : ℕ) : NeZero (side n) := ⟨by dsimp [side]; omega⟩
  have hside : Tendsto side atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [side]; omega) hm.tendsto_atTop
  let K (n : ℕ) : Site → ℝ := J β (δ (u n))
  have hcoupling := (J_l1_nearest β).comp (hzero.comp hu.tendsto_atTop)
  have hpair (z : Site) : Tendsto (fun n => fieldPair (P (u n)) z) atTop (𝓝 (fieldPair Q z)) :=
    hF (fieldDot N 0 z)
  have hsigned (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
      ∀ᶠ n : ℕ in atTop, ∀ z, K n (signedPerm p s z) = K n z :=
    Eventually.of_forall fun n => J_signedPerm β (δ (u n)) p s
  refine ⟨Q, u, m, hu, hm, hlow, hfinite, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact ShiftInvariant.of_tendsto hfinite fun n =>
      rootedLaw_invariant N _ (Seam.cubic_displacement_action (side n)) _
  · exact LocalGibbs.nearest_gibbs_of_cubic_periodic N side hside K
      (fun n => l1_abs_summable (J β (δ (u n)))) β hcoupling Q hfinite
  · exact FerromagneticPair.fieldPair_nonneg_of_tendsto hQ (fun n => nonnegative (u n))
  · exact fun p s => PeriodicHorizontal.cubic_limit_pair_signedPerm N side K Q hfinite p s (hsigned p s)
  · exact ThreeMirrors.of_pair_limit (fun n => mirrors (u n)) hpair
  · exact fun p s => PeriodicHorizontal.cubic_limit_signed N side K Q hfinite p s (hsigned p s)
  · exact InternalOrthogonal.cubic_limit_invariant N side K Q hfinite

/-- At a temperature with a unique nearest-neighbour DLR law, the entire
sequence of ordinary finite-volume periodic laws converges. The periods
may be odd or even; the finite couplings may vary in lattice ℓ¹. -/
theorem periodic_tendsto_of_unique (N : ℕ) [NeZero N] {β : ℝ}
    (P : ProbabilityMeasure (SpinField N))
    (unique : ∀ Q : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β Q → Q = P)
    (side : ℕ → ℕ) [∀ n, NeZero (side n)] (hside : Tendsto side atTop atTop)
    (K : ℕ → Site → ℝ) (hK : ∀ n, Summable fun z => |K n z|)
    (hclose : Tendsto (fun n => ∑' z, |K n z - LocalGibbs.nearestCoupling β z|) atTop (𝓝 0)) :
    Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) (K n))) atTop (𝓝 P) := by
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨Q, v, hv, _, hQ, _⟩ := cubic_spin_limit N (fun n => side (f n)) (fun n => K (f n))
  have hidx := hf.comp hv.tendsto_atTop
  have hg := LocalGibbs.nearest_gibbs_of_cubic_periodic N (fun n => side (f (v n)))
    (hside.comp hidx) (fun n => K (f (v n))) (fun n => hK (f (v n))) β (hclose.comp hidx) Q hQ
  exact ⟨v, unique Q hg ▸ hQ⟩

private theorem nearest_l1_tendsto {b : ℕ → ℝ} {β : ℝ} (hb : Tendsto b atTop (𝓝 β)) :
    Tendsto (fun n => ∑' z, |LocalGibbs.nearestCoupling (b n) z - LocalGibbs.nearestCoupling β z|)
      atTop (𝓝 0) := by
  have sum (n : ℕ) : (∑' z, |LocalGibbs.nearestCoupling (b n) z - LocalGibbs.nearestCoupling β z|) =
      LocalGibbs.nearestSteps.card * |b n - β| := by
    rw [tsum_eq_sum (s := LocalGibbs.nearestSteps) (fun z hz => by simp [LocalGibbs.nearestCoupling, hz])]
    calc
      _ = ∑ _z ∈ LocalGibbs.nearestSteps, |b n - β| := by
        exact Finset.sum_congr rfl fun z hz => by simp [LocalGibbs.nearestCoupling, hz]
      _ = _ := by simp
  simp only [sum]
  simpa using ((hb.sub_const β).abs.const_mul (LocalGibbs.nearestSteps.card : ℝ))

/-- Every weak limit of the Gibbs laws at a sequence of uniqueness
temperatures inherits the original three reflected forms. The limiting
temperature may have more than one Gibbs state. -/
theorem selected_of_unique_temperature_limit (N : ℕ) [NeZero N] {b : ℕ → ℝ} {β : ℝ}
    (hb : ∀ n, 0 ≤ b n) (ht : Tendsto b atTop (𝓝 β))
    (P : ℕ → ProbabilityMeasure (SpinField N)) {Q : ProbabilityMeasure (SpinField N)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (unique : ∀ n W, LocalGibbs.IsNearestGibbs N (b n) W → W = P n) :
    Selected N β Q ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), PeriodicHorizontal.FixedBy Q (signedPerm p s)) ∧
      InternalOrthogonal.AllInternalInvariant Q := by
  have properties (n : ℕ) : Selected N (b n) (P n) ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), PeriodicHorizontal.FixedBy (P n) (signedPerm p s)) ∧
      InternalOrthogonal.AllInternalInvariant (P n) := by
    obtain ⟨W, hw, hs, hi⟩ := PhysicalStateSymmetries.exists_symmetric_state N (hb n)
    exact unique n W hw.gibbs ▸ ⟨hw, hs, hi⟩
  have hpair (z : Site) : Tendsto (fun n => fieldPair (P n) z) atTop (𝓝 (fieldPair Q z)) :=
    (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot N 0 z)).continuousAt.tendsto.comp hQ
  refine ⟨⟨ShiftInvariant.of_tendsto hQ (fun n => (properties n).1.stationary), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact LocalGibbs.nearest_gibbs_of_weak_l1_limits N hQ (fun n => LocalGibbs.nearestCoupling (b n))
      β (fun n => LocalGibbs.summable_abs_nearest (b n)) (nearest_l1_tendsto ht) (fun n => (properties n).1.gibbs)
  · exact FerromagneticPair.fieldPair_nonneg_of_tendsto hQ (fun n => (properties n).1.ferromagnetic)
  · intro p s z
    exact tendsto_nhds_unique (hpair (signedPerm p s z))
      ((hpair z).congr' (Eventually.of_forall fun n => ((properties n).1.cubic p s z).symm))
  · exact ThreeMirrors.of_pair_limit (fun n => (properties n).1.mirrors) hpair
  · exact fun p s => PeriodicHorizontal.fixed_of_tendsto hQ (signedPerm p s)
      (Eventually.of_forall fun n => (properties n).2.1 p s)
  · exact InternalOrthogonal.invariant_of_tendsto hQ (fun n => (properties n).2.2)

/-- The actual infinite product of the normalized sphere laws. -/
def independentLaw (N : ℕ) [NeZero N] : ProbabilityMeasure (SpinField N) :=
  ⟨Measure.infinitePi (fun _ : Site => SiteReflection.surfacePrior N), inferInstance⟩

private theorem zero_energy (N : ℕ) (T : Finset Site) :
    LocalGibbs.windowEnergy N T (LocalGibbs.nearestCoupling 0) (LocalGibbs.summable_abs_nearest 0) = 0 := by
  ext s
  simp [LocalGibbs.windowEnergy, LocalGibbs.nearestCoupling]

private theorem zero_read {N : ℕ} [NeZero N] (T : Finset Site) (F : C(LocalGibbs.WindowSpin N T, ℝ))
    (s : SpinField N) :
    LocalGibbs.readout T 0 (LocalGibbs.cylinderRead T F) s =
      ∫ a, F a ∂(LocalGibbs.windowPrior N T : Measure _) := by
  change (∫ t, LocalGibbs.cylinderRead T F t ∂(LocalGibbs.resample T 0 s : Measure _)) = _
  rw [LocalGibbs.resample_integral]
  have hrepl (a : LocalGibbs.WindowSpin N T) : T.restrict (LocalGibbs.replace T s a) = a :=
    funext fun i => LocalGibbs.replace_inside T s a i.property
  change (∫ a, Real.exp 0 * F (T.restrict (LocalGibbs.replace T s a)) ∂(LocalGibbs.windowPrior N T : Measure _)) /
      (∫ _a : LocalGibbs.WindowSpin N T, Real.exp 0 ∂(LocalGibbs.windowPrior N T : Measure _)) = _
  simp [hrepl]

/-- At zero inverse temperature the DLR law is uniquely the independent
sphere field. Every finite-window marginal follows by resampling exactly
that window, and these marginals determine the entire Borel measure. -/
theorem zero_gibbs_eq_product (N : ℕ) [NeZero N] (P : ProbabilityMeasure (SpinField N))
    (hP : LocalGibbs.IsNearestGibbs N 0 P) : P = independentLaw N := by
  apply ProbabilityMeasure.toMeasure_injective
  apply IsProjectiveLimit.unique (P := fun T : Finset Site => (LocalGibbs.windowPrior N T : Measure _))
  · intro T
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro F
    have hc : Continuous (T.restrict : SpinField N → LocalGibbs.WindowSpin N T) :=
      continuous_pi fun i => continuous_apply i.val
    rw [integral_map hc.measurable.aemeasurable F.continuous.aestronglyMeasurable]
    change (∫ s, LocalGibbs.cylinderRead T F.toContinuousMap s ∂(P : Measure _)) = _
    rw [hP T (LocalGibbs.cylinderRead T F.toContinuousMap), zero_energy]
    simp [zero_read, measureReal_def]
  · exact Measure.isProjectiveLimit_infinitePi (fun _ : Site => SiteReflection.surfacePrior N)

#print axioms exists_selected_periodic_sequence
#print axioms finite_pair_tendsto
#print axioms periodic_tendsto_of_unique
#print axioms selected_of_unique_temperature_limit
#print axioms zero_gibbs_eq_product

end IsingScaling.Rotor.PressureSelection.PeriodicStateRealization
