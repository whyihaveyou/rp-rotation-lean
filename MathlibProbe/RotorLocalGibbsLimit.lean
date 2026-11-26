import MathlibProbe.RotorPeriodicFirstVariation
import MathlibProbe.RotorPeriodicLocalCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Constructions.Projective

/-! # Finite-window Gibbs resampling for lattice sphere spins

Fix a finite window. Replace all spins in it by an independent sample from
the product surface law, and weight the sample by the exponential of every
pair interaction meeting the window. For a symmetric interaction the bonds
internal to the window carry a factor one half in the directed site sum.
Every external spin is left at its original value. Absolute summability
makes this energy a uniformly convergent series of continuous functions.
Consequently the normalized integral sends continuous tests to continuous
tests. A change of interaction of norm d changes the window energy by at
most |window| d, uniformly in both the external and the replacement spins.
The exponential and its normalizing integral give a factor exp(2|window|d)
in either direction on positive reads. Weak convergence can then be passed
through the local specification. All measures use the normalized surface
law of the actual unit sphere, including the two-point sphere at N=1.

For a rooted cubic periodic field, a fixed finite-range collar embeds at
every origin once the period is large. In that collar the torus energy
differs from the lattice window energy by an exterior-only constant, so
the normalized conditional readings agree. Cylinder projections determine
the whole Borel law. For a summable interaction, truncate on growing
cubes and use the window-size bound before taking the weak limit. This
also treats an outer sequence of auxiliary couplings converging to the
nearest-neighbour interaction on the original lattice.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace IsingScaling.Rotor.PressureSelection.LocalGibbs

abbrev WindowSpin (N : ℕ) (Λ : Finset Site) := (x : Λ) → Spin N

def windowPrior (N : ℕ) [NeZero N] (Λ : Finset Site) : ProbabilityMeasure (WindowSpin N Λ) :=
  ⟨Measure.pi (fun _ : Λ => SiteReflection.surfacePrior N), inferInstance⟩

def replace {N : ℕ} (Λ : Finset Site) (s : SpinField N) (a : WindowSpin N Λ) (x : Site) :
    Spin N := if h : x ∈ Λ then a ⟨x,h⟩ else s x

theorem replace_inside {N : ℕ} (Λ : Finset Site) (s : SpinField N) (a : WindowSpin N Λ)
    {x : Site} (hx : x ∈ Λ) : replace Λ s a x = a ⟨x,hx⟩ := by simp [replace,hx]

theorem replace_outside {N : ℕ} (Λ : Finset Site) (s : SpinField N) (a : WindowSpin N Λ)
    {x : Site} (hx : x ∉ Λ) : replace Λ s a x = s x := by simp [replace,hx]

theorem replace_continuous {N : ℕ} (Λ : Finset Site) :
    Continuous (fun p : SpinField N × WindowSpin N Λ => replace Λ p.1 p.2) := by
  apply continuous_pi
  intro x
  by_cases hx : x ∈ Λ
  · simp only [replace_inside _ _ _ hx]
    exact (continuous_apply (⟨x,hx⟩ : Λ)).comp continuous_snd
  · simp only [replace_outside _ _ _ hx]
    exact (continuous_apply x).comp continuous_fst

private def bondCoeff (Λ : Finset Site) (x z : Site) : ℝ := if x+z ∈ Λ then 1/2 else 1

private def bond (N : ℕ) (Λ : Finset Site) (x z : Site) : C(SpinField N, ℝ) :=
  (ContinuousMap.const _ (bondCoeff Λ x z)) * fieldDot N x (x+z)

private theorem abs_bond (N : ℕ) (Λ : Finset Site) (x z : Site) (s : SpinField N) :
    |bond N Λ x z s| ≤ 1 := by
  change |bondCoeff Λ x z * ⟪(s x).val, (s (x+z)).val⟫_ℝ| ≤ 1
  rw [abs_mul]
  have hm := abs_real_inner_le_norm (s x).val (s (x+z)).val
  simp only [mem_sphere_zero_iff_norm.mp (s x).property,
    mem_sphere_zero_iff_norm.mp (s (x+z)).property, one_mul] at hm
  exact (mul_le_mul_of_nonneg_left hm (abs_nonneg _)).trans (by
    unfold bondCoeff
    split_ifs <;> norm_num)

/-- For an even coupling this directed sum gives each undirected pair
touching the window its physical weight. -/
def windowEnergy (N : ℕ) (Λ : Finset Site) (J : Site → ℝ) (hJ : Summable fun z => |J z|) :
    C(SpinField N, ℝ) where
  toFun s := ∑ x : Λ, ∑' z, J z * bond N Λ x.val z s
  continuous_toFun := continuous_finsetSum _ (fun x _ =>
    continuous_tsum (fun z => continuous_const.mul (bond N Λ x.val z).continuous) hJ
      (fun z s => by rw [Real.norm_eq_abs, abs_mul]
                     exact mul_le_of_le_one_right (abs_nonneg _) (abs_bond N Λ x.val z s)))

private theorem summableBond (N : ℕ) (Λ : Finset Site) (x : Site) (s : SpinField N)
    {J : Site → ℝ} (hJ : Summable fun z => |J z|) : Summable fun z => J z*bond N Λ x z s :=
  hJ.of_norm_bounded (fun z => by rw [Real.norm_eq_abs, abs_mul]
                                  exact mul_le_of_le_one_right (abs_nonneg _) (abs_bond N Λ x z s))

theorem energy_error (N : ℕ) (Λ : Finset Site) (J K : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hK : Summable fun z => |K z|) (s : SpinField N) :
    |windowEnergy N Λ J hJ s - windowEnergy N Λ K hK s| ≤
      Λ.card * ∑' z, |J z-K z| := by
  change |(∑ x : Λ, ∑' z, J z*bond N Λ x.val z s) - ∑ x : Λ, ∑' z, K z*bond N Λ x.val z s| ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have habs : Summable fun z => |J z-K z| := (hJ.of_abs.sub hK.of_abs).abs
  calc
    _ ≤ ∑ _ : Λ, ∑' z, |J z-K z| := by
      apply Finset.sum_le_sum
      intro x _
      rw [← (summableBond N Λ x.val s hJ).tsum_sub (summableBond N Λ x.val s hK)]
      simp_rw [← sub_mul]
      have hs := (summableBond N Λ x.val s habs).abs
      calc
        _ ≤ ∑' z, |(J z-K z)*bond N Λ x.val z s| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
            (f := fun z => (J z-K z)*bond N Λ x.val z s) (by simpa only [Real.norm_eq_abs] using hs)
        _ ≤ _ := hs.tsum_le_tsum (fun z => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (abs_bond N Λ x.val z s)) habs
    _ = _ := by simp

private def partition {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ))
    (s : SpinField N) : ℝ :=
  ∫ a, Real.exp (E (replace Λ s a)) ∂(windowPrior N Λ : Measure _)

private theorem continuousReplaceFixed {N : ℕ} (Λ : Finset Site) (s : SpinField N) :
    Continuous (replace Λ s) :=
  (replace_continuous Λ).comp (continuous_const.prodMk continuous_id)

private theorem partition_pos {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ))
    (s : SpinField N) : 0 < partition Λ E s :=
  integral_exp_pos ((E.continuous.comp (continuousReplaceFixed Λ s)).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

/-- Replacement spins use the normalized Boltzmann density against an actual
product of unit-sphere priors, and the pushforward preserves the outside. -/
def resample {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ))
    (s : SpinField N) : ProbabilityMeasure (SpinField N) :=
  let θ : Measure (WindowSpin N Λ) := windowPrior N Λ
  let aP : ProbabilityMeasure (WindowSpin N Λ) := ⟨θ.tilted (fun a => E (replace Λ s a)),
    isProbabilityMeasure_tilted ((E.continuous.comp (continuousReplaceFixed Λ s)).rexp.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))⟩
  aP.map (continuousReplaceFixed Λ s).measurable.aemeasurable

private def read {N : ℕ} [NeZero N] (Λ : Finset Site) (E F : C(SpinField N, ℝ))
    (s : SpinField N) : ℝ :=
  (∫ a, Real.exp (E (replace Λ s a)) * F (replace Λ s a) ∂(windowPrior N Λ : Measure _)) /
    partition Λ E s

theorem resample_integral {N : ℕ} [NeZero N] (Λ : Finset Site) (E F : C(SpinField N, ℝ))
    (s : SpinField N) :
    (∫ t, F t ∂(resample Λ E s : Measure _)) = read Λ E F s := by
  change (∫ t, F t ∂(Measure.map (replace Λ s) ((windowPrior N Λ : Measure _).tilted _))) = _
  rw [integral_map (continuousReplaceFixed Λ s).measurable.aemeasurable
    F.continuous.aestronglyMeasurable, integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div, read, partition]

private theorem integral_continuous {N : ℕ} [NeZero N] (Λ : Finset Site)
    (f : SpinField N → WindowSpin N Λ → ℝ) (hf : Continuous f.uncurry) :
    Continuous fun s => ∫ a, f s a ∂(windowPrior N Λ : Measure _) := by
  simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
    (μ := (windowPrior N Λ : Measure _)) hf isCompact_univ

/-- Continuous action of the physical resampling operator on every continuous
field observable, including all continuous cylinder tests. -/
def readout {N : ℕ} [NeZero N] (Λ : Finset Site) (E F : C(SpinField N, ℝ)) : C(SpinField N, ℝ) where
  toFun s := ∫ t, F t ∂(resample Λ E s : Measure _)
  continuous_toFun := by
    simp only [resample_integral, read]
    apply Continuous.div
    · apply integral_continuous
      exact ((E.continuous.comp (replace_continuous Λ)).rexp).mul (F.continuous.comp (replace_continuous Λ))
    · apply integral_continuous
      exact (E.continuous.comp (replace_continuous Λ)).rexp
    · exact fun s => (partition_pos Λ E s).ne'

theorem continuous_resample {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ)) :
    Continuous (resample Λ E) :=
  ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
    (fun F => (readout Λ E F).continuous)

private def siteStep (i : Fin 3) (b : Bool) : Site := Pi.single i (if b then 1 else -1)

def nearestSteps : Finset Site := Finset.univ.image (fun p : Fin 3 × Bool => siteStep p.1 p.2)

def nearestCoupling (β : ℝ) (z : Site) : ℝ := if z ∈ nearestSteps then β else 0

theorem summable_abs_nearest (β : ℝ) : Summable (fun z => |nearestCoupling β z|) := by
  apply summable_of_ne_finset_zero (s := nearestSteps)
  intro z hz
  simp [nearestCoupling,hz]

theorem mem_nearestSteps_iff_latticeDistance (z : Site) :
    z ∈ nearestSteps ↔ latticeDistance 0 z = 1 := by
  have dist (q : Site) : latticeDistance 0 q = ∑ i, (q i).natAbs := by
    simp [latticeDistance]
  rw [dist]
  constructor
  · intro hz
    obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.sum_eq_single i]
    · cases b <;> simp [siteStep]
    · intro j _ hj
      simp [siteStep,Pi.single_eq_of_ne hj]
    · simp
  · intro h
    obtain ⟨i,hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra! h0
      simp [h0] at h
    have hp : 0 < (z i).natAbs := Int.natAbs_pos.mpr hi
    have hi' : (z i).natAbs ≤ 1 := h ▸ Finset.single_le_sum (f := fun k => (z k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hrest (j : Fin 3) (hj : j ≠ i) : z j = 0 := by
      have ht := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (z k).natAbs)
        (Finset.subset_univ ({i,j} : Finset (Fin 3))) (fun _ _ _ => Nat.zero_le _)
      simp [Ne.symm hj,h] at ht
      omega
    have pick (b : Bool) (hb : z i = if b then 1 else -1) : z ∈ nearestSteps := by
      refine Finset.mem_image.mpr ⟨(i,b),Finset.mem_univ _,?_⟩
      funext j
      by_cases hj : j=i
      · subst j
        simp [siteStep,hb]
      · simp [siteStep,Pi.single_eq_of_ne hj,hrest j hj]
    rcases (show z i=1 ∨ z i= -1 by omega) with hpos | hneg
    · exact pick true hpos
    · exact pick false hneg

theorem nearestCoupling_at_pair (β : ℝ) (x y : Site) :
    nearestCoupling β (y-x) = if latticeDistance x y = 1 then β else 0 := by
  have h : latticeDistance 0 (y-x) = latticeDistance x y := by
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.sub_apply]
  simp only [nearestCoupling,mem_nearestSteps_iff_latticeDistance,h]

def nearestResample (N : ℕ) [NeZero N] (Λ : Finset Site) (β : ℝ) :
    SpinField N → ProbabilityMeasure (SpinField N) :=
  resample Λ (windowEnergy N Λ (nearestCoupling β) (summable_abs_nearest β))

theorem continuous_nearestResample (N : ℕ) [NeZero N] (Λ : Finset Site) (β : ℝ) :
    Continuous (nearestResample N Λ β) := continuous_resample _ _

private theorem intCont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : ProbabilityMeasure X) {f : X → ℝ} (h : Continuous f) :
    Integrable f (P : Measure X) :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem exp_le (a b d : ℝ) (h : |a-b| ≤ d) : Real.exp a ≤ Real.exp d*Real.exp b := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).2])

private theorem partition_compare {N : ℕ} [NeZero N] (Λ : Finset Site)
    (E K : C(SpinField N, ℝ)) {d : ℝ} (h : ∀ s, |E s-K s| ≤ d) (s : SpinField N) :
    partition Λ E s ≤ Real.exp d * partition Λ K s := by
  unfold partition
  rw [← integral_const_mul]
  apply integral_mono (intCont _ (E.continuous.comp (continuousReplaceFixed Λ s)).rexp)
    (intCont _ (continuous_const.mul (K.continuous.comp (continuousReplaceFixed Λ s)).rexp))
  exact fun a => exp_le _ _ _ (h (replace Λ s a))

private theorem readout_compare {N : ℕ} [NeZero N] (Λ : Finset Site) (E K F : C(SpinField N, ℝ))
    {d : ℝ} (h : ∀ s, |E s-K s| ≤ d) (hF : ∀ s, 0 ≤ F s) (s : SpinField N) :
    readout Λ E F s ≤ Real.exp (2*d) * readout Λ K F s := by
  let I (A : C(SpinField N, ℝ)) :=
    ∫ a, Real.exp (A (replace Λ s a))*F (replace Λ s a) ∂(windowPrior N Λ : Measure _)
  have hpos (A : C(SpinField N, ℝ)) : 0 ≤ I A :=
    integral_nonneg (fun a => mul_nonneg (Real.exp_pos _).le (hF (replace Λ s a)))
  have hi : I E ≤ Real.exp d*I K := by
    unfold I
    rw [← integral_const_mul]
    apply integral_mono
      (intCont _ ((E.continuous.comp (continuousReplaceFixed Λ s)).rexp.mul
        (F.continuous.comp (continuousReplaceFixed Λ s))))
      (intCont _ (continuous_const.mul ((K.continuous.comp (continuousReplaceFixed Λ s)).rexp.mul
        (F.continuous.comp (continuousReplaceFixed Λ s)))))
    intro a
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (exp_le _ _ _ (h (replace Λ s a))) (hF _)
  have hz := partition_compare Λ K E (fun a => by rw [abs_sub_comm]; exact h a) s
  change (∫ t, F t ∂(resample Λ E s : Measure _)) ≤ _*(∫ t, F t ∂(resample Λ K s : Measure _))
  rw [resample_integral, resample_integral]
  change I E / partition Λ E s ≤ Real.exp (2*d) * (I K / partition Λ K s)
  rw [← mul_div_assoc, div_le_div_iff₀ (partition_pos Λ E s) (partition_pos Λ K s)]
  calc
    _ ≤ (Real.exp d * I K) * (Real.exp d * partition Λ E s) :=
      mul_le_mul hi hz (partition_pos Λ K s).le (mul_nonneg (Real.exp_pos _).le (hpos K))
    _ = _ := by rw [two_mul,Real.exp_add]; ring

theorem readout_nonnegative_error {N : ℕ} [NeZero N] (Λ : Finset Site) (E K F : C(SpinField N, ℝ))
    {d M : ℝ} (hd : 0 ≤ d) (h : ∀ s, |E s-K s| ≤ d)
    (hF : ∀ s, 0 ≤ F s ∧ F s ≤ M) (s : SpinField N) :
    |readout Λ E F s - readout Λ K F s| ≤ (Real.exp (2*d)-1)*M := by
  have hu (A : C(SpinField N, ℝ)) : readout Λ A F s ≤ M := by
    change (∫ t, F t ∂(resample Λ A s : Measure _)) ≤ M
    calc
      _ ≤ ∫ _ : SpinField N, M ∂(resample Λ A s : Measure _) :=
        integral_mono (intCont _ F.continuous) (integrable_const _) (fun a => (hF a).2)
      _ = _ := by simp
  have hc : 0 ≤ Real.exp (2*d)-1 := sub_nonneg.mpr (Real.one_le_exp (by linarith))
  have upper (A B : C(SpinField N, ℝ)) (h' : ∀ a, |A a-B a| ≤ d) :
      readout Λ A F s - readout Λ B F s ≤ (Real.exp (2*d)-1)*M := calc
    _ ≤ (Real.exp (2*d)-1)*readout Λ B F s := by
      linarith [readout_compare Λ A B F h' (fun a => (hF a).1) s]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hu B) hc
  exact abs_sub_le_iff.mpr ⟨upper E K h,upper K E (fun a => by rw [abs_sub_comm]; exact h a)⟩

private theorem readout_add_const {N : ℕ} [NeZero N] (Λ : Finset Site) (E F : C(SpinField N, ℝ))
    (a : ℝ) (s : SpinField N) :
    readout Λ E (F+ContinuousMap.const _ a) s = readout Λ E F s + a := by
  change (∫ t, F t+a ∂(resample Λ E s : Measure _)) = _ + a
  rw [integral_add (intCont _ F.continuous) (integrable_const _)]
  simp [readout]

theorem readout_error {N : ℕ} [NeZero N] (Λ : Finset Site) (E K F : C(SpinField N, ℝ))
    {d : ℝ} (hd : 0 ≤ d) (h : ∀ s, |E s-K s| ≤ d) (s : SpinField N) :
    |readout Λ E F s - readout Λ K F s| ≤ (Real.exp (2*d)-1)*(2*‖F‖) := by
  have hb (a : SpinField N) := abs_le.mp (show |F a| ≤ ‖F‖ from F.norm_coe_le_norm a)
  have hh := readout_nonnegative_error Λ E K (F+ContinuousMap.const _ ‖F‖) hd h
    (M := 2*‖F‖) (fun a => by change 0 ≤ F a+‖F‖ ∧ F a+‖F‖ ≤ _; constructor <;> linarith [hb a]) s
  simpa only [readout_add_const, add_sub_add_right_eq_sub] using hh

theorem interaction_readout_error {N : ℕ} [NeZero N] (Λ : Finset Site) (J K : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hK : Summable fun z => |K z|) (F : C(SpinField N, ℝ))
    (s : SpinField N) :
    |readout Λ (windowEnergy N Λ J hJ) F s - readout Λ (windowEnergy N Λ K hK) F s| ≤
      (Real.exp (2*(Λ.card * ∑' z, |J z-K z|))-1)*(2*‖F‖) :=
  readout_error _ _ _ _ (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun _ => abs_nonneg _))
    (energy_error N Λ J K hJ hK) _

/-- DLR invariance tested on all continuous observables of the compact
spin-field space. Exterior factors are preserved by the local update. -/
def IsGibbs (N : ℕ) [NeZero N] (J : Site → ℝ) (hJ : Summable fun z => |J z|)
    (P : ProbabilityMeasure (SpinField N)) : Prop :=
  ∀ (Λ : Finset Site) (F : C(SpinField N, ℝ)),
    (∫ s, F s ∂(P : Measure _)) = ∫ s, readout Λ (windowEnergy N Λ J hJ) F s ∂(P : Measure _)

def IsNearestGibbs (N : ℕ) [NeZero N] (β : ℝ) (P : ProbabilityMeasure (SpinField N)) : Prop :=
  IsGibbs N (nearestCoupling β) (summable_abs_nearest β) P

/-- DLR identities are closed under simultaneous weak spin-law and uniform
ℓ¹-coupling limits. The input may already have a vanishing local resampling
error, as happens when a finite-volume window only sees boundary tails. -/
theorem gibbs_of_approximation (N : ℕ) [NeZero N] {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (hQ : Tendsto P atTop (𝓝 Q))
    (K : ℕ → Site → ℝ) (J : Site → ℝ) (hK : ∀ n, Summable fun z => |K n z|)
    (hJ : Summable fun z => |J z|)
    (hclose : Tendsto (fun n => ∑' z, |K n z-J z|) atTop (𝓝 0))
    (hid : ∀ (Λ : Finset Site) (F : C(SpinField N, ℝ)),
      Tendsto (fun n => (∫ s, F s ∂(P n : Measure _)) -
        ∫ s, readout Λ (windowEnergy N Λ (K n) (hK n)) F s ∂(P n : Measure _)) atTop (𝓝 0)) :
    IsGibbs N J hJ Q := by
  intro Λ F
  let A (n : ℕ) := readout Λ (windowEnergy N Λ (K n) (hK n)) F
  let B := readout Λ (windowEnergy N Λ J hJ) F
  let err (n : ℕ) := (Real.exp (2*(Λ.card * ∑' z, |K n z-J z|))-1)*(2*‖F‖)
  have hE : Tendsto err atTop (𝓝 0) := by
    have h := (((hclose.const_mul (Λ.card : ℝ)).const_mul 2).rexp.sub_const 1).mul_const (2*‖F‖)
    simpa only [mul_zero,Real.exp_zero,sub_self,zero_mul] using h
  have hi (n : ℕ) :
      |(∫ s, A n s ∂(P n : Measure _)) - ∫ s, B s ∂(P n : Measure _)| ≤ err n := by
    rw [← integral_sub (intCont _ (A n).continuous) (intCont _ B.continuous)]
    simpa [Real.norm_eq_abs, measureReal_def] using
      norm_integral_le_of_norm_le_const (μ := (P n : Measure _))
        (f := fun s => A n s-B s) (C := err n)
        (Eventually.of_forall fun s => interaction_readout_error Λ (K n) J (hK n) hJ F s)
  have hdiff : Tendsto (fun n => (∫ s, A n s ∂(P n : Measure _)) -
      ∫ s, B s ∂(P n : Measure _)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => hi n) hE
  have he := (hid Λ F).add hdiff
  simp only [A, sub_add_sub_cancel, add_zero] at he
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hQ
  have hB := (ProbabilityMeasure.continuous_integral_continuousMap B).continuousAt.tendsto.comp hQ
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique (hF.sub hB) he

theorem nearest_gibbs_of_weak_l1_limits (N : ℕ) [NeZero N] {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (hQ : Tendsto P atTop (𝓝 Q))
    (K : ℕ → Site → ℝ) (β : ℝ) (hK : ∀ n, Summable fun z => |K n z|)
    (hclose : Tendsto (fun n => ∑' z, |K n z-nearestCoupling β z|) atTop (𝓝 0))
    (hg : ∀ n, IsGibbs N (K n) (hK n) (P n)) : IsNearestGibbs N β Q := by
  apply gibbs_of_approximation N hQ K _ hK _ hclose
  intro Λ F
  simpa only [fun n => (hg n Λ F).symm, sub_self] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

open ProbabilityTheory

/-- Borel Markov kernel with the same physical surface-spin conditional. -/
def kernel {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ)) :
    Kernel (SpinField N) (SpinField N) where
  toFun s := resample Λ E s
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    let θ : Measure (WindowSpin N Λ) := windowPrior N Λ
    let g (p : SpinField N × WindowSpin N Λ) :=
      ENNReal.ofReal (Real.exp (E (replace Λ p.1 p.2)) / partition Λ E p.1)
    have hZ : Continuous (partition Λ E) :=
      integral_continuous Λ _ (E.continuous.comp (replace_continuous Λ)).rexp
    have hg : Measurable g := (((E.continuous.comp (replace_continuous Λ)).rexp.measurable.div
      (hZ.measurable.comp measurable_fst))).ennreal_ofReal
    let T : Set (SpinField N × WindowSpin N Λ) := (fun p => replace Λ p.1 p.2) ⁻¹' B
    have hT : MeasurableSet T := (replace_continuous Λ).measurable hB
    have hi := (hg.indicator hT).lintegral_prod_right' (ν := θ)
    convert hi using 1
    funext s
    change (Measure.map (replace Λ s) (θ.tilted (fun a => E (replace Λ s a)))) B =
      ∫⁻ a, T.indicator g (s,a) ∂θ
    rw [Measure.map_apply (continuousReplaceFixed Λ s).measurable hB,
      tilted_apply' _ _ ((continuousReplaceFixed Λ s).measurable hB),
      ← lintegral_indicator ((continuousReplaceFixed Λ s).measurable hB)]
    apply lintegral_congr
    intro a
    by_cases ha : replace Λ s a ∈ B <;> simp [T,g,ha,partition,θ]

instance kernel_markov {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ)) :
    IsMarkovKernel (kernel Λ E) where
  isProbabilityMeasure s := (resample Λ E s).prop

theorem readout_outside_factor {N : ℕ} [NeZero N] (Λ : Finset Site)
    (E G F : C(SpinField N, ℝ))
    (hg : ∀ s t : SpinField N, (∀ x ∉ Λ, s x = t x) → G s = G t) (s : SpinField N) :
    readout Λ E (G*F) s = G s * readout Λ E F s := by
  change (∫ t, (G*F) t ∂(resample Λ E s : Measure (SpinField N))) =
    G s * ∫ t, F t ∂(resample Λ E s : Measure (SpinField N))
  simp only [resample_integral, read]
  have hrep (a : WindowSpin N Λ) : G (replace Λ s a) = G s :=
    hg _ _ (fun x hx => replace_outside Λ s a hx)
  simp only [ContinuousMap.mul_apply, hrep]
  simp_rw [mul_left_comm _ (G s)]
  rw [integral_const_mul, mul_div_assoc]

/-- Equality on all continuous physical field tests is equivalent to
invariance of the actual full Borel spin law under the window kernel. -/
theorem isGibbs_iff_kernel (N : ℕ) [NeZero N] (J : Site → ℝ) (hJ : Summable fun z => |J z|)
    (P : ProbabilityMeasure (SpinField N)) :
    IsGibbs N J hJ P ↔ ∀ Λ, kernel Λ (windowEnergy N Λ J hJ) ∘ₘ (P : Measure (SpinField N)) = P := by
  have hint (Λ : Finset Site) (F : C(SpinField N, ℝ)) :
      (∫ s, F s ∂(kernel Λ (windowEnergy N Λ J hJ) ∘ₘ (P : Measure (SpinField N)))) =
        ∫ s, readout Λ (windowEnergy N Λ J hJ) F s ∂(P : Measure _) := by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp
      (F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    rfl
  constructor
  · intro h Λ
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro F
    exact (hint Λ F.toContinuousMap).trans (h Λ F.toContinuousMap).symm
  · intro h Λ F
    simpa only [h Λ] using hint Λ F

section FiniteConditional

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y] [LocallyCompactSpace Y] [FirstCountableTopology Y]

/-- The inside-variable conditional for a compact product of two spin blocks. -/
private def conditionalAt (θ : ProbabilityMeasure X) (E F : C(X × Y, ℝ)) (y : Y) : ℝ :=
  (∫ a, Real.exp (E (a,y)) * F (a,y) ∂(θ : Measure X)) /
    ∫ a, Real.exp (E (a,y)) ∂(θ : Measure X)

private theorem insideZ_pos (θ : ProbabilityMeasure X) (E : C(X × Y, ℝ)) (y : Y) :
    0 < ∫ a, Real.exp (E (a,y)) ∂(θ : Measure X) :=
  integral_exp_pos (intCont _ ((E.continuous.comp (continuous_id.prodMk continuous_const)).rexp))

private theorem conditionalAt_continuous (θ : ProbabilityMeasure X) (E F : C(X × Y, ℝ)) :
    Continuous (conditionalAt θ E F) := by
  unfold conditionalAt
  apply Continuous.div
  · simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
      (μ := (θ : Measure X)) (f := fun y a => Real.exp (E (a,y)) * F (a,y))
      ((E.continuous.rexp.mul F.continuous).comp continuous_swap) isCompact_univ
  · simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
      (μ := (θ : Measure X)) (f := fun y a => Real.exp (E (a,y)))
      (E.continuous.rexp.comp continuous_swap) isCompact_univ
  · exact fun y => (insideZ_pos θ E y).ne'

private theorem product_disintegrate (θ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (E F : C(X × Y, ℝ)) :
    (∫ p, Real.exp (E p)*F p ∂((θ : Measure X).prod (ν : Measure Y))) =
    ∫ p, Real.exp (E p)*conditionalAt θ E F p.2 ∂((θ : Measure X).prod (ν : Measure Y)) := by
  have h0 : Continuous (fun p : X × Y => Real.exp (E p) * F p) := E.continuous.rexp.mul F.continuous
  have h1 : Continuous (fun p : X × Y => Real.exp (E p)*conditionalAt θ E F p.2) :=
    E.continuous.rexp.mul ((conditionalAt_continuous θ E F).comp continuous_snd)
  rw [integral_prod_symm _ (h0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_prod_symm _ (h1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  change (∫ a, Real.exp (E (a,y))*F (a,y) ∂(θ : Measure X)) =
    ∫ a, Real.exp (E (a,y))*conditionalAt θ E F y ∂(θ : Measure X)
  rw [integral_mul_const,conditionalAt]
  field_simp [(insideZ_pos θ E y).ne']

end FiniteConditional

private def finiteEnergy {N : ℕ} {V : Type*} [Fintype V] (H : V → V → ℝ) : C(V → Spin N, ℝ) where
  toFun := energy H
  continuous_toFun := by
    unfold energy
    exact (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      continuous_const.mul (by fun_prop)))).div_const _

private def finitePrior (N : ℕ) [NeZero N] (V : Type*) [Fintype V] :
    ProbabilityMeasure (V → Spin N) :=
  ⟨Measure.pi (fun _ : V => SiteReflection.surfacePrior N), inferInstance⟩

private theorem finitePrior_same (N : ℕ) [NeZero N] (V : Type*) (a b : Fintype V) :
    ((@finitePrior N _ V a) : Measure (V → Spin N)) = (@finitePrior N _ V b : Measure (V → Spin N)) := by
  rw [Subsingleton.elim a b]

private def windowSplit {N : ℕ} {V : Type*} (W : Finset V) [DecidablePred (· ∈ W)] :=
  Homeomorph.piEquivPiSubtypeProd (fun x => x ∈ W) (fun _ : V => Spin N)

/-- The exact Gibbs conditional of a finite torus window at the *original
matrix H*. Its domain is all finite configurations, its value depends
only on the spins in the finite complement. -/
def finiteConditional {N : ℕ} [NeZero N] {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (H : V → V → ℝ) (F : C(V → Spin N, ℝ)) : C(V → Spin N, ℝ) := by
  let e := windowSplit (N := N) W
  let E := (finiteEnergy (N := N) H).comp ⟨e.symm,e.symm.continuous⟩
  let T := F.comp ⟨e.symm,e.symm.continuous⟩
  exact ⟨fun s => conditionalAt (finitePrior N {v : V // v ∈ W}) E T (e s).2,
    (conditionalAt_continuous _ E T).comp (continuous_snd.comp e.continuous)⟩

set_option maxHeartbeats 800000 in
/-- True conditional invariance in finite volume for the physical sphere
Gibbs law at any real coupling matrix, including either winding sum. -/
theorem finite_gibbs_conditional (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (H : V → V → ℝ) (F : C(V → Spin N, ℝ)) :
    (∫ s, F s ∂(sphereGibbs N H : Measure _)) =
      ∫ s, finiteConditional W H F s ∂(sphereGibbs N H : Measure _) := by
  let X := {v : V // v ∈ W} → Spin N
  let Y := {v : V // v ∉ W} → Spin N
  let θ := finitePrior N {v : V // v ∈ W}
  let ν := finitePrior N {v : V // v ∉ W}
  let e := windowSplit (N := N) W
  let em := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Spin N) (fun x => x ∈ W)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : V => SiteReflection.surfacePrior N)
    (fun x : V => x ∈ W)
  have repack (f : (V → Spin N) → ℝ) :
      (∫ s, f s ∂(finitePrior N V : Measure _)) =
        ∫ p, f (e.symm p) ∂((θ : Measure X).prod (ν : Measure Y)) :=
    by
      let h := ((he.symm em).integral_comp' f).symm
      convert h using 1 <;> first | rfl | congr 3 <;> apply finitePrior_same
  let E := (finiteEnergy (N := N) H).comp ⟨e.symm,e.symm.continuous⟩
  let T := F.comp ⟨e.symm,e.symm.continuous⟩
  change (∫ s, F s ∂((finitePrior N V : Measure (V → Spin N)).tilted (energy H))) =
    ∫ s, finiteConditional W H F s ∂((finitePrior N V : Measure (V → Spin N)).tilted (energy H))
  rw [integral_tilted, integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div]
  congr 1
  rw [repack, repack (fun s => Real.exp (energy H s)*finiteConditional W H F s)]
  have h := product_disintegrate θ ν E T
  calc
    _ = ∫ p, Real.exp (E p) * conditionalAt θ E T p.2 ∂((θ : Measure X).prod (ν : Measure Y)) := h
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun p => ?_
      change _ = Real.exp (E p)*conditionalAt θ E T (e (e.symm p)).2
      rw [e.apply_symm_apply]

private theorem sum_abs_periodize_bound {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (J : Site → ℝ) (hJ : Summable fun z => |J z|) (v : V) :
    (∑ w, |Seam.periodizeSeries D J v w|) ≤ ∑' z, |J z| := by
  let f (w : V) (z : Site) := if D z v = w then J z else 0
  have hs (w : V) : Summable (f w) := hJ.of_norm_bounded fun z => by
    by_cases hz : D z v = w <;> simp [f,hz,Real.norm_eq_abs]
  calc
    _ ≤ ∑ w, ∑' z, |f w z| := by
      apply Finset.sum_le_sum
      intro w _
      simpa only [Real.norm_eq_abs, Seam.periodizeSeries, f] using norm_tsum_le_tsum_norm (f := f w) (hs w).norm
    _ = ∑' z, ∑ w, |f w z| := (Summable.tsum_finsetSum (fun w _ => (hs w).abs)).symm
    _ = _ := by
      apply tsum_congr
      intro z
      simp only [f,apply_ite abs,abs_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
private theorem sum_abs_periodize_col_bound {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (hD : DisplacementAction D) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (w : V) :
    (∑ v, |Seam.periodizeSeries D J v w|) ≤ ∑' z, |J z| := by
  let f (v : V) (z : Site) := if D z v = w then J z else 0
  have hs (v : V) : Summable (f v) := hJ.of_norm_bounded fun z => by
    by_cases hz : D z v = w <;> simp [f,hz,Real.norm_eq_abs]
  calc
    _ ≤ ∑ v, ∑' z, |f v z| := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [Real.norm_eq_abs, Seam.periodizeSeries, f] using norm_tsum_le_tsum_norm (f := f v) (hs v).norm
    _ = ∑' z, ∑ v, |f v z| := (Summable.tsum_finsetSum (fun v _ => (hs v).abs)).symm
    _ = _ := by
      apply tsum_congr
      intro z
      change (∑ v, |if hD.shiftEquiv z v = w then J z else 0|) = _
      rw [Equiv.sum_comp (hD.shiftEquiv z) (fun u => |if u = w then J z else 0|)]
      simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
private theorem periodizeSeries_sub {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (J K : Site → ℝ) (hJ : Summable fun z => |J z|)
    (hK : Summable fun z => |K z|) (v w : V) :
    Seam.periodizeSeries D J v w - Seam.periodizeSeries D K v w =
    Seam.periodizeSeries D (fun z => J z-K z) v w := by
  have summ (a : Site → ℝ) (ha : Summable fun z => |a z|) :
      Summable (fun z => if D z v = w then a z else 0) :=
    ha.of_norm_bounded fun z => by by_cases hz : D z v = w <;> simp [hz,Real.norm_eq_abs]
  unfold Seam.periodizeSeries
  rw [← (summ J hJ).tsum_sub (summ K hK)]
  apply tsum_congr
  intro z
  split_ifs <;> simp

private theorem abs_unit_dot {N : ℕ} (s t : Spin N) : |⟪s.val,t.val⟫_ℝ| ≤ 1 := by
  have h := abs_real_inner_le_norm s.val t.val
  simpa only [mem_sphere_zero_iff_norm.mp s.property,mem_sphere_zero_iff_norm.mp t.property,one_mul] using h

/-- Exterior-only energy cancels. This bound is independent of the number of
sites outside the resampled window. -/
theorem finite_energy_change_oscillation {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (J K : V → V → ℝ) (s t : V → Spin N)
    (hout : ∀ v ∉ W, s v = t v) {d : ℝ}
    (hrow : ∀ v, (∑ w, |J v w-K v w|) ≤ d)
    (hcol : ∀ w, (∑ v, |J v w-K v w|) ≤ d) :
    |(energy J s-energy K s)-(energy J t-energy K t)| ≤ 2*(W.card*d) := by
  let a (v w : V) := |J v w-K v w|
  let b (v w : V) := (J v w-K v w)*(⟪(s v).val,(s w).val⟫_ℝ-⟪(t v).val,(t w).val⟫_ℝ)
  have he : (energy J s-energy K s)-(energy J t-energy K t) = (∑ v, ∑ w, b v w)/2 := by
    unfold energy b
    simp only [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hentry (v w : V) :
      |b v w| ≤ (if v ∈ W then 2*a v w else 0) + (if w ∈ W then 2*a v w else 0) := by
    have hb : |b v w| ≤ 2*a v w := by
      rw [show |b v w| = a v w * |⟪(s v).val,(s w).val⟫_ℝ-⟪(t v).val,(t w).val⟫_ℝ| from abs_mul _ _]
      calc
        _ ≤ a v w * (|⟪(s v).val,(s w).val⟫_ℝ|+|⟪(t v).val,(t w).val⟫_ℝ|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
        _ ≤ a v w * (1+1) := mul_le_mul_of_nonneg_left
          (add_le_add (abs_unit_dot (s v) (s w)) (abs_unit_dot (t v) (t w))) (abs_nonneg _)
        _ = _ := by ring
    by_cases hv : v ∈ W <;> by_cases hw : w ∈ W
    · simp only [hv,hw,ite_true]
      linarith [abs_nonneg (b v w)]
    · simpa only [hv,hw,ite_true,ite_false,add_zero] using hb
    · simpa only [hv,hw,ite_true,ite_false,zero_add] using hb
    · simp [b,hv,hw,hout v hv,hout w hw]
  have sumIndicator (X : V → V → ℝ) (hX : ∀ v, ∑ w, X v w ≤ d) :
      (∑ v, ∑ w, if v ∈ W then 2*X v w else 0) ≤ 2*(W.card*d) := by
    calc
      _ = ∑ v, if v ∈ W then ∑ w, 2*X v w else 0 := by
        exact Finset.sum_congr rfl fun v _ => by by_cases hv : v ∈ W <;> simp [hv]
      _ = ∑ v ∈ W, ∑ w, 2*X v w := by simp
      _ = 2*∑ v ∈ W, ∑ w, X v w := by simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (Finset.sum_le_sum fun v _ => hX v).trans_eq (by simp)
  rw [he,abs_div]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    |∑ v, ∑ w, b v w| ≤ ∑ v, ∑ w, |b v w| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun v _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hentry v w
    _ = (∑ v, ∑ w, if v ∈ W then 2*a v w else 0) +
        (∑ w, ∑ v, if w ∈ W then 2*a v w else 0) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun v w => if w ∈ W then 2*a v w else 0)]
    _ ≤ _ := by linarith [sumIndicator a hrow, sumIndicator (fun w v => a v w) hcol]

theorem periodized_energy_change_oscillation {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (hD : DisplacementAction D) (W : Finset V) (J K : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hK : Summable fun z => |K z|)
    (s t : V → Spin N) (hout : ∀ v ∉ W, s v = t v) :
    |(energy (Seam.periodizeSeries D J) s-energy (Seam.periodizeSeries D K) s)-
       (energy (Seam.periodizeSeries D J) t-energy (Seam.periodizeSeries D K) t)| ≤
       2*(W.card*∑' z, |J z-K z|) := by
  apply finite_energy_change_oscillation W _ _ s t hout
  · intro v
    simp only [periodizeSeries_sub D J K hJ hK]
    apply sum_abs_periodize_bound
    exact (hJ.of_abs.sub hK.of_abs).abs
  · intro w
    simp only [periodizeSeries_sub D J K hJ hK]
    apply sum_abs_periodize_col_bound D hD
    exact (hJ.of_abs.sub hK.of_abs).abs

/-- If the energy difference has oscillation d in the resampled spins,
the difference of signed test readings is at most 2‖F‖(exp(d)−1).
An arbitrary exterior-dependent constant cancels in both normalizations. -/
private theorem conditionalAt_error_of_oscillation {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    (θ : ProbabilityMeasure X) (E K F : C(X × Y, ℝ)) (y : Y) {d : ℝ}
    (hd : 0 ≤ d) (h : ∀ a b : X, |(E (a,y)-K (a,y))-(E (b,y)-K (b,y))| ≤ d) :
    |conditionalAt θ E F y-conditionalAt θ K F y| ≤ (Real.exp d-1)*(2*‖F‖) := by
  let Z (A : C(X × Y, ℝ)) := ∫ a, Real.exp (A (a,y)) ∂(θ : Measure X)
  let w (A : C(X × Y, ℝ)) (a : X) := Real.exp (A (a,y)) / Z A
  have hZ (A : C(X × Y, ℝ)) : 0 < Z A := integral_exp_pos
    (intCont θ ((A.continuous.comp (continuous_id.prodMk continuous_const)).rexp))
  have hw (A : C(X × Y, ℝ)) (a : X) : 0 ≤ w A a := (div_pos (Real.exp_pos _) (hZ A)).le
  have cA (A : C(X × Y, ℝ)) : Continuous (fun a : X => A (a,y)) :=
    A.continuous.comp (continuous_id.prodMk continuous_const)
  have cw (A : C(X × Y, ℝ)) : Continuous (w A) := (cA A).rexp.div_const _
  have mass (A : C(X × Y, ℝ)) : (∫ a, w A a ∂(θ : Measure X)) = 1 := by
    change (∫ a, Real.exp (A (a,y))/Z A ∂(θ : Measure X)) = _
    rw [integral_div, div_self (hZ A).ne']
  have rep (A : C(X × Y, ℝ)) : conditionalAt θ A F y =
      ∫ a, w A a*F (a,y) ∂(θ : Measure X) := by
    simp only [w,div_mul_eq_mul_div,integral_div,conditionalAt,Z]
  have compDen (A B : C(X × Y, ℝ)) (h' : ∀ a b : X,
      (A (a,y)-B (a,y))-(A (b,y)-B (b,y)) ≤ d) (a : X) :
      w A a ≤ Real.exp d*w B a := by
    change _/Z A ≤ _*(_/Z B)
    rw [← mul_div_assoc, div_le_div_iff₀ (hZ A) (hZ B)]
    change Real.exp (A (a,y))*(∫ b, Real.exp (B (b,y)) ∂(θ : Measure X)) ≤
      (Real.exp d*Real.exp (B (a,y)))*(∫ b, Real.exp (A (b,y)) ∂(θ : Measure X))
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_mono (intCont _ (continuous_const.mul (cA B).rexp))
      (intCont _ (continuous_const.mul (cA A).rexp))
    intro b
    change Real.exp (A (a,y)) * Real.exp (B (b,y)) ≤ (Real.exp d * Real.exp (B (a,y))) * Real.exp (A (b,y))
    simp only [← Real.exp_add, Real.exp_le_exp]
    linarith [h' a b]
  have h1 := compDen E K (fun a b => (abs_le.mp (h a b)).2)
  have h2 := compDen K E (fun a b => by linarith [(abs_le.mp (h a b)).1])
  have hδ : 0 ≤ Real.exp d-1 := sub_nonneg.mpr (Real.one_le_exp hd)
  have pw (a : X) : |w E a-w K a| ≤ (Real.exp d-1)*(w E a+w K a) := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [h1 a,mul_nonneg hδ (hw E a)]
    · nlinarith [h2 a,mul_nonneg hδ (hw K a)]
  have fI (A : C(X × Y, ℝ)) : Integrable (fun a => w A a*F (a,y)) (θ : Measure X) :=
    intCont θ ((cw A).mul (cA F))
  rw [rep E, rep K, ← integral_sub (fI E) (fI K)]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∫ a, |(w E a-w K a)*F (a,y)| ∂(θ : Measure X) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (f := fun a => (w E a-w K a)*F (a,y)) (μ := (θ : Measure X))
    _ ≤ ∫ a, ((Real.exp d-1)*(w E a+w K a))*‖F‖ ∂(θ : Measure X) := by
      apply integral_mono (intCont _ (((cw E).sub (cw K)).mul (cA F)).abs)
        (intCont _ ((continuous_const.mul ((cw E).add (cw K))).mul continuous_const))
      intro a
      change |(w E a-w K a)*F (a,y)| ≤ ((Real.exp d-1)*(w E a+w K a))*‖F‖
      rw [abs_mul]
      exact mul_le_mul (pw a) (F.norm_coe_le_norm (a,y)) (abs_nonneg _)
        (mul_nonneg hδ (add_nonneg (hw E a) (hw K a)))
    _ = _ := by
      rw [integral_mul_const,integral_const_mul,integral_add (intCont _ (cw E)) (intCont _ (cw K)),mass,mass]
      ring

/-- Exact conditional comparison on an arbitrary finite torus. The only
factor in the coupling error is the number of sites being resampled. -/
theorem periodized_conditional_error (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (hD : DisplacementAction D) (W : Finset V) (J K : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hK : Summable fun z => |K z|)
    (F : C(V → Spin N, ℝ)) (s : V → Spin N) :
    |finiteConditional W (Seam.periodizeSeries D J) F s -
      finiteConditional W (Seam.periodizeSeries D K) F s| ≤
      (Real.exp (2*(W.card*∑' z, |J z-K z|))-1)*(2*‖F‖) := by
  let e := windowSplit (N := N) W
  let E (A : Site → ℝ) := (finiteEnergy (N := N) (Seam.periodizeSeries D A)).comp ⟨e.symm,e.symm.continuous⟩
  let T := F.comp ⟨e.symm,e.symm.continuous⟩
  let y := (e s).2
  let θ := finitePrior N {v : V // v ∈ W}
  let d := 2*(W.card*∑' z, |J z-K z|)
  have hd : 0 ≤ d := mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun _ => abs_nonneg _))
  have hn : ‖T‖ ≤ ‖F‖ := ContinuousMap.norm_le _ (norm_nonneg _) |>.mpr fun u => F.norm_coe_le_norm (e.symm u)
  apply (conditionalAt_error_of_oscillation θ (E J) (E K) T y hd ?_).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by norm_num))
        (sub_nonneg.mpr (Real.one_le_exp hd)))
  intro a b
  apply periodized_energy_change_oscillation D hD W J K hJ hK
      (e.symm (a,y)) (e.symm (b,y))
  intro v hv
  change (if h : v ∈ W then a ⟨v,h⟩ else y ⟨v,h⟩) =
      (if h : v ∈ W then b ⟨v,h⟩ else y ⟨v,h⟩)
  simp only [hv,dite_false]

def cylinderRead {N : ℕ} (T : Finset Site) (F : C(WindowSpin N T, ℝ)) : C(SpinField N, ℝ) :=
  F.comp ⟨T.restrict, continuous_pi fun i => continuous_apply i.val⟩

theorem isGibbs_of_cylinder (N : ℕ) [NeZero N] (J : Site → ℝ) (hJ : Summable fun z => |J z|)
    (P : ProbabilityMeasure (SpinField N))
    (h : ∀ (Λ T : Finset Site) (F : C(WindowSpin N T, ℝ)),
      (∫ s, cylinderRead T F s ∂(P : Measure _)) =
        ∫ s, readout Λ (windowEnergy N Λ J hJ) (cylinderRead T F) s ∂(P : Measure _)) :
    IsGibbs N J hJ P := by
  apply (isGibbs_iff_kernel _ _ _ _).mpr
  intro Λ
  let E := windowEnergy N Λ J hJ
  let A := kernel Λ E ∘ₘ (P : Measure (SpinField N))
  apply IsProjectiveLimit.unique (P := fun T : Finset Site => Measure.map T.restrict (P : Measure (SpinField N)))
  · intro T
    have hc : Continuous (T.restrict : SpinField N → WindowSpin N T) :=
      continuous_pi fun i => continuous_apply i.val
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable,
        integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    change (∫ s, cylinderRead T f.toContinuousMap s ∂(kernel Λ E ∘ₘ (P : Measure _))) = _
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp
      ((cylinderRead T f.toContinuousMap).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    exact (h Λ T f.toContinuousMap).symm
  · intro T
    rfl

theorem gibbs_of_cylinder_residual (N : ℕ) [NeZero N] (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (hQ : Tendsto P atTop (𝓝 Q))
    (h : ∀ (Λ T : Finset Site) (F : C(WindowSpin N T, ℝ)),
      Tendsto (fun n => (∫ s, cylinderRead T F s ∂(P n : Measure _)) -
        ∫ s, readout Λ (windowEnergy N Λ J hJ) (cylinderRead T F) s ∂(P n : Measure _)) atTop (𝓝 0)) :
    IsGibbs N J hJ Q := by
  apply isGibbs_of_cylinder
  intro Λ T F
  apply sub_eq_zero.mp
  apply tendsto_nhds_unique _ (h Λ T F)
  exact ((ProbabilityMeasure.continuous_integral_continuousMap (cylinderRead T F)).continuousAt.tendsto.comp hQ).sub
    ((ProbabilityMeasure.continuous_integral_continuousMap (readout Λ (windowEnergy N Λ J hJ)
      (cylinderRead T F))).continuousAt.tendsto.comp hQ)

private def activeWeight {V : Type*} [DecidableEq V] (W : Finset V) (v w : V) : ℝ :=
  if v ∈ W then (if w ∈ W then 1/2 else 1) else 0

private def activeEnergy {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (W : Finset V)
    (H : V → V → ℝ) (s : V → Spin N) : ℝ :=
  ∑ v, ∑ w, activeWeight W v w * (H v w * ⟪(s v).val,(s w).val⟫_ℝ)

private theorem activeEnergy_change {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (H : V → V → ℝ) (hH : ∀ v w, H v w = H w v)
    (s t : V → Spin N) (h : ∀ v ∉ W, s v = t v) :
    energy H s-energy H t = activeEnergy W H s-activeEnergy W H t := by
  let d (v w : V) := H v w * (⟪(s v).val,(s w).val⟫_ℝ-⟪(t v).val,(t w).val⟫_ℝ)
  have ds (v w : V) : d v w = d w v := by
    unfold d
    rw [hH v w,real_inner_comm (s v).val (s w).val,real_inner_comm (t v).val (t w).val]
  have split (v w : V) : d v w = activeWeight W v w*d v w + activeWeight W w v*d w v := by
    rw [← ds v w]
    by_cases hv : v ∈ W <;> by_cases hw : w ∈ W
    · simp only [activeWeight,hv,hw,ite_true]
      ring
    · simp [activeWeight,hv,hw]
    · simp [activeWeight,hv,hw]
    · simp [activeWeight,hv,hw,d,h v hv,h w hw]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
    (fun v _ => Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun w _ => split v w))
  simp only [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_comm (f := fun v w => activeWeight W w v * d w v)] at hsum
  have hfull : energy H s-energy H t = (∑ v, ∑ w, d v w)/2 := by
    simp only [energy, ← sub_div, ← Finset.sum_sub_distrib, d, mul_sub]
  have hlocal : activeEnergy W H s-activeEnergy W H t = ∑ v, ∑ w, activeWeight W v w*d v w := by
    simp only [activeEnergy, ← Finset.sum_sub_distrib, d, mul_sub]
  rw [hfull,hlocal]
  linarith

private theorem periodizeSeries_symmetric {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (hD : DisplacementAction D) (J : Site → ℝ)
    (hJ : ∀ z, J (-z) = J z) (v w : V) :
    Seam.periodizeSeries D J v w = Seam.periodizeSeries D J w v := by
  unfold Seam.periodizeSeries
  rw [← tsum_comp_neg (fun z : Site => if D z v = w then J z else 0)]
  apply tsum_congr
  intro z
  have h : D (-z) v = w ↔ D z w = v := by
    constructor
    · rintro rfl
      rw [← hD.add,add_neg_cancel,hD.zero]
    · rintro rfl
      rw [← hD.add,neg_add_cancel,hD.zero]
  simp only [h,hJ]

private theorem periodize_finiteEnergy_read {V : Type*} [Fintype V] [DecidableEq V] (D : Site → V → V)
    (T : Finset Site) (J : Site → ℝ) (hT : ∀ z ∉ T, J z = 0) (v : V) (f : V → ℝ) :
    (∑ w, Seam.periodizeSeries D J v w*f w) = ∑ z ∈ T, J z*f (D z v) := by
  have h (w : V) : Seam.periodizeSeries D J v w = ∑ z ∈ T, if D z v = w then J z else 0 :=
    tsum_eq_sum fun z hz => by simp [hT z hz]
  simp_rw [h,Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]


private theorem windowEnergy_on_finite (N : ℕ) (Λ T : Finset Site) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hT : ∀ z ∉ T, J z = 0) (s : SpinField N) :
    windowEnergy N Λ J hJ s =
      ∑ x ∈ Λ, ∑ z ∈ T, J z * ((if x+z ∈ Λ then (1:ℝ)/2 else 1)*
        ⟪(s x).val,(s (x+z)).val⟫_ℝ) := by
  change (∑ x : Λ, ∑' z : Site, J z*((if x.val+z ∈ Λ then (1:ℝ)/2 else 1)*
    ⟪(s x.val).val,(s (x.val+z)).val⟫_ℝ)) = _
  let k (x : Site) := ∑' z : Site, J z*((if x+z ∈ Λ then (1:ℝ)/2 else 1)*
    ⟪(s x).val,(s (x+z)).val⟫_ℝ)
  change (∑ x : Λ, k x.val) = _
  rw [Finset.sum_coe_sort Λ k]
  refine Finset.sum_congr rfl fun x _ => tsum_eq_sum fun z hz => ?_
  simp [hT z hz]

private theorem activeEnergy_sum {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (H : V → V → ℝ) (s : V → Spin N) :
    activeEnergy W H s = ∑ v ∈ W, ∑ w, H v w*((if w ∈ W then (1:ℝ)/2 else 1)*
        ⟪(s v).val,(s w).val⟫_ℝ) := by
  unfold activeEnergy
  calc
    _ = ∑ v, if v ∈ W then ∑ w, H v w*((if w ∈ W then (1:ℝ)/2 else 1)*
        ⟪(s v).val,(s w).val⟫_ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ W
      · simp only [activeWeight,hv,ite_true]
        apply Finset.sum_congr rfl
        intro w _
        ring
      · simp [activeWeight,hv]
    _ = _ := by simp

private theorem localImage_mem {V : Type*} [DecidableEq V] (f : Site → V)
    {Λ T : Finset Site} (hj : Set.InjOn f (T : Set Site)) (hΛ : Λ ⊆ T) {q : Site} (hq : q ∈ T) :
    f q ∈ Λ.image f ↔ q ∈ Λ := by
  constructor
  · intro h
    obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp h
    exact (hj (hΛ hx) hq eq) ▸ hx
  · exact fun h => Finset.mem_image_of_mem f h

/-- On one injective neighborhood the exact periodized finite-range
incident energy is the original lattice window energy. -/
private theorem activeEnergy_lift {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (hD : DisplacementAction D) (o : V) (Λ Z T : Finset Site)
    (hΛ : Λ ⊆ T) (hZ : ∀ x ∈ Λ, ∀ z ∈ Z, x+z ∈ T)
    (hj : Set.InjOn (fun x => D x o) (T : Set Site)) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hs : ∀ z ∉ Z, J z = 0) (s : V → Spin N) :
    activeEnergy (Λ.image (fun x => D x o)) (Seam.periodizeSeries D J) s =
      windowEnergy N Λ J hJ (liftAt D o s) := by
  rw [windowEnergy_on_finite N Λ Z J hJ hs,activeEnergy_sum,Finset.sum_image (hj.mono hΛ)]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [periodize_finiteEnergy_read D Z J hs]
  refine Finset.sum_congr rfl fun z hz => ?_
  have move : D z (D x o) = D (x+z) o := by rw [← hD.add,add_comm z x]
  rw [move]
  simp only [localImage_mem _ hj hΛ (hZ x hx z hz),liftAt]

private def imageEquiv {V : Type*} [DecidableEq V] (f : Site → V) (Λ : Finset Site)
    (h : Set.InjOn f (Λ : Set Site)) : Λ ≃ (Λ.image f) :=
  Equiv.ofBijective (fun x => ⟨f x.val, Finset.mem_image_of_mem f x.property⟩)
    ⟨fun x y hxy => Subtype.ext (h x.property y.property (congrArg Subtype.val hxy)), by
      rintro ⟨v,hv⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨⟨x,hx⟩,rfl⟩⟩

private def pullSpin {N : ℕ} {X Y : Type*} (e : X ≃ Y) :
    (Y → Spin N) ≃ᵐ (X → Spin N) :=
  MeasurableEquiv.piCongrLeft (fun _ : X => Spin N) e.symm

private theorem pullSpin_value {N : ℕ} {X Y : Type*} (e : X ≃ Y) (a : Y → Spin N) (x : X) :
    pullSpin e a x = a (e x) := by
  simpa only [Equiv.symm_apply_apply,pullSpin] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : X => Spin N) e.symm a (e x)

private def finiteReplace {N : ℕ} {V : Type*} [DecidableEq V] (W : Finset V) (s : V → Spin N)
    (a : W → Spin N) (v : V) := if h : v ∈ W then a ⟨v,h⟩ else s v

private theorem restricted_lift_replace {N : ℕ} {V : Type*} [DecidableEq V] (f : Site → V)
    (Λ T : Finset Site) (hΛ : Λ ⊆ T) (hj : Set.InjOn f (T : Set Site))
    (s : V → Spin N) (a : (Λ.image f) → Spin N) (x : Site) (hx : x ∈ T) :
    finiteReplace (Λ.image f) s a (f x) =
    replace Λ (fun i => s (f i)) (pullSpin (imageEquiv f Λ (hj.mono hΛ)) a) x := by
  let e := imageEquiv f Λ (hj.mono hΛ)
  by_cases hm : x ∈ Λ
  · rw [replace_inside _ _ _ hm,pullSpin_value]
    simp only [finiteReplace, Finset.mem_image_of_mem f hm, dite_true]
    rfl
  · rw [replace_outside _ _ _ hm]
    have hnot : f x ∉ Λ.image f := by
      intro hx'
      obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hx'
      exact hm ((hj (hΛ hq) hx heq) ▸ hq)
    simp only [finiteReplace,hnot,dite_false]

/-- The rematched prior is still exactly the product of the unit-sphere
laws on the original window. -/
private theorem surface_reindex (N : ℕ) [NeZero N] {V : Type*} [DecidableEq V] (W : Finset V)
    (Λ : Finset Site) (e : Λ ≃ W) (F : WindowSpin N Λ → ℝ) :
    (∫ a, F (pullSpin e a) ∂(Measure.pi fun _ : W => SiteReflection.surfacePrior N)) =
      ∫ a, F a ∂(windowPrior N Λ : Measure _) := by
  exact (measurePreserving_piCongrLeft (fun _ : Λ => SiteReflection.surfacePrior N) e.symm).integral_comp' F

def torusPullback {N : ℕ} {V : Type*} (D : Site → V → V) (o : V) (F : C(SpinField N, ℝ)) :
    C(V → Spin N, ℝ) :=
  F.comp ⟨liftAt D o,continuous_pi fun x => continuous_apply (D x o)⟩

private theorem windowEnergy_local {N : ℕ} (Λ Z T : Finset Site)
    (hΛ : Λ ⊆ T) (hZ : ∀ x ∈ Λ, ∀ z ∈ Z, x+z ∈ T) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hs : ∀ z ∉ Z, J z = 0) (s t : SpinField N)
    (h : ∀ x ∈ T, s x=t x) : windowEnergy N Λ J hJ s=windowEnergy N Λ J hJ t := by
  rw [windowEnergy_on_finite N Λ Z J hJ hs s,windowEnergy_on_finite N Λ Z J hJ hs t]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro z hz
  rw [h x (hΛ hx),h (x+z) (hZ x hx z hz)]

/-- A finite-range even interaction has exactly the same local resampling
reading on an injective torus neighborhood and on its infinite lattice
lift, for every test whose sites belong to this same neighborhood. -/
theorem injective_periodized_resampling (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (hD : DisplacementAction D) (o : V) (Λ Z T : Finset Site)
    (hΛ : Λ ⊆ T) (hZ : ∀ x ∈ Λ, ∀ z ∈ Z, x+z ∈ T)
    (hj : Set.InjOn (fun x => D x o) (T : Set Site)) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hs : ∀ z ∉ Z, J z = 0) (hneg : ∀ z, J (-z) = J z)
    (s : V → Spin N) (F : C(SpinField N, ℝ))
    (hF : ∀ f g : SpinField N, (∀ x ∈ T, f x = g x) → F f = F g) :
    finiteConditional (Λ.image (fun x => D x o)) (Seam.periodizeSeries D J) (torusPullback D o F) s =
      readout Λ (windowEnergy N Λ J hJ) F (liftAt D o s) := by
  let f (x : Site) := D x o
  let W := Λ.image f
  let e := imageEquiv f Λ (hj.mono hΛ)
  let b (a : W → Spin N) := pullSpin e a
  let S (a : W → Spin N) := finiteReplace W s a
  let U (a : WindowSpin N Λ) := replace Λ (liftAt D o s) a
  let E := windowEnergy N Λ J hJ
  let H := Seam.periodizeSeries D J
  let C := energy H s - E (liftAt D o s)
  have site (a : W → Spin N) (x : Site) (hx : x ∈ T) : liftAt D o (S a) x = U (b a) x :=
    restricted_lift_replace f Λ T hΛ hj s a x hx
  have Fval (a : W → Spin N) : F (liftAt D o (S a)) = F (U (b a)) := hF _ _ (site a)
  have Eval (a : W → Spin N) : energy H (S a) = C+ E (U (b a)) := by
    have h0 := activeEnergy_change W H (periodizeSeries_symmetric D hD J hneg) (S a) s
      (fun v hv => by simp only [S, finiteReplace,hv,dite_false])
    have h1 := activeEnergy_lift D hD o Λ Z T hΛ hZ hj J hJ hs (S a)
    have h2 := activeEnergy_lift D hD o Λ Z T hΛ hZ hj J hJ hs s
    have h3 := windowEnergy_local Λ Z T hΛ hZ J hJ hs (liftAt D o (S a)) (U (b a)) (site a)
    change activeEnergy W H (S a) = E (liftAt D o (S a)) at h1
    change activeEnergy W H s = E (liftAt D o s) at h2
    change E (liftAt D o (S a)) = E (U (b a)) at h3
    change _ = (energy H s - E (liftAt D o s))+_
    linarith
  let θ : Measure (W → Spin N) := Measure.pi fun _ : W => SiteReflection.surfacePrior N
  let ν : Measure (WindowSpin N Λ) := windowPrior N Λ
  have push (G : WindowSpin N Λ → ℝ) : (∫ a, G (b a) ∂θ) = ∫ a, G a ∂ν :=
    surface_reindex N W Λ e G
  have znum : (∫ a, Real.exp (energy H (S a))*F (liftAt D o (S a)) ∂θ) =
      Real.exp C * ∫ p, Real.exp (E (U p))*F (U p) ∂ν := by
    simp_rw [Eval,Fval,Real.exp_add,mul_assoc]
    rw [integral_const_mul]
    exact congrArg (Real.exp C * ·) (push (fun p => Real.exp (E (U p))*F (U p)))
  have zden : (∫ a, Real.exp (energy H (S a)) ∂θ) =
      Real.exp C * ∫ p, Real.exp (E (U p)) ∂ν := by
    simp_rw [Eval, Real.exp_add]
    rw [integral_const_mul]
    exact congrArg (Real.exp C * ·) (push (fun p => Real.exp (E (U p))))
  change ((∫ a, Real.exp (energy H (S a))*F (liftAt D o (S a)) ∂θ) /
      ∫ a, Real.exp (energy H (S a)) ∂θ) = ∫ t, F t ∂(resample Λ E (liftAt D o s) : Measure _)
  rw [resample_integral]
  change _ = (∫ p, Real.exp (E (U p))*F (U p) ∂ν) / ∫ p, Real.exp (E (U p)) ∂ν
  rw [znum,zden,mul_div_mul_left _ _ (Real.exp_pos C).ne']


private theorem abs_rooted_residual {N : ℕ} [NeZero N] {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (D : Site → V → V) (hD : DisplacementAction D) (Λ Z T : Finset Site)
    (hΛ : Λ ⊆ T) (hZ : ∀ x ∈ Λ, ∀ z ∈ Z, x+z ∈ T)
    (hj : ∀ o, Set.InjOn (fun x => D x o) (T : Set Site))
    (K J : Site → ℝ) (hK : Summable fun z => |K z|) (hJ : Summable fun z => |J z|)
    (hs : ∀ z ∉ Z, J z = 0) (hneg : ∀ z, J (-z) = J z)
    (F : C(SpinField N, ℝ)) (hF : ∀ f g : SpinField N, (∀ x ∈ T, f x = g x) → F f = F g) :
    |(∫ s, F s ∂(rootedLaw N D (Seam.periodizeSeries D K) : Measure _)) -
      ∫ s, readout Λ (windowEnergy N Λ J hJ) F s
        ∂(rootedLaw N D (Seam.periodizeSeries D K) : Measure _)| ≤
       (Real.exp (2*(Λ.card*∑' z, |K z-J z|))-1)*(2*‖F‖) := by
  let Q := sphereGibbs N (Seam.periodizeSeries D K)
  let G := readout Λ (windowEnergy N Λ J hJ) F
  let δ := ∑' z, |K z-J z|
  have hd : 0 ≤ δ := tsum_nonneg fun _ => abs_nonneg _
  let err := (Real.exp (2*(Λ.card*δ))-1)*(2*‖F‖)
  have one (o : V) : |(∫ s, F (liftAt D o s) ∂(Q : Measure _)) -
      ∫ s, G (liftAt D o s) ∂(Q : Measure _)| ≤ err := by
    let W := Λ.image (fun x => D x o)
    let B := torusPullback D o F
    let A (J' : Site → ℝ) := finiteConditional W (Seam.periodizeSeries D J') B
    have he := finite_gibbs_conditional N W (Seam.periodizeSeries D K) B
    have he' (s : V → Spin N) : A J s = G (liftAt D o s) :=
      injective_periodized_resampling N D hD o Λ Z T hΛ hZ (hj o) J hJ hs hneg s F hF
    change |(∫ s, B s ∂(Q : Measure _)) - ∫ s, G (liftAt D o s) ∂(Q : Measure _)| ≤ err
    rw [he]
    simp_rw [← he']
    rw [← integral_sub (intCont Q (A K).continuous) (intCont Q (A J).continuous)]
    have ew : 0 ≤ Real.exp (2*(W.card*δ))-1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    have hW : (W.card : ℝ) ≤ Λ.card := by exact_mod_cast Finset.card_image_le
    have hb : ‖B‖ ≤ ‖F‖ :=
      (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun s => F.norm_coe_le_norm (liftAt D o s)
    have eCompare : (Real.exp (2*(W.card*δ))-1)*(2*‖B‖) ≤ err := by
      have hspec : Real.exp (2*(W.card*δ))-1 ≤ Real.exp (2*(Λ.card*δ))-1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW hd) (by norm_num))) 1
      have hexp : 0 ≤ Real.exp (2*(Λ.card*δ))-1 :=
        sub_nonneg.mpr (Real.one_le_exp (by positivity))
      exact mul_le_mul hspec (mul_le_mul_of_nonneg_left hb (by norm_num)) (by positivity) hexp
    simpa [Real.norm_eq_abs,measureReal_def] using
      norm_integral_le_of_norm_le_const (μ := (Q : Measure _)) (f := fun s => A K s-A J s)
        (C := err) (Eventually.of_forall fun s => (periodized_conditional_error N D hD W K J hK hJ B s).trans eCompare)
  rw [rootedLaw_integral,rootedLaw_integral,← sub_div,← Finset.sum_sub_distrib,abs_div,
    abs_of_pos (show (0:ℝ) < (Fintype.card V : ℝ) from Nat.cast_pos.mpr Fintype.card_pos)]
  apply (div_le_iff₀ (show (0:ℝ) < (Fintype.card V : ℝ) from Nat.cast_pos.mpr Fintype.card_pos)).mpr
  calc
    _ ≤ ∑ o, |(∫ s, F (liftAt D o s) ∂(Q : Measure _)) - ∫ s, G (liftAt D o s) ∂(Q : Measure _)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : V, err := Finset.sum_le_sum fun o _ => one o
    _ = _ := by simp [err,δ,mul_comm]

/-- Every weak limit of actual uniformly rooted cubic periodic Gibbs fields
at couplings approaching a fixed finite-range even coupling in l1 is a
full Borel Gibbs state at that coupling. -/
theorem gibbs_of_cubic_periodic_weak_l1_limit (N : ℕ) [NeZero N]
    (side : ℕ → ℕ) [∀ n, NeZero (side n)] (hside : Tendsto side atTop atTop)
    (K : ℕ → Site → ℝ) (hK : ∀ n, Summable fun z => |K n z|) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (Z : Finset Site) (hs : ∀ z ∉ Z, J z = 0)
    (hneg : ∀ z, J (-z) = J z)
    (hclose : Tendsto (fun n => ∑' z, |K n z-J z|) atTop (𝓝 0))
    (Q : ProbabilityMeasure (SpinField N))
    (hQ : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) (K n))) atTop (𝓝 Q)) :
    IsGibbs N J hJ Q := by
  apply gibbs_of_cylinder_residual N J hJ hQ
  intro Λ S C
  let F := cylinderRead S C
  let T := (Λ∪S) ∪ Λ.biUnion (fun x => Z.image (fun z => x+z))
  have hΛ : Λ ⊆ T := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hS : S ⊆ T := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hZ (x : Site) (hx : x ∈ Λ) (z : Site) (hz : z ∈ Z) : x+z ∈ T :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩)
  have hF (s t : SpinField N) (h : ∀ x ∈ T, s x = t x) : F s = F t :=
    congrArg C (funext fun x : S => h x.val (hS x.property))
  let err (n : ℕ) := (Real.exp (2*(Λ.card*∑' z, |K n z-J z|))-1)*(2*‖F‖)
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero,Real.exp_zero,sub_self,zero_mul] using
      ((((hclose.const_mul (Λ.card : ℝ)).const_mul 2).rexp.sub_const 1).mul_const (2*‖F‖))
  apply squeeze_zero_norm' _ herr
  filter_upwards [hside.eventually (Seam.eventually_injOn_baseMove T.finite_toSet)] with n hn
  exact abs_rooted_residual Seam.baseMove (Seam.cubic_displacement_action (side n)) Λ Z T hΛ hZ
    (fun o => hn o) (K n) J (hK n) hJ hs hneg F hF


theorem nearestCoupling_even (β : ℝ) (z : Site) : nearestCoupling β (-z) = nearestCoupling β z := by
  have flip (i : Fin 3) (b : Bool) : -siteStep i b = siteStep i (!b) := by
    cases b <;> simp [siteStep, ← Pi.single_neg]
  have closed (x : Site) (hx : x ∈ nearestSteps) : -x ∈ nearestSteps := by
    obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(i,!b),Finset.mem_univ _,(flip i b).symm⟩
  have eq : -z ∈ nearestSteps ↔ z ∈ nearestSteps := ⟨fun h => by simpa using closed (-z) h,closed z⟩
  simp only [nearestCoupling,eq]

/-- Original nearest-neighbour surface specification. Only the actual
weak convergence of the lifted Gibbs laws and convergence of couplings
enter. No finite or infinite DLR hypothesis is required. -/
theorem nearest_gibbs_of_cubic_periodic (N : ℕ) [NeZero N]
    (side : ℕ → ℕ) [∀ n, NeZero (side n)] (hside : Tendsto side atTop atTop)
    (K : ℕ → Site → ℝ) (hK : ∀ n, Summable fun z => |K n z|) (β : ℝ)
    (hclose : Tendsto (fun n => ∑' z, |K n z-nearestCoupling β z|) atTop (𝓝 0))
    (Q : ProbabilityMeasure (SpinField N))
    (hQ : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) (K n))) atTop (𝓝 Q)) :
    IsNearestGibbs N β Q :=
  gibbs_of_cubic_periodic_weak_l1_limit N side hside K hK (nearestCoupling β)
    (summable_abs_nearest β) nearestSteps (fun z hz => by simp [nearestCoupling,hz])
    (nearestCoupling_even β) hclose Q hQ


private theorem local_cube_exhausts (z : Site) : ∀ᶠ j : ℕ in atTop, z ∈ cube j := by
  filter_upwards [eventually_ge_atTop (∑ i, (z i).natAbs)] with j hj
  simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc]
  intro i
  have hi : (z i).natAbs ≤ ∑ q, (z q).natAbs :=
    Finset.single_le_sum (f := fun q => (z q).natAbs) (fun q _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

private theorem neg_mem_cube (j : ℕ) (x : Site) : -x ∈ cube j ↔ x ∈ cube j := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply]
  constructor <;> intro h i <;> have := h i <;> omega

private theorem lattice_l1_triangle (A B C : Site → ℝ)
    (hA : Summable fun z => |A z|) (hB : Summable fun z => |B z|) (hC : Summable fun z => |C z|) :
    (∑' z, |A z-C z|) ≤ (∑' z, |A z-B z|)+∑' z, |B z-C z| := by
  have hAB := (hA.of_abs.sub hB.of_abs).abs
  have hBC := (hB.of_abs.sub hC.of_abs).abs
  rw [← hAB.tsum_add hBC]
  apply ((hA.of_abs.sub hC.of_abs).abs).tsum_le_tsum _ (hAB.add hBC)
  intro z
  simpa only [sub_add_sub_cancel] using abs_add_le (A z-B z) (B z-C z)

/-- Every cubic periodic weak limit at any even summable displacement
interaction satisfies its complete Borel DLR equations. Couplings may
vary in l1 with the period. For each fixed finite cylinder, use a
subsequence of the *same* limiting law along which the growing truncated
interaction collar embeds, and then let its l1 tail vanish. -/
theorem gibbs_of_cubic_periodic_summable (N : ℕ) [NeZero N]
    (side : ℕ → ℕ) [∀ n, NeZero (side n)] (hside : Tendsto side atTop atTop)
    (K : ℕ → Site → ℝ) (hK : ∀ n, Summable fun z => |K n z|) (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (hneg : ∀ z, J (-z) = J z)
    (hclose : Tendsto (fun n => ∑' z, |K n z-J z|) atTop (𝓝 0))
    (Q : ProbabilityMeasure (SpinField N))
    (hQ : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) (K n))) atTop (𝓝 Q)) :
    IsGibbs N J hJ Q := by
  apply isGibbs_of_cylinder
  intro Λ S F'
  let F := cylinderRead S F'
  let P (n : ℕ) := rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) (K n))
  let A (j : ℕ) (z : Site) := if z ∈ cube j then J z else 0
  have hA (j : ℕ) : Summable (fun z => |A j z|) := summable_of_ne_finset_zero (s := cube j)
    (fun z hz => by simp [A,hz])
  have heven (j : ℕ) (z : Site) : A j (-z) = A j z := by simp only [A,neg_mem_cube,hneg]
  have htail : Tendsto (fun j => ∑' z, |A j z-J z|) atTop (𝓝 0) := by
    have co (z : Site) : Tendsto (fun j => |A j z-J z|) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [local_cube_exhausts z] with j hj using (by simp [A,hj])
    simpa using tendsto_tsum_of_dominated_convergence (f := fun j z => |A j z-J z|)
      (g := fun _ => (0:ℝ)) hJ co (Eventually.of_forall fun j z => by
        by_cases h : z ∈ cube j <;> simp [A,h,Real.norm_eq_abs])
  let T (j : ℕ) := (Λ∪S) ∪ Λ.biUnion (fun x => (cube j).image (fun z => x+z))
  have hΛ (j : ℕ) : Λ ⊆ T j := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hS (j : ℕ) : S ⊆ T j := fun _ hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hZ (j : ℕ) (x : Site) (hx : x ∈ Λ) (z : Site) (hz : z ∈ cube j) : x+z ∈ T j :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩)
  have hF (j : ℕ) (s t : SpinField N) (h : ∀ x ∈ T j, s x = t x) : F s = F t :=
    congrArg F' (funext fun x : S => h x.val (hS j x.property))
  have pick (j : ℕ) : ∃ n : ℕ, j ≤ n ∧ ∀ o : Seam.Cell (side n),
      Set.InjOn (fun x => Seam.baseMove x o) (T j : Set Site) := by
    have hh := hside.eventually (Seam.eventually_injOn_baseMove (T j).finite_toSet)
    obtain ⟨n,hn,hm⟩ := ((eventually_ge_atTop j).and hh).exists
    exact ⟨n,hn,fun o => hm o⟩
  choose l hle hcoord using pick
  have hl : Tendsto l atTop atTop := tendsto_atTop_mono hle tendsto_id
  have hPA : Tendsto (fun j => ∑' z, |K (l j) z-A j z|) atTop (𝓝 0) := by
    have res := (hclose.comp hl).add htail
    simp only [zero_add] at res
    apply squeeze_zero (fun j => tsum_nonneg fun z => abs_nonneg _)
      (fun j => (lattice_l1_triangle (K (l j)) J (A j) (hK _) hJ (hA j)).trans_eq ?_) res
    rw [show (fun z => |J z-A j z|) = (fun z => |A j z-J z|) by
      funext z; exact abs_sub_comm _ _]
    rfl
  let rd (n : ℕ) (E : C(SpinField N, ℝ)) := ∫ s, E s ∂(P n : Measure _)
  let B (j : ℕ) := readout Λ (windowEnergy N Λ (A j) (hA j)) F
  let G := readout Λ (windowEnergy N Λ J hJ) F
  have small (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0)) :
      Tendsto (fun j => (Real.exp (2*(Λ.card*d j))-1)*(2*‖F‖)) atTop (𝓝 0) := by
    simpa only [mul_zero,Real.exp_zero,sub_self,zero_mul] using
      ((((hd.const_mul (Λ.card : ℝ)).const_mul 2).rexp.sub_const 1).mul_const (2*‖F‖))
  have ha : Tendsto (fun j => rd (l j) F-rd (l j) (B j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (small _ hPA)
    intro j
    exact abs_rooted_residual Seam.baseMove (Seam.cubic_displacement_action (side (l j))) Λ (cube j)
      (T j) (hΛ j) (hZ j) (hcoord j) (K (l j)) (A j) (hK _) (hA j)
      (fun z hz => by simp [A,hz]) (heven j) F (hF j)
  have hb : Tendsto (fun j => rd (l j) (B j) - rd (l j) G) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (small _ htail)
    intro j
    change ‖(∫ s, B j s ∂(P (l j) : Measure _)) - ∫ s, G s ∂(P (l j) : Measure _)‖ ≤ _
    rw [← integral_sub (intCont _ (B j).continuous) (intCont _ G.continuous)]
    simpa [Real.norm_eq_abs,measureReal_def] using
      norm_integral_le_of_norm_le_const (μ := (P (l j) : Measure _)) (f := fun s => B j s - G s)
        (C := (Real.exp (2*(Λ.card*∑' z, |A j z-J z|))-1)*(2*‖F‖)) (Eventually.of_forall fun s =>
          interaction_readout_error Λ (A j) J (hA j) hJ F s)
  have diff := ha.add hb
  simp only [sub_add_sub_cancel,zero_add] at diff
  have lim (F : C(SpinField N, ℝ)) :
      Tendsto (fun j => rd (l j) F) atTop (𝓝 (∫ s, F s ∂(Q : Measure _))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp (hQ.comp hl)
  exact sub_eq_zero.mp (tendsto_nhds_unique ((lim F).sub (lim G)) diff)


/-- Fixed-interaction form for the very cubic subsequence returned by the
periodic variational selection theorem. -/
theorem gibbs_of_cubic_fixed (N : ℕ) [NeZero N]
    (side : ℕ → ℕ) [∀ n, NeZero (side n)] (hside : Tendsto side atTop atTop)
    (J : Site → ℝ) (hJ : Summable fun z => |J z|) (hneg : ∀ z, J (-z) = J z)
    (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) J)) atTop (𝓝 P)) :
    IsGibbs N J hJ P := by
  apply gibbs_of_cubic_periodic_summable N side hside (fun _ => J) (fun _ => hJ) J hJ hneg _ P hP
  simpa only [sub_self,abs_zero,tsum_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

/-- Two successive physical limits used in the auxiliary-interaction
selection. Each Pj can use its own actual periodic side sequence. The same
weak limit that retains the mirror inequalities has the six-neighbour
specification once the perturbations tend to zero in l1. -/
theorem nearest_gibbs_of_weak_cubic_states (N : ℕ) [NeZero N]
    (side : ℕ → ℕ → ℕ) [∀ j n, NeZero (side j n)] (hside : ∀ j, Tendsto (side j) atTop atTop)
    (J : ℕ → Site → ℝ) (hJ : ∀ j, Summable fun z => |J j z|) (heven : ∀ j z, J j (-z)=J j z)
    (β : ℝ) (hclose : Tendsto (fun j => ∑' z, |J j z-nearestCoupling β z|) atTop (𝓝 0))
    (P : ℕ → ProbabilityMeasure (SpinField N))
    (hP : ∀ j, Tendsto (fun n => rootedLaw N Seam.baseMove
      (Seam.ordinarySeries (side j n) (J j))) atTop (𝓝 (P j)))
    {Q : ProbabilityMeasure (SpinField N)} (hQ : Tendsto P atTop (𝓝 Q)) :
    IsNearestGibbs N β Q :=
  nearest_gibbs_of_weak_l1_limits N hQ J β hJ hclose
    (fun j => gibbs_of_cubic_fixed N (side j) (hside j) (J j) (hJ j) (heven j) (P j) (hP j))

/-- Boundary spins determine the entire conditional law, retaining its
full Borel record. -/
theorem resample_eq_of_outside {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ))
    {s t : SpinField N} (h : ∀ x ∉ Λ, s x=t x) : resample Λ E s = resample Λ E t := by
  have rr : replace Λ s = replace Λ t := by
    funext a x
    by_cases hx : x ∈ Λ
    · rw [replace_inside _ _ _ hx,replace_inside _ _ _ hx]
    · rw [replace_outside _ _ _ hx,replace_outside _ _ _ hx,h x hx]
  apply Subtype.ext
  change Measure.map (replace Λ s) ((windowPrior N Λ : Measure _).tilted (fun a => E (replace Λ s a))) =
    Measure.map (replace Λ t) ((windowPrior N Λ : Measure _).tilted (fun a => E (replace Λ t a)))
  rw [rr]

/-- Properness for arbitrary Borel outside records. -/
theorem kernel_inter_outside {N : ℕ} [NeZero N] (Λ : Finset Site) (E : C(SpinField N, ℝ))
    (s : SpinField N) {A B : Set (SpinField N)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    [Decidable (s ∈ B)] (outside : ∀ f g : SpinField N, (∀ x ∉ Λ, f x = g x) → (f ∈ B ↔ g ∈ B)) :
    kernel Λ E s (A ∩ B) = if s ∈ B then kernel Λ E s A else 0 := by
  let μ := (windowPrior N Λ : Measure _).tilted (fun a => E (replace Λ s a))
  change (Measure.map (replace Λ s) μ) (A ∩ B) = if s ∈ B then Measure.map (replace Λ s) μ A else 0
  rw [Measure.map_apply (continuousReplaceFixed Λ s).measurable (hA.inter hB),
    Measure.map_apply (continuousReplaceFixed Λ s).measurable hA, Set.preimage_inter]
  have hp (a : WindowSpin N Λ) := outside (replace Λ s a) s (fun x hx => replace_outside Λ s a hx)
  by_cases hs : s ∈ B
  · have hb : (replace Λ s) ⁻¹' B = Set.univ := Set.eq_univ_of_forall fun a => (hp a).2 hs
    simp [hb,hs]
  · have hb : (replace Λ s) ⁻¹' B = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun a ha => hs ((hp a).1 ha))
    simp [hb,hs]
/-- One original cubic state simultaneously satisfies the physical Gibbs
equations, gives the indicated momentum law, and controls every actual
pressure variation by a direction-dependent adapted state. -/
theorem common_cubic_variational_gibbs_state (N : ℕ) [NeZero N] (J : Site → ℝ)
    (hJ : Summable fun z => |J z|) (heven : ∀ z, J (-z)=J z)
    (sides : ℕ → ℕ) [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop) :
    ∃ P : ProbabilityMeasure (SpinField N), ∃ μ : ProbabilityMeasure Momentum, ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant P ∧ IsGibbs N J hJ P ∧
      Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides (l n)) J))
        atTop (𝓝 P) ∧ (∀ z, spectralPair (μ : Measure Momentum) z = fieldPair P z) ∧
      ∀ (H : Site → ℝ) (K : ℕ → Site → ℝ) (t : ℕ → ℝ), (∀ n, 0 < t n) →
        ∀ hH : Summable fun z => |H z|, (∀ n, Summable fun z => |K n z|) →
        Tendsto (fun n => ∑' z, |(K n z-J z)/t n-H z|) atTop (𝓝 0) →
        ∃ Q : ProbabilityMeasure (SpinField N), ∃ ν : ProbabilityMeasure Momentum,
          AdaptedVariationLimit N (fun n => sides (l n)) K Q ∧ ShiftInvariant Q ∧
          (∀ z, spectralPair (ν : Measure Momentum) z = fieldPair Q z) ∧
          (∫ k, interactionMultiplier H hH k ∂(μ : Measure Momentum)) ≤
            ∫ k, interactionMultiplier H hH k ∂(ν : Measure Momentum) := by
  obtain ⟨P,μ,l,hl,hstat,hP,hμ,hvar⟩ := common_cubic_variational_state N J hJ sides hsides
  exact ⟨P,μ,l,hl,hstat,gibbs_of_cubic_fixed N (fun n => sides (l n))
    (hsides.comp hl.tendsto_atTop) J hJ heven P hP,hP,hμ,hvar⟩

end IsingScaling.Rotor.PressureSelection.LocalGibbs

#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.continuous_nearestResample
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.nearest_gibbs_of_weak_l1_limits
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.isGibbs_iff_kernel
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.finite_gibbs_conditional
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.periodized_conditional_error

#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.gibbs_of_cubic_periodic_weak_l1_limit
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.nearest_gibbs_of_cubic_periodic
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.gibbs_of_cubic_periodic_summable
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.nearest_gibbs_of_weak_cubic_states
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.kernel_inter_outside
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.common_cubic_variational_gibbs_state
#print axioms IsingScaling.Rotor.PressureSelection.LocalGibbs.nearestCoupling_at_pair
