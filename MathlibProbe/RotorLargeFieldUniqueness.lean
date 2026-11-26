import MathlibProbe.RotorHeisenbergFreeCubeDLR
import MathlibProbe.RotorDobrushinComparison
import MathlibProbe.RotorLargeFieldConcentration
import Mathlib.MeasureTheory.Integral.Pi

/-! # Positive-field Dobrushin comparison for the physical Heisenberg specification

The one-site operator on the full configuration space is disintegrated into an
integral over one spin with the other sites held fixed. Its six exterior spins
give precisely the six interaction terms of the field specification. For fixed
nonnegative inverse temperature, high-field concentration makes the difference
between any two such one-site laws smaller than one twelfth on unit readouts.
Thus the sum of site influences is at most one half. Compactness supplies a
Gibbs accumulation point of the actual free cubes, and uniqueness identifies
all their subsequential limits, including each fixed two-site dot product.
-/

noncomputable section
open MeasureTheory Filter
open scoped Classical Topology InnerProductSpace

namespace IsingScaling.Rotor.HeisenbergField.LargeField
open PressureSelection LocalGibbs DobrushinComparison

private abbrev stepCount := Fintype.card ↥nearestSteps

private def steps : Fin stepCount ≃ ↥nearestSteps :=
  (Fintype.equivFin ↥nearestSteps).symm

private theorem stepCount_le : stepCount ≤ 6 := by
  change Fintype.card ↥nearestSteps ≤ 6
  rw [Fintype.card_coe]
  exact (Finset.card_image_le).trans (by decide)

private def neighbors (i : Site) := nearestSteps.image (fun z => i+z)

private theorem degree_bound (i : Site) : (neighbors i).card ≤ 6 :=
  Finset.card_image_le.trans (by simpa [stepCount] using stepCount_le)

private theorem step_ne (i : Site) (k : Fin stepCount) : i + (steps k).val ≠ i := by
  intro he
  have hz : (steps k).val = 0 := by
    apply add_left_cancel (a := i)
    simpa only [add_zero] using he
  have h := (mem_nearestSteps_iff_latticeDistance _).mp (steps k).property
  simp [hz, latticeDistance] at h

private def env (i : Site) (s : SpinField 3) (k : Fin stepCount) : Spin 3 :=
  s (i + (steps k).val)

private def one (i : Site) (s : SpinField 3) (v : Spin 3) : SpinField 3 :=
  Function.update s i v

private theorem one_cont (i : Site) (s : SpinField 3) : Continuous (one i s) :=
  continuous_const.update i continuous_id

private def energy (β h : ℝ) (a : Fin stepCount → Spin 3) (v : Spin 3) :=
  h * v.val 0 + ∑ k, β * ⟪(a k).val, v.val⟫_ℝ

private theorem energy_cont (β h : ℝ) (a : Fin stepCount → Spin 3) :
    Continuous (energy β h a) := by unfold energy; fun_prop

private def law (β h : ℝ) (a : Fin stepCount → Spin 3) : Measure (Spin 3) :=
  (SiteReflection.surfacePrior 3).tilted (energy β h a)

private instance law_prob (β h : ℝ) (a : Fin stepCount → Spin 3) :
    IsProbabilityMeasure (law β h a) :=
  isProbabilityMeasure_tilted ((energy_cont β h a).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

private theorem singleton_energy (β h : ℝ) (i : Site) (s : SpinField 3) :
    localFieldEnergy β h {i} s = energy β h (env i s) (s i) := by
  let H (x z : Site) := nearestCoupling β z * ((if x + z ∈ ({i} : Finset Site)
    then (1 : ℝ) / 2 else 1) * ⟪(s x).val, (s (x+z)).val⟫_ℝ)
  have hpair : nearestEnergy β {i} s = ∑ z ∈ nearestSteps, β * ⟪(s (i+z)).val,(s i).val⟫_ℝ := by
    change (∑ x : ↥({i} : Finset Site), ∑' z, H x.val z) = _
    rw [Finset.sum_coe_sort {i} (fun x => ∑' z, H x z), Finset.sum_singleton]
    rw [tsum_eq_sum (s := nearestSteps) (fun z hz => by simp [H, nearestCoupling, hz])]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hne : z ≠ 0 := by
      rintro rfl
      simpa [latticeDistance] using (mem_nearestSteps_iff_latticeDistance 0).mp hz
    simp [H, nearestCoupling, hz, hne, real_inner_comm (s i).val]
  have hsum := steps.sum_comp (fun z : ↥nearestSteps => β * ⟪(s (i+z.val)).val,(s i).val⟫_ℝ)
  rw [Finset.sum_coe_sort nearestSteps (fun z => β * ⟪(s (i+z)).val,(s i).val⟫_ℝ)] at hsum
  change nearestEnergy β {i} s + (∑ x : ↥({i} : Finset Site), siteField h (s x)) = _
  rw [hpair, Finset.sum_coe_sort {i} (fun x => siteField h (s x)), Finset.sum_singleton]
  simp only [energy, env, siteField, hsum, add_comm]

private theorem env_one (i : Site) (s : SpinField 3) (v : Spin 3) : env i (one i s v) = env i s := by
  funext k
  exact Function.update_of_ne (step_ne i k) _ _

private abbrev K (β h : ℝ) (i : Site) (F : C(SpinField 3, ℝ)) :=
  readout {i} (localFieldEnergy β h {i}) F

private theorem K_read (β h : ℝ) (i : Site) (F : C(SpinField 3, ℝ)) (s : SpinField 3) :
    K β h i F s = ∫ v, F (one i s v) ∂law β h (env i s) := by
  let p : ↥({i} : Finset Site) := ⟨i, by simp⟩
  have rep (a : WindowSpin 3 {i}) : replace {i} s a = one i s (a p) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [replace, one, p]
    · simp [replace, one, hj]
  have e (v : Spin 3) : localFieldEnergy β h {i} (one i s v) = energy β h (env i s) v := by
    rw [singleton_energy, env_one]
    simp [one]
  have eval (g : Spin 3 → ℝ) (hg : Continuous g) :
      (∫ a : WindowSpin 3 {i}, g (a p) ∂(windowPrior 3 {i} : Measure _)) =
        ∫ v, g v ∂SiteReflection.surfacePrior 3 :=
    integral_comp_eval (μ := fun _ : ↥({i} : Finset Site) => SiteReflection.surfacePrior 3)
      hg.aestronglyMeasurable
  change (∫ t, F t ∂(resample {i} (localFieldEnergy β h {i}) s : Measure _)) = _
  rw [resample_integral]
  change ((∫ a, Real.exp (localFieldEnergy β h {i} (replace {i} s a)) * F (replace {i} s a)
    ∂(windowPrior 3 {i} : Measure _)) /
    ∫ a, Real.exp (localFieldEnergy β h {i} (replace {i} s a)) ∂(windowPrior 3 {i} : Measure _)) = _
  simp only [rep, e]
  rw [eval (fun v => Real.exp (energy β h (env i s) v) * F (one i s v))
    ((energy_cont β h _).rexp.mul (F.continuous.comp (one_cont i s))),
    eval (fun v => Real.exp (energy β h (env i s) v)) (energy_cont β h _).rexp]
  simp [law, integral_tilted, smul_eq_mul, div_mul_eq_mul_div, integral_div]

private def Closeness (β h d : ℝ) : Prop :=
  ∀ (a b : Fin stepCount → Spin 3) (F : Spin 3 → ℝ), Measurable F → (∀ s, |F s| ≤ 1) →
    |(∫ s, F s ∂law β h a) - ∫ s, F s ∂law β h b| ≤ d

private theorem centered {β h d : ℝ} (hc : Closeness β h d)
    (a b : Fin stepCount → Spin 3) {u : ℝ} (F : C(Spin 3, ℝ))
    (hF : ∀ z, |F z-F firstSpin| ≤ u) :
    |(∫ z, F z ∂law β h a) - ∫ z, F z ∂law β h b| ≤ d * u := by
  have hu : 0 ≤ u := by simpa using hF firstSpin
  rcases hu.eq_or_lt with he | hp
  · subst u
    have H (z) : F z = F firstSpin := sub_eq_zero.mp (abs_nonpos_iff.mp (hF z))
    simp_rw [H]; simp
  let J (z : Spin 3) := (F z - F firstSpin)/u
  have H := hc a b J ((F.continuous.sub continuous_const).div_const _).measurable
    (fun z => by simpa [J, abs_div, abs_of_pos hp, div_le_iff₀ hp] using hF z)
  have hI (c : Fin stepCount → Spin 3) :
      (∫ z, J z ∂law β h c) = ((∫ z, F z ∂law β h c)-F firstSpin)/u := by
    simp [J, integral_div, integral_sub (F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  rw [hI, hI, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hp, div_le_iff₀ hp] at H
  exact H

private theorem other {β h d : ℝ} (hc : Closeness β h d) (i j : Site) (F : C(SpinField 3, ℝ))
    (a b : ℝ) (_hji : j ≠ i) (hi : CoordBound F i a) (hj : CoordBound F j b) :
    CoordBound (K β h i F) j (b + if j ∈ neighbors i then d*a else 0) := by
  intro s t hst
  let Fs : C(Spin 3, ℝ) := ⟨fun v => F (one i s v), F.continuous.comp (one_cont i s)⟩
  let Ft : C(Spin 3, ℝ) := ⟨fun v => F (one i t v), F.continuous.comp (one_cont i t)⟩
  have hosc (v : Spin 3) : |Fs v - Fs firstSpin| ≤ a := by
    apply hi
    intro x hx; simp [one, hx]
  have hbase (v : Spin 3) : |Fs v-Ft v| ≤ b := by
    apply hj
    intro x hx
    by_cases hxi : x = i
    · subst x; simp [one]
    · simp [one, hxi, hst x hx]
  have hterm : |(∫ v, Fs v ∂law β h (env i t)) - ∫ v, Ft v ∂law β h (env i t)| ≤ b := by
    rw [← integral_sub (Fs.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Ft.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    simpa [Real.norm_eq_abs, measureReal_def] using norm_integral_le_of_norm_le_const
      (μ := law β h (env i t)) (f := fun v => Fs v - Ft v)
      (Eventually.of_forall hbase)
  rw [K_read, K_read]
  change |(∫ v, Fs v ∂law β h (env i s)) - ∫ v, Ft v ∂law β h (env i t)| ≤ _
  by_cases hn : j ∈ neighbors i
  · rw [ite_eq_left hn, add_comm b]
    exact (abs_sub_le _ _ _).trans (add_le_add (centered hc _ _ Fs hosc) hterm)
  · have e : env i s = env i t := by
      funext k
      apply hst
      intro he
      exact hn (he ▸ Finset.mem_image.mpr ⟨(steps k).val,(steps k).property,rfl⟩)
    simpa [e, hn] using hterm

private theorem field_eq_of_close {β h d : ℝ} (hd : 0 ≤ d) (hsmall : 6*d < 1)
    (hc : Closeness β h d) {P Q : ProbabilityMeasure (SpinField 3)}
    (hP : IsFieldGibbs β h P) (hQ : IsFieldGibbs β h Q) : P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_site_bounds neighbors 6 degree_bound d hd hsmall (K β h) _
    (other hc) (P : Measure _) (Q : Measure _)
  · exact fun i F => (hP {i} F).symm
  · exact fun i F => (hQ {i} F).symm
  · intro i F s t hst
    rw [K_read, K_read]
    have e : env i s = env i t := funext fun k => hst _ (step_ne i k)
    have eq (v : Spin 3) : one i s v = one i t v := by
      funext j
      by_cases hj : j = i
      · subst j; simp [one]
      · simp [one, hj, hst j hj]
    simp only [e, eq, sub_self, abs_zero, le_refl]

/-- For every fixed nonnegative coupling, the physical lattice Heisenberg
specification has a unique infinite-volume Gibbs probability at all sufficiently
large positive external fields. -/
theorem exists_unique_fieldGibbs_eventually {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ h : ℝ in atTop, ∃! P : ProbabilityMeasure (SpinField 3), IsFieldGibbs β h P := by
  filter_upwards [six_neighbour_readouts_eventually_close hβ (ε := 1/12) (by norm_num)] with h hc
  have H : Closeness β h (1/12) := by
    intro a b F hm hf
    have elaw (v : Fin stepCount → Spin 3) :
        law β h v = singleSiteConditional h (neighbourField β v) :=
      (neighbour_conditional_eq h β v).symm
    rw [elaw a, elaw b]
    exact (hc stepCount stepCount stepCount_le stepCount_le a b F hm hf).le
  obtain ⟨P,u,hu,hP,_⟩ := spinField_subsequence 3 (cubeLaw β h)
  have hg := field_gibbs_of_free_cube_limit (β := β) (h := h) hu.tendsto_atTop hP
  exact ⟨P,hg,fun Q hQ => field_eq_of_close (by norm_num) (by norm_num) H hQ hg⟩

/-- Uniqueness identifies the full centered free-cube sequence. -/
theorem cube_tendsto_of_unique {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)}
    (unique : ∀ Q, IsFieldGibbs β h Q → Q=P) : Tendsto (cubeLaw β h) atTop (𝓝 P) := by
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨Q,u,hu,hQ,_⟩ := spinField_subsequence 3 (fun k => cubeLaw β h (f k))
  have hg := field_gibbs_of_free_cube_limit (β := β) (h := h) (hf.comp hu.tendsto_atTop) hQ
  exact ⟨u,unique Q hg ▸ hQ⟩

/-- The same large-field Gibbs probability realizes the full weak limit and the
ordinary free-surface-law two-point limits at every pair of lattice sites. -/
theorem free_cube_and_pairs_eventually {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ h : ℝ in atTop, ∃ P : ProbabilityMeasure (SpinField 3),
      IsFieldGibbs β h P ∧ (∀ Q, IsFieldGibbs β h Q → Q=P) ∧
      Tendsto (cubeLaw β h) atTop (𝓝 P) ∧ ∀ x y : Site,
        Tendsto (fun L => SiteReflection.freePair (fieldPrior h) β L x y)
          atTop (𝓝 (∫ s, fieldDot 3 x y s ∂(P : Measure _))) := by
  filter_upwards [exists_unique_fieldGibbs_eventually hβ] with h H
  obtain ⟨P,hP,unique⟩ := H
  have hlim := cube_tendsto_of_unique unique
  refine ⟨P,hP,unique,hlim,?_⟩
  intro x y
  have hd := (ProbabilityMeasure.continuous_integral_continuousMap
    (fieldDot 3 x y)).continuousAt.tendsto.comp hlim
  apply hd.congr'
  filter_upwards [BondMirror.ev_cube x, BondMirror.ev_cube y] with L hx hy
  exact cubeLaw_pair β h L hx hy

#print axioms exists_unique_fieldGibbs_eventually
#print axioms free_cube_and_pairs_eventually

end IsingScaling.Rotor.HeisenbergField.LargeField
