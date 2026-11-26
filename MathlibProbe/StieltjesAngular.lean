import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Compactified Stieltjes profiles for the packet limit in AS-8.
The coordinate u=1/(1+s) puts the additive constant at u=0. -/

noncomputable section
open Filter Set MeasureTheory Topology
open scoped NNReal

namespace IsingRotation.Stieltjes

abbrev Parameter := Icc (0:ℝ) 1
abbrev Frequency := Ioi (0:ℝ)

private theorem denom_pos (z : Frequency) (u : Parameter) :
    0 < 1 - (u:ℝ) + u * (z:ℝ) := by
  rcases eq_or_lt_of_le u.2.1 with hu | hu
  · simp [← hu]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr u.2.2) (mul_pos hu z.2)

def kernel (z : Frequency) : C(Parameter, ℝ) where
  toFun u := (1 - (u:ℝ) + u * (z:ℝ))⁻¹
  continuous_toFun := by
    apply Continuous.inv₀
    · fun_prop
    · exact fun u => (denom_pos z u).ne'

def profile (μ : FiniteMeasure Parameter) (z : Frequency) : ℝ :=
  ∫ u, kernel z u ∂(μ : Measure Parameter)

/-- The compactification absorbs the weight (1+s)⁻¹ into the finite measure. -/
theorem kernel_at_finite (z : Frequency) (s : ℝ) (hs : 0 ≤ s) :
    ∃ u : Parameter, (u:ℝ) = (1+s)⁻¹ ∧ kernel z u = (1+s)/(z+s) := by
  have h : 0 < 1+s := by linarith
  have hz : 0 < (z:ℝ)+s := add_pos_of_pos_of_nonneg z.2 hs
  refine ⟨⟨(1+s)⁻¹, inv_nonneg.mpr h.le, inv_le_one_of_one_le₀ (by linarith)⟩, rfl, ?_⟩
  change (1 - (1+s)⁻¹ + (1+s)⁻¹ * (z:ℝ))⁻¹ = _
  calc _ = (((z:ℝ)+s)/(1+s))⁻¹ := by
            congr 1
            field_simp [h.ne']
            ring
       _ = _ := inv_div ..

@[simp] theorem kernel_at_infinity (z : Frequency) :
    kernel z ⟨0, by norm_num⟩ = 1 := by simp [kernel]

@[simp] theorem profile_one (μ : FiniteMeasure Parameter) :
    profile μ ⟨1, by norm_num⟩ = (μ.mass : ℝ) := by
  have hone (u : Parameter) : kernel ⟨1, by norm_num⟩ u = 1 := by
    simp [kernel]
  unfold profile
  simp only [hone, integral_const, smul_eq_mul, mul_one]
  rfl

theorem continuous_profile : Continuous profile := by
  apply continuous_pi
  exact fun z => FiniteMeasure.continuous_integral_continuousMap (kernel z)

/-- Packet shapes may have arbitrary frequencies and measures. A common bound
at z=1 puts the profiles in one compact subset of the full pointwise space. -/
theorem exists_profile_of_tendsto (μ : ℕ → FiniteMeasure Parameter)
    (C : ℝ≥0) (hC : ∀ n, profile (μ n) ⟨1, by norm_num⟩ ≤ (C:ℝ))
    (f : Frequency → ℝ)
    (hf : ∀ z, Tendsto (fun n => profile (μ n) z) atTop (𝓝 (f z))) :
    ∃ ν : FiniteMeasure Parameter, ν.mass ≤ C ∧ profile ν = f := by
  have closed := ((isCompact_setOfPred_finiteMeasure_le_of_compactSpace
    Parameter C).image continuous_profile).isClosed
  apply closed.mem_of_tendsto (tendsto_pi_nhds.mpr hf)
  filter_upwards with n
  exact ⟨μ n, by simpa using hC n, rfl⟩

/-- Complex denominator on the compact energy coordinate. -/
def denominator (z : ℂ) (u : Parameter) : ℂ := 1 - (u:ℝ) + (u:ℝ) * z

private theorem denominator_ne {z : ℂ} (hz : z ∈ Complex.slitPlane) (u : Parameter) :
    denominator z u ≠ 0 := by
  intro h
  rcases eq_or_lt_of_le u.2.1 with hu | hu
  · simp [denominator, ← hu] at h
  · rcases Complex.mem_slitPlane_iff.mp hz with hre | him
    · have heq := congrArg Complex.re h
      simp [denominator] at heq
      have hpos := mul_pos hu hre
      linarith [u.2.2]
    · have heq := congrArg Complex.im h
      simp [denominator, hu.ne', him] at heq

def extension (μ : FiniteMeasure Parameter) (z : ℂ) : ℂ :=
  ∫ u, (denominator z u)⁻¹ ∂(μ : Measure Parameter)

theorem extension_posReal (μ : FiniteMeasure Parameter) (z : Frequency) :
    extension μ (z:ℝ) = (profile μ z : ℂ) := by
  unfold extension profile
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  simp [denominator, kernel]

/-- The extension is holomorphic on the whole slit plane, including at
positive real frequencies. A compact product with the entire parameter
interval supplies a uniform local derivative bound for differentiation
under the integral. -/
theorem differentiableOn_extension (μ : FiniteMeasure Parameter) :
    DifferentiableOn ℂ (extension μ) Complex.slitPlane := by
  intro z hz
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Complex.isOpen_slitPlane.mem_nhds hz)
  let S := Metric.closedBall z r
  let derivK (w : ℂ) (u : Parameter) : ℂ := -((u:ℝ):ℂ) / (denominator w u)^2
  have hcont {w : ℂ} (hw : w ∈ Complex.slitPlane) :
      Continuous (fun u : Parameter => (denominator w u)⁻¹) := by
    apply Continuous.inv₀ (by unfold denominator; fun_prop)
    exact denominator_ne hw
  have hdcont : ContinuousOn (fun p : ℂ × Parameter => derivK p.1 p.2)
      (S ×ˢ univ) := by
    apply ContinuousOn.div
    · fun_prop
    · unfold denominator
      fun_prop
    · intro p hp
      exact pow_ne_zero _ (denominator_ne (hsub hp.1) p.2)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall z r).prod
    (isCompact_univ : IsCompact (univ : Set Parameter))).exists_bound_of_continuousOn hdcont
  have hder {w : ℂ} (hw : w ∈ Complex.slitPlane) (u : Parameter) :
      HasDerivAt (fun t => (denominator t u)⁻¹) (derivK w u) w := by
    have hd : HasDerivAt (fun t => denominator t u) ((u:ℝ):ℂ) w := by
      unfold denominator
      exact (hasDerivAt_const_mul ((u:ℝ):ℂ)).const_add _
    exact hd.inv (denominator_ne hw u)
  have hmeas : Continuous (derivK z) := by
    apply Continuous.div
    · fun_prop
    · unfold denominator
      fun_prop
    · exact fun u => pow_ne_zero _ (denominator_ne hz u)
  apply DifferentiableAt.differentiableWithinAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (μ:Measure Parameter))
    (F := fun w u => (denominator w u)⁻¹) (F' := derivK)
    (bound := fun _ => M) (Metric.closedBall_mem_nhds z hr)
    (by filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
        exact (hcont hw).aestronglyMeasurable)
    ((hcont hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hmeas.aestronglyMeasurable
    (ae_of_all _ (fun u w hw => hM (w,u) ⟨hw, mem_univ _⟩))
    (integrable_const M)
    (ae_of_all _ (fun u w hw => hder (hsub hw) u))).2.differentiableAt

/-- Off the real axis the normalized Stieltjes kernel has a uniform
resolvent bound, even when its compact parameter approaches either endpoint. -/
theorem norm_kernel_le (z : ℂ) (hz : z.im ≠ 0) (u : Parameter) :
    ‖(denominator z u)⁻¹‖ ≤ 1 + ‖1-z‖/|z.im| := by
  have hd := denominator_ne (Complex.mem_slitPlane_iff.mpr (Or.inr hz)) u
  have hn : 0 < ‖denominator z u‖ := norm_pos_iff.mpr hd
  have hi : 0 < |z.im| := abs_pos.mpr hz
  have him : (u:ℝ) * |z.im| ≤ ‖denominator z u‖ := by
    simpa [denominator, abs_mul, abs_of_nonneg u.2.1] using
      (Complex.abs_im_le_norm (denominator z u))
  have hsum : 1 ≤ ‖denominator z u‖ + (u:ℝ) * ‖1-z‖ := by
    calc (1:ℝ) = ‖denominator z u + ((u:ℝ):ℂ)*(1-z)‖ := by
                  simp only [denominator]; ring_nf; simp
         _ ≤ _ := by
           simpa [norm_mul, abs_of_nonneg u.2.1, Real.norm_eq_abs] using
             norm_add_le (denominator z u) (((u:ℝ):ℂ)*(1-z))
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hn]
  have hule := (le_div_iff₀ hi).mpr him
  calc (1:ℝ) ≤ _ := hsum
       _ ≤ ‖denominator z u‖ + (‖denominator z u‖/|z.im|) * ‖1-z‖ :=
         by gcongr
       _ = _ := by ring

theorem norm_extension_le (μ : FiniteMeasure Parameter) (z : ℂ) (hz : z.im ≠ 0) :
    ‖extension μ z‖ ≤ (μ.mass:ℝ) * (1 + ‖1-z‖/|z.im|) := by
  rw [mul_comm]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ (norm_kernel_le z hz))

/-- Positive-time packet spectrum after the normal Fourier transform,
including a fixed spatial contact contribution. The only mass assumption
is finiteness of the weighted spectrum at unit squared frequency. -/
def energyWeight (E : ℝ≥0) : ℝ≥0 := 2 * E / (1+E^2)

def energyCoord (E : ℝ≥0) : Parameter :=
  ⟨(1 + (E:ℝ)^2)⁻¹, by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (E:ℝ)])⟩

theorem profile_from_packet (ρ : Measure ℝ≥0) (contact : ℝ≥0)
    (hρ : (∫⁻ E, (energyWeight E : ENNReal) ∂ρ) < ⊤) :
    ∃ ν : FiniteMeasure Parameter, ∀ z : Frequency,
      profile ν z = (contact:ℝ) + ∫ E : ℝ≥0, 2*(E:ℝ)/((z:ℝ)+(E:ℝ)^2) ∂ρ := by
  let τ : Measure ℝ≥0 := ρ.withDensity (fun E => (energyWeight E : ENNReal))
  have : IsFiniteMeasure τ := ⟨by simpa [τ, withDensity_apply _ MeasurableSet.univ] using hρ⟩
  have hcoord : Continuous energyCoord := by
    apply Continuous.subtype_mk
    apply Continuous.inv₀ (by fun_prop)
    intro x
    positivity
  let atom : Measure Parameter := (contact : ENNReal) •
    Measure.dirac (⟨0, by norm_num⟩ : Parameter)
  have : IsFiniteMeasure atom := by dsimp [atom]; infer_instance
  refine ⟨⟨atom + τ.map energyCoord, inferInstance⟩, ?_⟩
  intro z
  have hint (ν : Measure Parameter) [IsFiniteMeasure ν] : Integrable (kernel z) ν :=
    (kernel z).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change ∫ u, kernel z u ∂(atom + τ.map energyCoord) = _
  rw [integral_add_measure (hint _) (hint _), integral_map hcoord.aemeasurable
    (kernel z).continuous.aestronglyMeasurable]
  have hatom : (∫ u, kernel z u ∂atom) = (contact:ℝ) := by
    simp [atom, kernel, NNReal.smul_def]
  rw [hatom]
  congr 1
  have hw : Measurable energyWeight := by unfold energyWeight; fun_prop
  unfold τ
  rw [integral_withDensity_eq_integral_smul hw]
  apply integral_congr_ae
  filter_upwards with E
  obtain ⟨u, he, hkernel⟩ := kernel_at_finite z ((E:ℝ)^2) (sq_nonneg _)
  have heu : energyCoord E = u := Subtype.ext he.symm
  rw [heu, hkernel]
  change (energyWeight E : ℝ) * _ = _
  simp only [energyWeight, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat]
  have h : (1:ℝ)+(E:ℝ)^2 ≠ 0 := by positivity
  field_simp [h]

/-- The AS-8 packet-localization implication. Pointwise convergence at unit
squared frequency itself bounds all masses needed for compactness. The
limit has one representing positive measure for all positive frequencies. -/
theorem packet_limit_has_stieltjes_extension (ρ : ℕ → Measure ℝ≥0)
    (contact : ℕ → ℝ≥0)
    (hρ : ∀ n, (∫⁻ E, (energyWeight E : ENNReal) ∂(ρ n)) < ⊤)
    (f : Frequency → ℝ)
    (hf : ∀ z : Frequency, Tendsto
      (fun n => (contact n : ℝ) +
        ∫ E : ℝ≥0, 2*(E:ℝ)/((z:ℝ)+(E:ℝ)^2) ∂(ρ n)) atTop (𝓝 (f z))) :
    ∃ ν : FiniteMeasure Parameter, profile ν = f ∧
      DifferentiableOn ℂ (extension ν) Complex.slitPlane ∧
      (∀ z : Frequency, extension ν (z:ℝ) = (f z:ℂ)) ∧
      ∀ z : ℂ, z.im ≠ 0 →
        ‖extension ν z‖ ≤ f ⟨1, by norm_num⟩ * (1+‖1-z‖/|z.im|) := by
  choose μ hμ using fun n => profile_from_packet (ρ n) (contact n) (hρ n)
  have ht (z : Frequency) : Tendsto (fun n => profile (μ n) z) atTop (𝓝 (f z)) := by
    simpa only [hμ] using hf z
  obtain ⟨C, hC⟩ := (ht ⟨1, by norm_num⟩).bddAbove_range
  obtain ⟨ν, _, hν⟩ := exists_profile_of_tendsto μ C.toNNReal
    (fun n => (hC (Set.mem_range_self n)).trans (Real.le_coe_toNNReal _)) f ht
  refine ⟨ν, hν, differentiableOn_extension ν, ?_, ?_⟩
  · intro z
    rw [extension_posReal, hν]
  · intro z hz
    rw [← hν, profile_one]
    exact norm_extension_le ν z hz

/-- Holomorphy under the AS-6 integral from local domination of the values.
Derivative measurability follows from slopes on the punctured neighbourhood,
and their local integrable bound follows from Cauchy's first estimate. -/
theorem differentiableOn_integral_of_local_domination
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {S : Set ℂ} (hS : IsOpen S) (F : ℂ → α → ℂ)
    (hm : ∀ z ∈ S, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ u ∂μ, DifferentiableOn ℂ (fun z => F z u) S)
    (hb : ∀ z ∈ S, ∃ r > 0, ∃ G : α → ℝ, Integrable G μ ∧
      ∀ᵐ u ∂μ, ∀ w ∈ Metric.closedBall z r, ‖F w u‖ ≤ G u) :
    DifferentiableOn ℂ (fun z => ∫ u, F z u ∂μ) S := by
  classical
  intro z hz
  obtain ⟨r₀, hr₀, hS₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds hz)
  obtain ⟨r, hr, G, hG, hbound⟩ := hb z hz
  let δ := min r₀ r / 2
  have hδ : 0 < δ := half_pos (lt_min hr₀ hr)
  have hball {w : ℂ} (hw : w ∈ Metric.closedBall z δ) :
      Metric.closedBall w δ ⊆ Metric.closedBall z (min r₀ r) := by
    apply Metric.closedBall_subset_closedBall'
    have hh : dist w z ≤ δ := hw
    dsimp [δ] at *
    linarith
  have hsub₀ := Metric.closedBall_subset_closedBall (x := z) (min_le_left r₀ r)
  have hsub := Metric.closedBall_subset_closedBall (x := z) (min_le_right r₀ r)
  let dF (w : ℂ) (u : α) := deriv (fun t => F t u) w
  have hdm : AEStronglyMeasurable (dF z) μ := by
    let slopes (t : ℂ) (u : α) := if t ∈ S then slope (fun x => F x u) z t else 0
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z) (f := slopes)
    · intro t
      by_cases ht : t ∈ S
      · simpa [slopes, ht, slope_def_field, div_eq_mul_inv] using
          (((hm t ht).sub (hm z hz)).mul_const ((t-z)⁻¹))
      · simpa [slopes, ht] using (aestronglyMeasurable_const (b := (0:ℂ)) (μ := μ))
    · filter_upwards [hd] with u hu
      apply ((hu.differentiableAt (hS.mem_nhds hz)).hasDerivAt.tendsto_slope).congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hS.mem_nhds hz)] with t ht
      simp [slopes, ht]
  have hint : Integrable (F z) μ := hG.mono' (hm z hz) (by
    filter_upwards [hbound] with u hu
    exact hu z (Metric.mem_closedBall_self hr.le))
  apply DifferentiableAt.differentiableWithinAt
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := dF)
      (bound := fun u => G u / δ) (Metric.closedBall_mem_nhds z hδ)
      (by filter_upwards [hS.mem_nhds hz] with w hw; exact hm w hw)
      hint hdm _ (hG.div_const δ) _).2.differentiableAt
  · filter_upwards [hd,hbound] with u hu hGu
    intro w hw
    have hin := hball hw
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hu.diffContOnCl_ball ((hin.trans hsub₀).trans hS₀))
    intro t ht
    exact hGu t (hsub (hin (Metric.sphere_subset_closedBall ht)))
  · filter_upwards [hd] with u hu
    intro w hw
    have hwS := hS₀ (hsub₀ (hball hw (Metric.mem_closedBall_self hδ.le)))
    exact (hu.differentiableAt (hS.mem_nhds hwS)).hasDerivAt

/-- Uniform bound for all positive mixture measures of a given mass on
each compact subset of the slit plane. -/
theorem extension_bdd_compact {K : Set ℂ} (hK : IsCompact K)
    (hs : K ⊆ Complex.slitPlane) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : FiniteMeasure Parameter, ∀ z ∈ K,
      ‖extension μ z‖ ≤ C * (μ.mass:ℝ) := by
  have hcont : ContinuousOn (fun p : ℂ × Parameter => (denominator p.1 p.2)⁻¹)
      (K ×ˢ univ) := by
    apply ContinuousOn.inv₀
    · unfold denominator
      fun_prop
    · exact fun p hp => denominator_ne (hs hp.1) p.2
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_univ : IsCompact (univ : Set Parameter))
      ).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro μ z hz
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun u =>
    (hC (z,u) ⟨hz, mem_univ _⟩).trans (le_max_left C 0))

private theorem extension_congr {μ ν : FiniteMeasure Parameter} (h : profile μ = profile ν) :
    EqOn (extension μ) (extension ν) Complex.slitPlane := by
  apply ((differentiableOn_extension μ).analyticOnNhd Complex.isOpen_slitPlane
    ).eqOn_of_preconnected_of_frequently_eq
      ((differentiableOn_extension ν).analyticOnNhd Complex.isOpen_slitPlane)
      (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
      Complex.one_mem_slitPlane
  have ht : Tendsto Complex.ofReal (𝓝[≠] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
       (fun x hx => by simpa using hx) :
         Tendsto Complex.ofReal (𝓝[≠] (1:ℝ)) (𝓝[≠] ((1:ℝ):ℂ)))
  apply ht.frequently
  apply Filter.Eventually.frequently
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (zero_lt_one : (0:ℝ)<1))]
     with x hx
  change extension μ ((⟨x,hx⟩ : Frequency):ℝ) = extension ν ((⟨x,hx⟩ : Frequency):ℝ)
  rw [extension_posReal, extension_posReal, h]

private theorem continuous_extension_measure {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Continuous (fun μ : FiniteMeasure Parameter => extension μ z) := by
  let K : C(Parameter, ℂ) := ⟨fun u => (denominator z u)⁻¹,
    Continuous.inv₀ (by unfold denominator; fun_prop) (denominator_ne hz)⟩
  let a : C(Parameter, ℝ) := ⟨_, Complex.continuous_re.comp K.continuous⟩
  let b : C(Parameter, ℝ) := ⟨_, Complex.continuous_im.comp K.continuous⟩
  have ha := Complex.continuous_ofReal.comp (FiniteMeasure.continuous_integral_continuousMap a)
  have hb := Complex.continuous_ofReal.comp (FiniteMeasure.continuous_integral_continuousMap b)
  apply (ha.add (hb.mul_const Complex.I)).congr
  intro μ
  have hint : Integrable (K : Parameter → ℂ) (μ:Measure Parameter) :=
    K.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (((∫ u, (K u).re ∂(μ:Measure Parameter)) : ℝ):ℂ) +
       (((∫ u, (K u).im ∂(μ:Measure Parameter)) : ℝ):ℂ) * Complex.I = _
  rw [show (∫ u, (K u).re ∂(μ:Measure Parameter)) = (∫ u, K u ∂(μ:Measure Parameter)).re from
        integral_re hint,
      show (∫ u, (K u).im ∂(μ:Measure Parameter)) = (∫ u, K u ∂(μ:Measure Parameter)).im from
        integral_im hint, Complex.re_add_im]
  rfl

/-- Arbitrary choices of representing measures for a continuous family of
real profiles yield the same continuous complex values on the slit. No
measurable choice of measures is required. -/
theorem continuous_extension_family {X : Type*} [TopologicalSpace X]
    (ν : X → FiniteMeasure Parameter) (M : ℝ≥0) (hM : ∀ w, (ν w).mass ≤ M)
    (hreal : ∀ x, Continuous fun w => profile (ν w) x)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Continuous fun w => extension (ν w) z := by
  apply continuous_iff_isClosed.mpr
  intro A hA
  let K := {μ : FiniteMeasure Parameter | μ.mass ≤ M} ∩
           (fun μ => extension μ z) ⁻¹' A
  have hK : IsCompact K :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace Parameter M).inter_right
      (hA.preimage (continuous_extension_measure hz))
  have hc : Continuous (fun w => profile (ν w)) := continuous_pi hreal
  have heq : (fun w => extension (ν w) z) ⁻¹' A =
      (fun w => profile (ν w)) ⁻¹' (profile '' K) := by
    ext w
    constructor
    · intro hw
      exact ⟨ν w, ⟨hM w,hw⟩,rfl⟩
    · rintro ⟨μ, hμ, he⟩
      change extension (ν w) z ∈ A
      rw [← extension_congr he hz]
      exact hμ.2
  rw [heq]
  exact (hK.image continuous_profile).isClosed.preimage hc

private lemma shifted_exp_norm (b w : ℝ) (hb : 0 < b) (l : ℂ) :
    ‖Complex.exp (-(b:ℂ)*((w:ℂ)-l)^2)‖ ≤
      Real.exp (b*‖l‖^2) * Real.exp (-(b/2)*w^2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_sub, neg_zero, zero_mul, sub_zero]
  nlinarith [mul_nonneg hb.le (sq_nonneg (w-2*l.re))]

/-- AS-6 in a local complex chart, before the strip coordinate is
specified. Its hypotheses concern the real packet index and the two
complex scalar coordinates. No domination or integrability of a
derivative of the Gaussian or the Stieltjes transform is assumed. -/
theorem gaussian_stieltjes_chart_holomorphic (b : ℝ) (hb : 0 < b)
    {S : Set ℂ} (hs : IsOpen S) (l k : ℂ → ℂ)
    (hl : DifferentiableOn ℂ l S) (hk : DifferentiableOn ℂ k S)
    (hks : MapsTo k S Complex.slitPlane) (ν : ℝ → FiniteMeasure Parameter)
    (M : ℝ) (hM : ∀ w, ((ν w).mass:ℝ) ≤ M)
    (hmeas : ∀ z ∈ S, AEStronglyMeasurable
      (fun w => extension (ν w) (k z)) volume) :
    DifferentiableOn ℂ
      (fun z => ∫ w : ℝ, Complex.exp (-(b:ℂ)*((w:ℂ)-l z)^2) *
                           extension (ν w) (k z)) S := by
  let F (z : ℂ) (w : ℝ) := Complex.exp (-(b:ℂ)*((w:ℂ)-l z)^2) * extension (ν w) (k z)
  apply differentiableOn_integral_of_local_domination volume hs F
  · intro z hz
    apply AEStronglyMeasurable.mul _ (hmeas z hz)
    apply Continuous.aestronglyMeasurable
    fun_prop
  · apply ae_of_all
    intro w
    apply DifferentiableOn.mul _ ((differentiableOn_extension _).comp hk hks)
    fun_prop
  · intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
    have hK := isCompact_closedBall z r
    obtain ⟨C, hC, hbound⟩ := extension_bdd_compact
      (hK.image_of_continuousOn (hk.continuousOn.mono hball))
      (show k '' Metric.closedBall z r ⊆ Complex.slitPlane from
        fun x ⟨y,hy,he⟩ => he ▸ hks (hball hy))
    obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (hl.continuousOn.mono hball)
    refine ⟨r, hr, fun w => (Real.exp (b*L^2)*(C*M))*Real.exp (-(b/2)*w^2),
      (integrable_exp_neg_mul_sq (half_pos hb)).const_mul _, ?_⟩
    apply ae_of_all
    intro w y hy
    have ha := hL y hy
    have hbnd := (hbound (ν w) _ (mem_image_of_mem _ hy)).trans
      (mul_le_mul_of_nonneg_left (hM w) hC)
    have hexp : Real.exp (b*‖l y‖^2) ≤ Real.exp (b*L^2) := by
      gcongr
    dsimp only [F]
    rw [norm_mul]
    calc _ ≤ (Real.exp (b*L^2)*Real.exp (-(b/2)*w^2))*(C*M) :=
            mul_le_mul ((shifted_exp_norm b w hb (l y)).trans
              (mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le))
              hbnd (norm_nonneg _) (by positivity)
         _ = _ := by ring

end IsingRotation.Stieltjes
