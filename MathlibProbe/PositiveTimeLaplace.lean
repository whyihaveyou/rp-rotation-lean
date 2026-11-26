import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Ultrafilter
import Mathlib.Tactic.Linarith

/-! Positive-time limits of transfer spectra. The compact coordinate is
the one-unit eigenvalue u=exp(-E). Only the tilted masses need be bounded. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace IsingRotation.Laplace

abbrev Eigenvalue := Icc (0:ℝ≥0) 1
abbrev Time := Ioi (0:ℝ)

private def power (t : ℝ) (x : Eigenvalue) : ℝ≥0∞ := ((x.val ^ t : ℝ≥0) : ℝ≥0∞)

private theorem power_measurable (t : ℝ) (ht : 0 ≤ t) : Measurable (power t) :=
  ENNReal.continuous_coe.measurable.comp
    ((NNReal.continuous_rpow_const ht).comp continuous_subtype_val).measurable

private theorem power_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    power (s+t) = power s * power t := by
  ext x
  simp [power, NNReal.rpow_add_of_nonneg _ hs ht]

private theorem tilted_lintegral_limit (μ : ℕ → Measure Eigenvalue) (H : Time → ℝ≥0)
    (hfin : ∀ n (t : Time), (∫⁻ x, power t x ∂(μ n)) ≠ ⊤)
    (hlim : ∀ t : Time, Tendsto (fun n => ∫⁻ x, power t x ∂(μ n)) atTop (𝓝 (H t : ℝ≥0∞))) :
    ∃ η : Time → FiniteMeasure Eigenvalue, (∀ t, (η t).mass = H t) ∧
      ∀ s t : Time, s.val < t.val →
        (η t : Measure Eigenvalue) = (η s : Measure Eigenvalue).withDensity (power (t.val-s.val)) := by
  let m (n : ℕ) (t : Time) : FiniteMeasure Eigenvalue :=
    ⟨(μ n).withDensity (power t), isFiniteMeasure_withDensity (hfin n t)⟩
  have hm (n : ℕ) (t : Time) :
      ((m n t).mass : ℝ≥0∞) = ∫⁻ x, power t x ∂(μ n) := by
    rw [FiniteMeasure.ennreal_mass]; simp [m, withDensity_apply]
  have hmt (t : Time) : Tendsto (fun n => (m n t).mass) atTop (𝓝 (H t)) := by
    apply ENNReal.tendsto_coe.mp
    simpa only [hm] using hlim t
  choose C hC using fun t => (hmt t).bddAbove_range
  have hK := isCompact_univ_pi (fun t : Time =>
    isCompact_setOfPred_finiteMeasure_le_of_compactSpace Eigenvalue (C t))
  obtain ⟨η, _, hη⟩ := hK.exists_mapClusterPt_of_frequently
    (f := m) (l := atTop) (Filter.Eventually.frequently (Eventually.of_forall
      (fun n t _ => hC t (mem_range_self n))))
  obtain ⟨U, hU, hηlim⟩ := mapClusterPt_iff_ultrafilter.mp hη
  have hl (t : Time) : Tendsto (fun n => m n t) (U : Filter ℕ) (𝓝 (η t)) :=
    (tendsto_pi_nhds.mp hηlim) t
  refine ⟨η, ?_, ?_⟩
  · intro t
    exact tendsto_nhds_unique (FiniteMeasure.continuous_mass.continuousAt.tendsto.comp (hl t))
      ((hmt t).mono_left hU)
  · intro s t hst
    have hr := (sub_pos.mpr hst).le
    have hrec (n : ℕ) :
        (m n t : Measure Eigenvalue) = (m n s : Measure Eigenvalue).withDensity (power (t.val-s.val)) := by
      change (μ n).withDensity _ = ((μ n).withDensity _).withDensity _
      rw [← withDensity_mul _ (power_measurable _ s.2.le) (power_measurable _ hr),
        ← power_add _ _ s.2.le hr, show s.val + (t.val-s.val) = t.val by ring]
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro f
    let g : C(Eigenvalue, ℝ≥0) :=
      ⟨fun x => x.val^(t.val-s.val) * f x,
        ((NNReal.continuous_rpow_const hr).comp continuous_subtype_val).mul f.continuous⟩
    have hi (ξ : Measure Eigenvalue) :
        ∫⁻ x, (f x : ℝ≥0∞) ∂ξ.withDensity (power (t.val-s.val)) = ∫⁻ x, g x ∂ξ := by
      rw [lintegral_withDensity_eq_lintegral_mul ξ (power_measurable _ hr)
        (g := fun x => (f x : ℝ≥0∞))
        (ENNReal.continuous_coe.comp f.continuous).measurable]
      simp [g, power]
    rw [hi]
    apply tendsto_nhds_unique ((FiniteMeasure.continuous_lintegral_continuousMap f
      ).continuousAt.tendsto.comp (hl t))
    convert! ((FiniteMeasure.continuous_lintegral_continuousMap g).continuousAt.tendsto.comp (hl s))
      using 1
    ext n
    exact (congrArg (fun ξ : Measure Eigenvalue => ∫⁻ x, (f x : ℝ≥0∞) ∂ξ) (hrec n)).trans
      (hi (m n s))

private def energy (x : Eigenvalue) : ℝ≥0 := (-Real.log (x.val:ℝ)).toNNReal

private def undo (x : Eigenvalue) : ℝ≥0∞ := ((x.val⁻¹ : ℝ≥0) : ℝ≥0∞)

/-- Limits of positive-time packet moments have one positive energy
measure for every time, even if the untilted masses diverge. -/
theorem exists_laplace_measure_of_transfer_limit
    (μ : ℕ → Measure Eigenvalue) (H : Time → ℝ≥0)
    (hfin : ∀ n (t : Time), (∫⁻ x, ((x.val ^ t.val : ℝ≥0) : ℝ≥0∞) ∂(μ n)) ≠ ⊤)
    (hlim : ∀ t : Time, Tendsto (fun n => ∫⁻ x, ((x.val ^ t.val : ℝ≥0) : ℝ≥0∞) ∂(μ n))
      atTop (𝓝 (H t : ℝ≥0∞))) :
    ∃ ρ : Measure ℝ≥0, ∀ t : Time,
      ∫⁻ E, ENNReal.ofReal (Real.exp (-t.val * (E:ℝ))) ∂ρ = (H t : ℝ≥0∞) := by
  obtain ⟨η, hm, he⟩ := tilted_lintegral_limit μ H hfin hlim
  let one : Time := ⟨1, (zero_lt_one : (0:ℝ) < 1)⟩
  let τ := (η one : Measure Eigenvalue).withDensity undo
  have hemeas : Measurable energy := by unfold energy; fun_prop
  have hundo : Measurable undo := by unfold undo; fun_prop
  refine ⟨τ.map energy, ?_⟩
  intro t
  let s : Time := ⟨min 1 t.val / 2, (show (0:ℝ) < min 1 t.val / 2 from
    half_pos (lt_min zero_lt_one t.2))⟩
  have hs1 : s.val < one.val := by
    dsimp [s,one]; linarith [min_le_left (1:ℝ) t.val]
  have hst : s.val < t.val := by
    dsimp [s]; linarith [min_le_right (1:ℝ) t.val, (show 0 < t.val from t.2)]
  have hfun : Measurable (fun E : ℝ≥0 => ENNReal.ofReal (Real.exp (-t.val * (E:ℝ)))) := by fun_prop
  rw [lintegral_map hfun hemeas]
  unfold τ
  rw [lintegral_withDensity_eq_lintegral_mul _ hundo
    (g := fun x => ENNReal.ofReal (Real.exp (-t.val * (energy x : ℝ)))) (hfun.comp hemeas)]
  rw [he s one hs1, lintegral_withDensity_eq_lintegral_mul (η s : Measure Eigenvalue)
    (power_measurable _ (sub_pos.mpr hs1).le)
    (g := undo * fun x => ENNReal.ofReal (Real.exp (-t.val * (energy x : ℝ))))
    (hundo.mul (hfun.comp hemeas))]
  rw [← hm t, FiniteMeasure.ennreal_mass, he s t hst, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  apply lintegral_congr
  intro x
  change power (1-s.val) x * (undo x * ENNReal.ofReal (Real.exp (-t.val * (energy x : ℝ)))) =
    power (t.val-s.val) x
  by_cases hx : x.val = 0
  · simp [power, undo, hx, NNReal.zero_rpow (sub_pos.mpr hst).ne']
  have hxpos : 0 < (x.val:ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hx
  have hlog : Real.log (x.val:ℝ) ≤ 0 :=
    Real.log_nonpos hxpos.le (by exact_mod_cast x.2.2)
  have hpow : Real.exp (-t.val * (energy x:ℝ)) = ((x.val ^ t.val : ℝ≥0):ℝ) := by
    rw [energy, Real.coe_toNNReal _ (neg_nonneg.mpr hlog), NNReal.coe_rpow, Real.rpow_def_of_pos hxpos]
    congr 1
    ring
  rw [hpow, ENNReal.ofReal_coe_nnreal]
  unfold undo power
  norm_cast
  rw [← NNReal.rpow_neg_one, ← NNReal.rpow_add hx, ← NNReal.rpow_add hx]
  congr 1
  ring

/-- Real-integral formulation for finite lattice packet spectra. Each finite
measure may have a different, arbitrarily large, zero-time mass. -/
theorem exists_laplace_measure_of_moment_limits
    (μ : ℕ → FiniteMeasure Eigenvalue) (H : Time → ℝ)
    (hl : ∀ t : Time, Tendsto
      (fun n => ∫ x : Eigenvalue, ((x.val ^ t.val : ℝ≥0):ℝ) ∂(μ n : Measure Eigenvalue))
      atTop (𝓝 (H t))) :
    ∃ ρ : Measure ℝ≥0, ∀ t : Time,
      Integrable (fun E : ℝ≥0 => Real.exp (-t.val * E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t.val * E) ∂ρ) = H t := by
  have hc (t : Time) : Continuous (fun x : Eigenvalue => ((x.val ^ t.val : ℝ≥0):ℝ)) :=
    NNReal.continuous_coe.comp ((NNReal.continuous_rpow_const (show 0 ≤ t.val from t.2.le)).comp
      continuous_subtype_val)
  have he (n : ℕ) (t : Time) :
      ENNReal.ofReal (∫ x : Eigenvalue, ((x.val ^ t.val : ℝ≥0):ℝ) ∂(μ n : Measure Eigenvalue)) =
      ∫⁻ x : Eigenvalue, ((x.val ^ t.val : ℝ≥0):ℝ≥0∞) ∂(μ n : Measure Eigenvalue) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      ((hc t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (ae_of_all _ fun x => (x.val ^ t.val : ℝ≥0).2)]
    simp only [ENNReal.ofReal_coe_nnreal]
  have hnon (t : Time) : 0 ≤ H t := ge_of_tendsto' (hl t) (fun _ =>
    integral_nonneg fun (x : Eigenvalue) => (x.val ^ t.val : ℝ≥0).2)
  let V (t : Time) : ℝ≥0 := ⟨H t, hnon t⟩
  obtain ⟨ρ,hρ⟩ := exists_laplace_measure_of_transfer_limit (fun n => (μ n : Measure Eigenvalue)) V
    (fun n t => by rw [← he n t]; exact ENNReal.ofReal_ne_top)
    (fun t => by
      simp_rw [← he]
      rw [ENNReal.coe_nnreal_eq (V t)]
      exact (ENNReal.continuous_ofReal.tendsto (H t)).comp (hl t))
  refine ⟨ρ, fun t => ?_⟩
  have hn : ∀ᵐ E : ℝ≥0 ∂ρ, 0 ≤ Real.exp (-t.val * E) := ae_of_all _ fun _ => (Real.exp_pos _).le
  have hint : Integrable (fun E : ℝ≥0 => Real.exp (-t.val * E)) ρ :=
    ⟨(by fun_prop : Continuous _).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr ((hρ t).trans_lt ENNReal.coe_lt_top)⟩
  refine ⟨hint, ?_⟩
  have heq := (ofReal_integral_eq_lintegral_ofReal hint hn).trans (hρ t)
  calc
    _ = (ENNReal.ofReal (∫ E : ℝ≥0, Real.exp (-t.val*E) ∂ρ)).toReal :=
      (ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)).symm
    _ = (V t : ℝ≥0∞).toReal := congrArg ENNReal.toReal heq
    _ = H t := by rw [ENNReal.coe_toReal]; rfl

/-- Rounded integer times of a transfer matrix give the same positive-time
limit as the exponential interpolation. Continuity is needed only on t>0. -/
theorem exists_laplace_measure_of_rounded_moment_limits
    (μ : ℕ → FiniteMeasure Eigenvalue) (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (H : ℝ → ℝ) (hc : ContinuousOn H (Ioi 0))
    (hl : ∀ t : ℝ, 0 < t → Tendsto
      (fun n => ∫ x : Eigenvalue, ((x.val ^ ((⌊t*R n⌋₊ : ℝ) / R n) : ℝ≥0):ℝ)
        ∂(μ n : Measure Eigenvalue)) atTop (𝓝 (H t))) :
    ∃ ρ : Measure ℝ≥0, ∀ t : Time,
      Integrable (fun E : ℝ≥0 => Real.exp (-t.val * E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t.val * E) ∂ρ) = H t := by
  let grid (n : ℕ) (s : ℝ) := (⌊s * R n⌋₊ : ℝ) / R n
  let F (n : ℕ) (s : ℝ) := ∫ x : Eigenvalue, ((x.val^s:ℝ≥0):ℝ) ∂(μ n : Measure Eigenvalue)
  have hmono (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) : F n t ≤ F n s := by
    have hi (r : ℝ) (hr : 0 ≤ r) : Integrable (fun x : Eigenvalue => ((x.val^r:ℝ≥0):ℝ))
        (μ n : Measure Eigenvalue) :=
      (NNReal.continuous_coe.comp ((NNReal.continuous_rpow_const hr).comp continuous_subtype_val)
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply integral_mono (hi t (hs.trans hst)) (hi s hs)
    intro x
    apply NNReal.coe_le_coe.mpr
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_rpow_of_nonneg _ hs, ENNReal.coe_rpow_of_nonneg _ (hs.trans hst)]
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast x.2.2) hst
  have hg (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => grid n s) atTop (𝓝 s) :=
    (tendsto_nat_floor_mul_div_atTop hs).comp (tendsto_natCast_atTop_atTop.comp hR)
  have hb (n : ℕ) (s : ℝ) (hs : 0 ≤ s) : grid n s ≤ s := by
    by_cases hr : R n = 0
    · simpa [grid,hr] using hs
    exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hr : (0:ℝ)<R n)).mpr
      (Nat.floor_le (mul_nonneg hs (Nat.cast_nonneg _)))
  apply exists_laplace_measure_of_moment_limits μ (fun t => H t)
  intro t
  apply tendsto_order.mpr
  constructor
  · intro l hlt
    have hnear : ∀ᶠ s in 𝓝 t.val, l < H s :=
      (hc.continuousAt (isOpen_Ioi.mem_nhds t.2)).tendsto.eventually_const_lt hlt
    have hright : ∀ᶠ s in 𝓝[>] t.val, t.val < s ∧ l < H s :=
      (show ∀ᶠ s in 𝓝[>] t.val, t.val < s from self_mem_nhdsWithin).and
        (hnear.filter_mono nhdsWithin_le_nhds)
    obtain ⟨s,hts,hls⟩ := hright.exists
    filter_upwards [(hl s ((show 0<t.val from t.2).trans hts)).eventually_const_lt hls,
      (hg s ((show 0<t.val from t.2).trans hts).le).eventually_const_lt hts] with n h1 h2
    exact h1.trans_le (hmono n t (grid n s) t.2.le h2.le)
  · intro b hlt
    filter_upwards [(hl t t.2).eventually_lt_const hlt] with n hn
    exact (hmono n (grid n t) t (by dsimp [grid]; positivity) (hb n t t.2.le)).trans_lt hn

/-- The positive-time cone is closed under pointwise limits even for
non-finite energy measures. This permits a second limit, from finite
transverse point packets to smooth packets. -/
theorem exists_laplace_measure_of_laplace_limits (σ : ℕ → Measure ℝ≥0)
    (H : Time → ℝ)
    (hint : ∀ (n : ℕ) (t : Time), Integrable (fun E : ℝ≥0 => Real.exp (-t.val * E)) (σ n))
    (hl : ∀ t : Time, Tendsto (fun n => ∫ E : ℝ≥0, Real.exp (-t.val * E) ∂σ n)
      atTop (𝓝 (H t))) :
    ∃ ρ : Measure ℝ≥0, ∀ t : Time,
      Integrable (fun E : ℝ≥0 => Real.exp (-t.val * E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t.val * E) ∂ρ) = H t := by
  let u (E : ℝ≥0) : Eigenvalue :=
    ⟨⟨Real.exp (-(E:ℝ)),(Real.exp_pos _).le⟩, bot_le, by
      change Real.exp (-(E:ℝ)) ≤ 1
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr E.2)⟩
  have hu : Measurable u := by
    apply Measurable.subtype_mk
    apply Measurable.subtype_mk
    fun_prop
  have he (n : ℕ) (t : Time) :
      (∫⁻ x : Eigenvalue, ((x.val^t.val:ℝ≥0):ℝ≥0∞) ∂(σ n).map u) =
      ENNReal.ofReal (∫ E : ℝ≥0, Real.exp (-t.val*E) ∂σ n) := by
    rw [lintegral_map (show Measurable (fun x : Eigenvalue => ((x.val^t.val:ℝ≥0):ℝ≥0∞))
      from power_measurable _ t.2.le) hu, ofReal_integral_eq_lintegral_ofReal (hint n t)
      (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    apply lintegral_congr
    intro E
    rw [ENNReal.coe_nnreal_eq, NNReal.coe_rpow]
    change ENNReal.ofReal (Real.exp (-(E:ℝ)) ^ t.val) = _
    rw [← Real.exp_mul, neg_mul, neg_mul, mul_comm]
  have hnon (t : Time) : 0 ≤ H t := ge_of_tendsto' (hl t) (fun _ =>
    integral_nonneg fun _ => (Real.exp_pos _).le)
  let V (t : Time) : ℝ≥0 := ⟨H t, hnon t⟩
  obtain ⟨ρ,hρ⟩ := exists_laplace_measure_of_transfer_limit (fun n => (σ n).map u) V
    (fun n t => by rw [he]; exact ENNReal.ofReal_ne_top)
    (fun t => by
      simp_rw [he, ENNReal.coe_nnreal_eq (V t)]
      exact (ENNReal.continuous_ofReal.tendsto (H t)).comp (hl t))
  refine ⟨ρ, fun t => ?_⟩
  have hn : ∀ᵐ E : ℝ≥0 ∂ρ, 0 ≤ Real.exp (-t.val * E) := ae_of_all _ fun _ => (Real.exp_pos _).le
  have hi : Integrable (fun E : ℝ≥0 => Real.exp (-t.val * E)) ρ :=
    ⟨(by fun_prop : Continuous _).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr ((hρ t).trans_lt ENNReal.coe_lt_top)⟩
  refine ⟨hi, ?_⟩
  calc
    _ = (ENNReal.ofReal (∫ E : ℝ≥0, Real.exp (-t.val*E) ∂ρ)).toReal :=
      (ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)).symm
    _ = (V t : ℝ≥0∞).toReal := congrArg ENNReal.toReal
      ((ofReal_integral_eq_lintegral_ofReal hi hn).trans (hρ t))
    _ = H t := by rw [ENNReal.coe_toReal]; rfl

end IsingRotation.Laplace
