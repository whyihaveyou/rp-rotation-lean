import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import MathlibProbe.StieltjesStrip
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Normal-time Fourier transform of positive-energy packets in AS-8.
The angular frequency convention is exp(-i ωt), with no 2π in the exponent. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Real
namespace IsingRotation.PacketFourier

def mode (d ω t : ℝ) : ℂ :=
  Complex.exp (-(d:ℂ)*(|t|:ℝ) - (ω:ℂ)*Complex.I*t)

private def leftRate (d ω : ℝ) : ℂ := d - (ω:ℂ)*Complex.I
private def rightRate (d ω : ℝ) : ℂ := -d - (ω:ℂ)*Complex.I

private theorem mode_left (d ω : ℝ) : EqOn (mode d ω)
    (fun t : ℝ => Complex.exp (leftRate d ω*t)) (Iic 0) := by
  intro t ht
  simp only [mode, abs_of_nonpos (show t ≤ 0 from ht), Complex.ofReal_neg, leftRate]
  congr 1
  ring

private theorem mode_right (d ω : ℝ) : EqOn (mode d ω)
    (fun t : ℝ => Complex.exp (rightRate d ω*t)) (Ioi 0) := by
  intro t ht
  simp only [mode, abs_of_pos (show 0 < t from ht), rightRate]
  congr 1
  ring

theorem integrable_mode {d : ℝ} (hd : 0 < d) (ω : ℝ) : Integrable (mode d ω) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
  exact ⟨(integrableOn_exp_mul_complex_Iic (a := leftRate d ω)
    (by simpa [leftRate, Complex.mul_re] using hd) 0).congr_fun (mode_left d ω).symm measurableSet_Iic,
    (integrableOn_exp_mul_complex_Ioi (a := rightRate d ω)
    (by simpa [rightRate, Complex.mul_re] using hd) 0).congr_fun (mode_right d ω).symm measurableSet_Ioi⟩

theorem integral_mode {d : ℝ} (hd : 0 < d) (ω : ℝ) :
    (∫ t : ℝ, mode d ω t) = ((2*d/(ω^2+d^2) : ℝ):ℂ) := by
  have hl : 0 < (leftRate d ω).re := by simpa [leftRate, Complex.mul_re] using hd
  have hr : (rightRate d ω).re < 0 := by simpa [rightRate, Complex.mul_re] using hd
  have h₁ : leftRate d ω ≠ 0 := fun h => by simp [h] at hl
  have h₂ : rightRate d ω ≠ 0 := fun h => by simp [h] at hr
  have h₃ : (ω:ℂ)^2+(d:ℂ)^2 ≠ 0 := by exact_mod_cast (show ω^2+d^2 ≠ 0 by positivity)
  rw [← integral_add_compl measurableSet_Iic (integrable_mode hd ω), compl_Iic,
    setIntegral_congr_fun measurableSet_Iic (mode_left d ω),
    setIntegral_congr_fun measurableSet_Ioi (mode_right d ω),
    integral_exp_mul_complex_Iic hl, integral_exp_mul_complex_Ioi hr]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat]
  field_simp [h₁, h₂, h₃]
  unfold leftRate rightRate
  ring_nf
  simp [Complex.I_sq]

theorem norm_mode (d ω t : ℝ) : ‖mode d ω t‖ = Real.exp (-d*|t|) := by
  simp [mode,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

theorem integral_norm_mode {d : ℝ} (hd : 0 < d) (ω : ℝ) :
    (∫ t : ℝ, ‖mode d ω t‖) = 2/d := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (integral_mode hd 0)
  rw [← integral_re (integrable_mode hd 0)] at h
  simp only [RCLike.re_to_complex, mode, Complex.ofReal_zero, zero_mul, sub_zero,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  simp only [norm_mode]
  rw [h]
  field_simp

/-- A finite (1+E)⁻¹ moment suffices even for infinite total spectral mass. -/
def weight (E : ℝ≥0) : ℝ := (1+(E:ℝ))⁻¹

theorem sigmaFinite_of_weight {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ) : SigmaFinite ρ := by
  let A (n : ℕ) := {E : ℝ≥0 | (1+(n:ℝ))⁻¹ ≤ weight E}
  refine ⟨⟨⟨A, fun _ => trivial, fun n => hρ.measure_ge_lt_top (show 0 < (1+(n:ℝ))⁻¹ by positivity), ?_⟩⟩⟩
  apply eq_univ_of_forall
  intro E
  obtain ⟨n,hn⟩ := exists_nat_ge (E:ℝ)
  refine mem_iUnion.mpr ⟨n, ?_⟩
  change (1+(n:ℝ))⁻¹ ≤ (1+(E:ℝ))⁻¹
  exact inv_anti₀ (by positivity) (by linarith)

/-- The even extension of the positive-time Laplace packet. At zero the
Bochner integral may take its default value when the total mass is infinite.
All subsequent time integrals are with respect to Lebesgue measure. -/
def packet (ρ : Measure ℝ≥0) (t : ℝ) : ℂ :=
  ∫ E : ℝ≥0, ((Real.exp (-(E:ℝ)*|t|) : ℝ):ℂ) ∂ρ

theorem integrable_packet_at {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun E : ℝ≥0 => ((Real.exp (-(E:ℝ)*|t|) : ℝ):ℂ)) ρ := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  apply (hρ.const_mul (1+1/|t|)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
  apply ae_of_all
  intro E
  have he := E.coe_nonneg
  have h₁ : 1 ≤ Real.exp ((E:ℝ)*|t|) := Real.one_le_exp (by positivity)
  have h₂ : (E:ℝ) ≤ Real.exp ((E:ℝ)*|t|) / |t| := by
    rw [le_div_iff₀ ht']
    linarith [Real.add_one_le_exp ((E:ℝ)*|t|)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_mul,
    Real.exp_neg, weight, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  rw [one_mul, add_mul, one_mul, one_div, ← div_eq_inv_mul]
  exact add_le_add h₁ h₂

private theorem mode_add_energy (E : ℝ≥0) (ε ω t : ℝ) :
    mode ε ω t * (Real.exp (-(E:ℝ)*|t|) : ℂ) = mode ((E:ℝ)+ε) ω t := by
  unfold mode
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_integral_bound (E : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    2/((E:ℝ)+ε) ≤ (2 / min 1 ε) * weight E := by
  have hmin : 0 < min 1 ε := lt_min (by norm_num) hε
  have he := E.coe_nonneg
  have hm := min_le_left (1:ℝ) ε
  have ha := min_le_right (1:ℝ) ε
  rw [weight, ← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hm he]

private theorem integrable_abel_product {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    {ε : ℝ} (hε : 0 < ε) (ω : ℝ) :
    Integrable (Function.uncurry (fun (E:ℝ≥0) (t:ℝ) => mode ((E:ℝ)+ε) ω t)) (ρ.prod volume) := by
  have hcont : Continuous (Function.uncurry (fun (E:ℝ≥0) (t:ℝ) => mode ((E:ℝ)+ε) ω t)) := by
    dsimp [Function.uncurry, mode]
    fun_prop
  apply (integrable_prod_iff hcont.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun E => integrable_mode (add_pos_of_nonneg_of_pos E.coe_nonneg hε) ω), ?_⟩
  change Integrable (fun E : ℝ≥0 => ∫ t : ℝ, ‖mode ((E:ℝ)+ε) ω t‖) ρ
  simp_rw [integral_norm_mode (add_pos_of_nonneg_of_pos (NNReal.coe_nonneg _) hε)]
  refine (hρ.const_mul (2/min 1 ε)).mono' ?_ (ae_of_all _ fun E => ?_)
  · apply Continuous.aestronglyMeasurable
    exact continuous_const.div (NNReal.continuous_coe.add continuous_const)
      (fun E => (add_pos_of_nonneg_of_pos E.coe_nonneg hε).ne')
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2/((E:ℝ)+ε))]
    exact norm_integral_bound E hε

private theorem packet_mul_mode (ρ : Measure ℝ≥0) (ε ω t : ℝ) :
    mode ε ω t * packet ρ t = ∫ E : ℝ≥0, mode ((E:ℝ)+ε) ω t ∂ρ := by
  change mode ε ω t * (∫ E : ℝ≥0, (Real.exp (-(E:ℝ)*|t|):ℂ) ∂ρ) = _
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (fun E => mode_add_energy E ε ω t))

theorem integrable_abel_packet {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    {ε : ℝ} (hε : 0 < ε) (ω : ℝ) : Integrable (fun t : ℝ => mode ε ω t * packet ρ t) := by
  let _ := sigmaFinite_of_weight hρ
  simp_rw [packet_mul_mode]
  exact (integrable_abel_product hρ hε ω).integral_prod_right

/-- Exact damped normal-frequency identity by absolute Fubini. The input
only has a weighted energy moment. In particular the undamped time
correlation need not be absolutely integrable. -/
theorem integral_abel_packet {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    {ε : ℝ} (hε : 0 < ε) (ω : ℝ) :
    (∫ t : ℝ, mode ε ω t * packet ρ t) =
    ∫ E : ℝ≥0, ((2*((E:ℝ)+ε)/(ω^2+((E:ℝ)+ε)^2) : ℝ):ℂ) ∂ρ := by
  let _ := sigmaFinite_of_weight hρ
  let F (E : ℝ≥0) (t : ℝ) := mode ((E:ℝ)+ε) ω t
  have hF := integrable_abel_product hρ hε ω
  calc
    _ = ∫ t : ℝ, ∫ E : ℝ≥0, F E t ∂ρ := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      exact packet_mul_mode ρ ε ω t
    _ = ∫ E : ℝ≥0, ∫ t : ℝ, F E t ∂volume ∂ρ := (integral_integral_swap hF).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun E =>
       integral_mode (add_pos_of_nonneg_of_pos E.coe_nonneg hε) ω))

theorem resolvent_bound {ω ε : ℝ} (hω : ω ≠ 0) (hε : 0 ≤ ε) (E : ℝ≥0) :
    2*((E:ℝ)+ε)/(ω^2+((E:ℝ)+ε)^2) ≤ (2+1/|ω|)*weight E := by
  let d := (E:ℝ)+ε
  have hE : (E:ℝ) ≤ d := by dsimp [d]; linarith
  have h := E.coe_nonneg
  have hd : 0 ≤ d := h.trans hE
  have hw : 0 < |ω| := abs_pos.mpr hω
  have hden : 0 < ω^2+d^2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hω) (sq_nonneg d)
  change 2*d/(ω^2+d^2) ≤ (2+1/|ω|)*(1+(E:ℝ))⁻¹
  rw [← div_eq_mul_inv, div_le_div_iff₀ hden (by positivity)]
  have hb : 2*d ≤ (1/|ω|)*(ω^2+d^2) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hw]
    nlinarith [sq_nonneg (d-|ω|), sq_abs ω]
  nlinarith [mul_le_mul_of_nonneg_left hE hd]

/-- Remove Abel damping at each nonzero frequency. A possible atom of the
energy measure at zero contributes zero here. -/
theorem tendsto_abel_packet {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, mode ε ω t * packet ρ t) (𝓝[>] 0)
      (𝓝 (∫ E : ℝ≥0, ((2*(E:ℝ)/(ω^2+(E:ℝ)^2):ℝ):ℂ) ∂ρ)) := by
  suffices h : Tendsto (fun ε : ℝ =>
      ∫ E : ℝ≥0, ((2*((E:ℝ)+ε)/(ω^2+((E:ℝ)+ε)^2):ℝ):ℂ) ∂ρ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ E : ℝ≥0, ((2*(E:ℝ)/(ω^2+(E:ℝ)^2):ℝ):ℂ) ∂ρ)) by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with ε hε
    exact (integral_abel_packet hρ hε ω).symm
  apply tendsto_integral_filter_of_dominated_convergence (fun E : ℝ≥0 => (2+1/|ω|)*weight E)
  · apply Eventually.of_forall
    intro ε
    apply Continuous.aestronglyMeasurable
    apply Complex.continuous_ofReal.comp
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro E
    positivity
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with ε hε
    apply ae_of_all
    intro E
    have hp : 0 ≤ (E:ℝ)+ε := add_nonneg E.coe_nonneg (show 0 < ε from hε).le
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact resolvent_bound hω (show 0 < ε from hε).le E
  · exact hρ.const_mul _
  · apply ae_of_all
    intro E
    have hc : Continuous (fun ε : ℝ => ((2*((E:ℝ)+ε)/(ω^2+((E:ℝ)+ε)^2):ℝ):ℂ)) := by
      apply Complex.continuous_ofReal.comp
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro ε
      positivity
    simpa using ((hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))

/-- The AS-8 compactified measure needs just the original inverse-energy
moment. A possible infinite total mass at high energy is allowed. -/
theorem energyWeight_moment {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ) :
    (∫⁻ E, (Stieltjes.energyWeight E : ℝ≥0∞) ∂ρ) < ⊤ := by
  apply hasFiniteIntegral_iff_ofNNReal.mp
  apply (hρ.2.const_mul (3:ℝ)).mono
  apply ae_of_all
  intro E
  have h := resolvent_bound (ω := 1) (ε := 0) (by norm_num) le_rfl E
  change ‖(Stieltjes.energyWeight E:ℝ)‖ ≤ ‖(3:ℝ)*weight E‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
    abs_of_nonneg (by dsimp [weight]; positivity : 0 ≤ (3:ℝ)*weight E)]
  simpa [Stieltjes.energyWeight, show (2:ℝ)+1 = 3 by norm_num] using h

/-- The Abel transforms for all nonzero normal frequencies have one
compactified Stieltjes measure. This version uses cycles per unit length
and includes the constant Fourier contribution of a spatial contact. -/
theorem exists_profile_abel_cycles {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    (contact : ℝ≥0) : ∃ ν : FiniteMeasure Stieltjes.Parameter,
    ∀ ξ : ℝ, ∀ hξ : ξ ≠ 0, Tendsto (fun ε : ℝ =>
      ((contact:ℝ):ℂ) + ∫ t : ℝ, mode ε (2*π*ξ) t * packet ρ t)
      (𝓝[>] (0:ℝ)) (𝓝 ((Stieltjes.profile ν ⟨ξ^2,sq_pos_of_ne_zero hξ⟩ : ℝ):ℂ)) := by
  obtain ⟨μ, hm⟩ := Stieltjes.profile_from_packet ρ contact (energyWeight_moment hρ)
  obtain ⟨ν, hν⟩ := Stieltjes.exists_profile_rescaled μ ((2*π)^2) (by positivity)
  refine ⟨ν,fun ξ hξ => ?_⟩
  have hω : 2*π*ξ ≠ 0 := mul_ne_zero (by positivity) hξ
  have ht := (tendsto_abel_packet hρ hω).const_add ((contact:ℝ):ℂ)
  rw [hν, hm]
  simp only [Complex.ofReal_add, integral_complex_ofReal] at ht ⊢
  convert ht using 2
  simp [mul_pow]

/-- The nonnegative time integral is well-defined before any assumption
about total or weighted mass of the energy measure. -/
def positiveLaplace (ρ : Measure ℝ≥0) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ E : ℝ≥0, ENNReal.ofReal (Real.exp (-(E:ℝ)*t)) ∂ρ

private theorem sigmaFinite_of_positive_laplace {ρ : Measure ℝ≥0} {t : ℝ}
    (h : positiveLaplace ρ t ≠ ⊤) : SigmaFinite ρ := by
  let f (E : ℝ≥0) := Real.exp (-(E:ℝ)*t)
  have hf := (lintegral_ofReal_ne_top_iff_integrable (f := f) (μ := ρ)
      (by dsimp [f]; fun_prop) (ae_of_all _ (fun E => (Real.exp_pos _).le))).mp h
  let A (n : ℕ) := {E : ℝ≥0 | (1+(n:ℝ))⁻¹ ≤ f E}
  refine ⟨⟨⟨A, fun _ => trivial, fun n => hf.measure_ge_lt_top (show 0 < (1+(n:ℝ))⁻¹ by positivity), ?_⟩⟩⟩
  apply eq_univ_of_forall
  intro E
  obtain ⟨n, hn⟩ := exists_nat_ge (f E)⁻¹
  refine mem_iUnion.mpr ⟨n, ?_⟩
  change (1+(n:ℝ))⁻¹ ≤ f E
  rw [← one_div, div_le_iff₀ (by positivity)]
  calc
    1 = f E * (f E)⁻¹ := (mul_inv_cancel₀ (Real.exp_pos _).ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

private theorem weight_le_laplace_integral (E : ℝ≥0) :
    ENNReal.ofReal (weight E) ≤ ∫⁻ t : ℝ in Ioc 0 1,
      ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-(E:ℝ)*t)) := by
  have he := E.coe_nonneg
  have hW : weight E ≤ 1 := inv_le_one_of_one_le₀ (by change 1 ≤ 1+(E:ℝ); linarith)
  calc
    _ = ∫⁻ _ : ℝ in Ioc 0 (weight E), (1:ℝ≥0∞) := by simp [Real.volume_Ioc]
    _ ≤ ∫⁻ t : ℝ in Ioc 0 (weight E),
      ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-(E:ℝ)*t)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      apply Real.one_le_exp
      have ht' : t ≤ 1/(1+(E:ℝ)) := by simpa only [one_div, weight] using ht.2
      have hta := (le_div_iff₀ (by positivity)).mp ht'
      nlinarith [ht.1]
    _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc le_rfl hW)

/-- Local integrability at time zero supplies the weighted spectral
moment in AS-8. One finite positive Laplace integral already makes
the energy measure sigma-finite, so Tonelli needs no extra hypothesis. -/
theorem integrable_weight_of_local_laplace {ρ : Measure ℝ≥0}
    (h : (∫⁻ t : ℝ in Ioc 0 1, positiveLaplace ρ t) < ⊤) : Integrable weight ρ := by
  have hex : ∃ t : ℝ, positiveLaplace ρ t ≠ ⊤ := by
    by_contra! htop
    simp_rw [htop] at h
    simp [Real.volume_Ioc] at h
  obtain ⟨t, ht⟩ := hex
  let _ := sigmaFinite_of_positive_laplace ht
  let c := ENNReal.ofReal (Real.exp 1)
  let F (E : ℝ≥0) (t : ℝ) := c * ENNReal.ofReal (Real.exp (-(E:ℝ)*t))
  have hcm : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwm : Measurable weight := by
    change Measurable (fun E : ℝ≥0 => (1+(E:ℝ))⁻¹)
    fun_prop
  apply (lintegral_ofReal_ne_top_iff_integrable (f := weight) (μ := ρ) hwm.aestronglyMeasurable
    (ae_of_all _ (fun E => show 0 ≤ (1+(E:ℝ))⁻¹ by positivity))).mp
  apply ne_of_lt
  calc
    _ ≤ ∫⁻ E : ℝ≥0, ∫⁻ t : ℝ in Ioc 0 1, F E t ∂volume ∂ρ := lintegral_mono weight_le_laplace_integral
    _ = ∫⁻ t : ℝ in Ioc 0 1, ∫⁻ E : ℝ≥0, F E t ∂ρ := by
      apply lintegral_lintegral_swap
      exact Measurable.aemeasurable (by dsimp [Function.uncurry, F,c]; fun_prop)
    _ = c * ∫⁻ t : ℝ in Ioc 0 1, positiveLaplace ρ t := by
      simp_rw [F, lintegral_const_mul' c _ hcm, positiveLaplace]
    _ < ⊤ := ENNReal.mul_lt_top hcm.lt_top h

/-- Real-integral version for use with positive-time transfer limits.
The value assigned to the correlation at time zero plays no role. -/
theorem integrable_weight_of_time_correlation {ρ : Measure ℝ≥0} (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioc 0 1))
    (he : ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = K t) :
    Integrable weight ρ := by
  apply integrable_weight_of_local_laplace
  have hcon : ∀ t ∈ Ioc (0:ℝ) 1, positiveLaplace ρ t = ENNReal.ofReal (K t) := by
    intro t ht
    obtain ⟨hfi, heq⟩ := he t ht.1
    rw [← heq, ofReal_integral_eq_lintegral_ofReal hfi
          (ae_of_all _ (fun E => (Real.exp_pos _).le))]
    unfold positiveLaplace
    apply lintegral_congr
    intro E
    rw [neg_mul, mul_comm (E:ℝ) t, ← neg_mul]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc (fun t ht => (hcon t ht).le)) ?_
  exact lt_of_le_of_lt (lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (le_abs_self (K t))))
    ((hasFiniteIntegral_iff_norm _).mp hK.2)

end IsingRotation.PacketFourier
