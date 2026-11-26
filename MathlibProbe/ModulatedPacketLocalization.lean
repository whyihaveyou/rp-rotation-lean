import MathlibProbe.TransversePacketLocalization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Physical compactly supported transverse packets, in cycles per unit length.
The minus sign in the Fourier readout is the one in the inverse-transform test. -/
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Real NNReal ENNReal Topology ContDiff
namespace IsingRotation

def modulatedPacket (φ : ℝ → ℂ) (d k x : ℝ) : ℂ :=
  ((Real.sqrt d : ℂ)⁻¹ * Complex.exp (((-2*π*x*k:ℝ):ℂ)*Complex.I)) * φ (x/d)

theorem modulatedPacket_regular (φ : ℝ → ℂ) (hs : ContDiff ℝ ∞ φ)
    (hk : HasCompactSupport φ) {d : ℝ} (hd : 0 < d) (k : ℝ) :
    ContDiff ℝ ∞ (modulatedPacket φ d k) ∧ HasCompactSupport (modulatedPacket φ d k) := by
  constructor
  · unfold modulatedPacket
    have he : ContDiff ℝ ∞ (fun x : ℝ => ((-2*π*x*k:ℝ):ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => -2*π*x*k))
    exact (contDiff_const.mul ((he.mul contDiff_const).cexp)).mul
      (hs.comp (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => x/d)))
  · have hc : HasCompactSupport (fun x : ℝ => φ (x/d)) := by
      simpa only [div_eq_mul_inv, Homeomorph.coe_mulRight₀, Function.comp_def] using
        (hk.comp_homeomorph (Homeomorph.mulRight₀ d⁻¹ (inv_ne_zero hd.ne')))
    exact hc.mul_left

theorem fourier_modulatedPacket_neg (φ : ℝ → ℂ) {d : ℝ} (hd : 0 < d) (k u : ℝ) :
    𝓕 (modulatedPacket φ d k) (-u) = (Real.sqrt d : ℂ) * 𝓕 φ (-(d*(u-k))) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let f (x : ℝ) := Complex.exp (((-2*π*x*(-(d*(u-k))):ℝ):ℂ)*Complex.I) * φ x
  have hi : (∫ x : ℝ, Complex.exp (((-2*π*x*(-u):ℝ):ℂ)*Complex.I) * modulatedPacket φ d k x) =
      (Real.sqrt d : ℂ)⁻¹ * ∫ x : ℝ, f (x/d) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    unfold modulatedPacket f
    dsimp only
    have he : (((-2*π*x*(-u):ℝ):ℂ)*Complex.I) + (((-2*π*x*k:ℝ):ℂ)*Complex.I) =
        (((-2*π*(x/d)*(-(d*(u-k))):ℝ):ℂ)*Complex.I) := by
      push_cast
      field_simp [show (d:ℂ) ≠ 0 by exact_mod_cast hd.ne']
      ring
    rw [← he,Complex.exp_add]
    ring
  rw [hi, Measure.integral_comp_div, abs_of_pos hd, Complex.real_smul,← mul_assoc]
  have hs : (Real.sqrt d : ℂ)^2 = (d:ℂ) := by exact_mod_cast Real.sq_sqrt hd.le
  have hn : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  have hcancel : (Real.sqrt d : ℂ)⁻¹ * d = (Real.sqrt d:ℂ) := by
    rw [← hs, sq, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [hcancel]

theorem fourier_modulatedPacket_power (φ : ℝ → ℂ) {d : ℝ} (hd : 0 < d) (k u : ℝ) :
    ‖𝓕 (modulatedPacket φ d k) (-u)‖^2 = d*‖𝓕 φ (-(d*(u-k)))‖^2 := by
  rw [fourier_modulatedPacket_neg φ hd k u, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd.le]

def packetPowerLaw (φ : 𝓢(ℝ,ℂ)) : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ((‖𝓕 φ (-x)‖₊^2 : ℝ≥0) : ℝ≥0∞))

theorem integral_packetPowerLaw (φ : 𝓢(ℝ,ℂ)) (F : ℝ → ℝ) :
    (∫ x : ℝ, F x ∂packetPowerLaw φ) = ∫ x : ℝ, ‖𝓕 φ (-x)‖^2*F x := by
  rw [packetPowerLaw, integral_withDensity_eq_integral_smul (by fun_prop)]
  rfl

theorem packetPowerLaw_probability (φ : 𝓢(ℝ,ℂ)) (h : (∫ x : ℝ, ‖φ x‖^2) = 1) :
    IsProbabilityMeasure (packetPowerLaw φ) := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have hz := integral_packetPowerLaw φ (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one] at hz
  change ((packetPowerLaw φ) univ).toReal = 1
  change ((packetPowerLaw φ) univ).toReal = _ at hz
  rw [hz,integral_neg_eq_self (fun x : ℝ => ‖𝓕 φ x‖^2), SchwartzMap.integral_norm_sq_fourier, h]

def packetPlaneLaw (φ : 𝓢(ℝ,ℂ)) : Measure (ℝ × ℝ) :=
  (packetPowerLaw φ).prod (packetPowerLaw φ)

theorem packetPlaneLaw_probability (φ : 𝓢(ℝ,ℂ)) (h : (∫ x : ℝ, ‖φ x‖^2) = 1) :
    IsProbabilityMeasure (packetPlaneLaw φ) := by
  have := packetPowerLaw_probability φ h
  unfold packetPlaneLaw
  infer_instance

/-- Any nonzero physical test bump can be normalized before logarithmic
angular or normal-frequency tests are chosen. -/
theorem exists_unit_packet (φ : ℝ → ℂ) (hs : ContDiff ℝ ∞ φ)
    (hk : HasCompactSupport φ) {x : ℝ} (hx : φ x ≠ 0) :
    ∃ (a : ℝ) (ψ : 𝓢(ℝ,ℂ)), 0 < a ∧ HasCompactSupport (ψ : ℝ → ℂ) ∧
      (∀ t, ψ t = (a:ℂ)*φ t) ∧ (∫ t : ℝ, ‖ψ t‖^2) = 1 := by
  let m : ℝ := ∫ t : ℝ, ‖φ t‖^2
  have hkc : HasCompactSupport (fun t : ℝ => ‖φ t‖^2) :=
    hk.comp_left (g := fun w : ℂ => ‖w‖^2) (by simp)
  have hm : 0 < m := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := volume) (f := fun t : ℝ => ‖φ t‖^2) (x := x) (hs.continuous.norm.pow 2)
    hkc (fun t => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  let a : ℝ := (Real.sqrt m)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  let f (t : ℝ) : ℂ := (a:ℂ)*φ t
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul hs
  have hfk : HasCompactSupport f := hk.mul_left
  refine ⟨a, hfk.toSchwartzMap hf, ha, hfk, fun _ => rfl, ?_⟩
  change (∫ t : ℝ, ‖(a:ℂ)*φ t‖^2) = 1
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [integral_const_mul]
  change ((Real.sqrt m)⁻¹)^2 * m = 1
  rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']

theorem exists_unit_compact_packet :
    ∃ ψ : 𝓢(ℝ,ℂ), HasCompactSupport (ψ : ℝ → ℂ) ∧ (∫ t : ℝ, ‖ψ t‖^2) = 1 := by
  let b : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
  let f (t : ℝ) : ℂ := (b t : ℝ)
  have hs : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hk : HasCompactSupport f := b.hasCompactSupport.comp_left (show ((0:ℝ):ℂ)=0 from rfl)
  have h0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hf : f 0 ≠ 0 := by simp [f,h0]
  obtain ⟨_, ψ, _, hψ, _, hmass⟩ := exists_unit_packet f hs hk hf
  exact ⟨ψ,hψ,hmass⟩

theorem integral_packetPlaneLaw (φ : 𝓢(ℝ,ℂ)) (F : ℝ × ℝ → ℝ) :
    (∫ x, F x ∂packetPlaneLaw φ) =
    ∫ x : ℝ × ℝ, F x * ‖𝓕 φ (-x.1)‖^2 * ‖𝓕 φ (-x.2)‖^2 := by
  let w (x : ℝ) : ℝ≥0 := ‖𝓕 φ (-x)‖₊^2
  have hw : Measurable w := by unfold w; fun_prop
  unfold packetPlaneLaw packetPowerLaw
  rw [prod_withDensity hw.coe_nnreal_ennreal hw.coe_nnreal_ennreal]
  change (∫ x, F x ∂(volume : Measure (ℝ × ℝ)).withDensity
    (fun x => ((w x.1 * w x.2 : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by change (_ * _) * _ = _; dsimp [w]; ring

theorem integral_localized_packets (φ : 𝓢(ℝ,ℂ)) (F : ℝ × ℝ → ℝ)
    {d : ℝ} (hd : 0 < d) (k : ℝ × ℝ) :
    (∫ x : ℝ × ℝ, F x * ‖𝓕 (modulatedPacket φ d k.1) (-x.1)‖^2 *
      ‖𝓕 (modulatedPacket φ d k.2) (-x.2)‖^2) =
    ∫ v, F (k + d⁻¹ • v) ∂packetPlaneLaw φ := by
  let G (v : ℝ × ℝ) := F (k + d⁻¹ • v) * ‖𝓕 φ (-v.1)‖^2 * ‖𝓕 φ (-v.2)‖^2
  rw [integral_packetPlaneLaw]
  change _ = ∫ v : ℝ × ℝ, G v
  simp_rw [fourier_modulatedPacket_power _ hd]
  calc _ = ∫ x : ℝ × ℝ, d^2 * G (d • (x - k)) := by
          apply integral_congr_ae
          apply ae_of_all
          intro x
          unfold G
          dsimp only
          rw [inv_smul_smul₀ hd.ne', show k + (x-k)=x by abel]
          change _ = d^2 * (F x * ‖𝓕 φ (-(d*(x.1-k.1)))‖^2 * ‖𝓕 φ (-(d*(x.2-k.2)))‖^2)
          simp only [SchwartzMap.fourier_coe]
          ring
       _ = _ := by
          rw [integral_const_mul,
            integral_sub_right_eq_self (μ := volume) (fun x : ℝ × ℝ => G (d • x)) k,
            Measure.integral_comp_smul]
          simp [Module.finrank_prod, abs_of_pos hd, smul_eq_mul, hd.ne']

theorem packetAverage_modulated (φ : 𝓢(ℝ,ℂ)) (C : Space3 → ℝ)
    (α v t z : ℝ) (n : ℕ) :
    (∫ x : ℝ × ℝ, C (planeFrequency α v x.1 x.2) *
      ‖𝓕 (modulatedPacket φ (n+1) t) (-x.1)‖^2 *
      ‖𝓕 (modulatedPacket φ (n+1) z) (-x.2)‖^2) =
    packetAverage (packetPlaneLaw φ) C α v t z n := by
  simpa only [packetAverage, one_div, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] using
    integral_localized_packets φ (fun x => C (planeFrequency α v x.1 x.2))
      (d := (n:ℝ)+1) (by positivity) (t,z)

/-- The actual Fourier intensities of one fixed modulated bump per
transverse direction recover the given point of the spectral density. -/
theorem tendsto_modulated_packets (φ : 𝓢(ℝ,ℂ)) (hunit : (∫ x : ℝ, ‖φ x‖^2)=1)
    (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ) (hB : BoundedAwayFromOrigin C)
    (α v t z : ℝ) (hv : 0 < v) :
    Tendsto (fun n : ℕ => ∫ x : ℝ × ℝ, C (planeFrequency α v x.1 x.2) *
      ‖𝓕 (modulatedPacket φ (n+1) t) (-x.1)‖^2 *
      ‖𝓕 (modulatedPacket φ (n+1) z) (-x.2)‖^2)
      atTop (𝓝 (C (planeFrequency α v t z))) := by
  have := packetPlaneLaw_probability φ hunit
  simpa only [packetAverage_modulated] using packetAverage_tendsto (packetPlaneLaw φ)
    C hc hB α v t z hv

end IsingRotation
