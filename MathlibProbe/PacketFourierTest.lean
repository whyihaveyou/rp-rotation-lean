import MathlibProbe.NormalPacketFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! The scalar distributional normal-frequency identification in AS-8.
We test first at positive Abel damping, then remove the damping on both
sides. Ordinary smooth tests supported off zero are sufficient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform Real NNReal Topology SchwartzMap ContDiff
namespace IsingRotation.PacketFourier

def damped (ρ : Measure ℝ≥0) (ε t : ℝ) : ℂ := mode ε 0 t * packet ρ t

def spectrum (ρ : Measure ℝ≥0) (ξ : ℝ) : ℂ :=
  ∫ E : ℝ≥0, ((2*(E:ℝ)/((2*π*ξ)^2+(E:ℝ)^2):ℝ):ℂ) ∂ρ

private theorem fourier_damped (ρ : Measure ℝ≥0) (ε ξ : ℝ) :
    𝓕 (damped ρ ε) ξ = ∫ t : ℝ, mode ε (2*π*ξ) t * packet ρ t := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [damped, mode, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, Real.inner_apply]
  congr 2
  push_cast
  ring

private theorem fourier_pair {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ : ℝ, 𝓕 f ξ * g ξ) = ∫ t : ℝ, f t * 𝓕 g t := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (.mul ℂ ℂ) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg

private theorem fourier_damped_bound {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    {ε r ξ : ℝ} (hε : 0 < ε) (hr : 0 < r) (hx : r ≤ |ξ|) :
    ‖𝓕 (damped ρ ε) ξ‖ ≤ (2+1/(2*π*r)) * ∫ E : ℝ≥0, weight E ∂ρ := by
  have hw : 2*π*ξ ≠ 0 := mul_ne_zero (by positivity) (abs_pos.mp (hr.trans_le hx))
  rw [fourier_damped,integral_abel_packet hρ hε]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hρ.const_mul _)
  apply ae_of_all
  intro E
  have hp : 0 ≤ (E:ℝ)+ε := add_nonneg E.coe_nonneg hε.le
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (resolvent_bound hw hε.le E).trans
  apply mul_le_mul_of_nonneg_right _ (show 0 ≤ weight E by dsimp [weight]; positivity)
  apply add_le_add_right
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2*π)]
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity))

/-- Integrable frequency tests separated from zero identify the Fourier
transform of the time packet against its energy resolvent. The last
integrability hypothesis concerns the undamped pairing with this test. -/
theorem integral_spectrum_mul_test {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ x : ℝ, ψ x ≠ 0 → r ≤ |x|)
    (htest : Integrable (fun t : ℝ => packet ρ t * 𝓕 ψ t)) :
    (∫ ξ : ℝ, spectrum ρ ξ * ψ ξ) = ∫ t : ℝ, packet ρ t * 𝓕 ψ t := by
  let D := (2+1/(2*π*r)) * ∫ E : ℝ≥0, weight E ∂ρ
  have hD : 0 ≤ D := mul_nonneg (by positivity)
    (integral_nonneg (fun E => show 0 ≤ (1+(E:ℝ))⁻¹ by positivity))
  have hl : Tendsto (fun ε : ℝ => ∫ ξ : ℝ, 𝓕 (damped ρ ε) ξ * ψ ξ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ξ : ℝ, spectrum ρ ξ * ψ ξ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ : ℝ => D*‖ψ ξ‖)
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with ε hε
      have hf : Integrable (damped ρ ε) := integrable_abel_packet hρ hε 0
      have hc : Continuous (𝓕 (damped ρ ε)) := VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
      exact hc.aestronglyMeasurable.mul hψ.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with ε hε
      apply ae_of_all
      intro ξ
      by_cases hn : ψ ξ = 0
      · simp [hn]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (fourier_damped_bound hρ hε hr (hsupp ξ hn)) (norm_nonneg _)
    · exact hψ.norm.const_mul D
    · apply ae_of_all
      intro ξ
      by_cases hn : ψ ξ = 0
      · simp [hn]
      · simp_rw [fourier_damped]
        exact (tendsto_abel_packet hρ (mul_ne_zero (by positivity)
          (abs_pos.mp (hr.trans_le (hsupp ξ hn))))).mul_const (ψ ξ)
  have ht : Tendsto (fun ε : ℝ => ∫ t : ℝ, damped ρ ε t * 𝓕 ψ t)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ t : ℝ, packet ρ t * 𝓕 ψ t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => ‖packet ρ t * 𝓕 ψ t‖)
    · apply Eventually.of_forall
      intro ε
      simp only [damped,mul_assoc]
      exact (Continuous.aestronglyMeasurable (f := mode ε 0) (by unfold mode; fun_prop)).mul
        htest.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with ε hε
      apply ae_of_all
      intro t
      simp only [damped, mul_assoc, norm_mul, norm_mode]
      apply mul_le_of_le_one_left (by positivity)
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (show 0 < ε from hε).le) (abs_nonneg t)
    · exact htest.norm
    · apply ae_of_all
      intro t
      have hc : Continuous (fun ε : ℝ => mode ε 0 t * (packet ρ t * 𝓕 ψ t)) := by
        unfold mode
        fun_prop
      simpa [damped, mode, mul_assoc] using
        ((hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))
  apply tendsto_nhds_unique hl
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with ε hε
  exact (fourier_pair (integrable_abel_packet hρ hε 0) hψ).symm

theorem continuousOn_spectrum {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ) :
    ContinuousOn (spectrum ρ) {0}ᶜ := by
  obtain ⟨μ, hm⟩ := Stieltjes.profile_from_packet ρ 0 (energyWeight_moment hρ)
  let k (ξ : ℝ) : ℂ := (((2*π*ξ)^2:ℝ):ℂ)
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hp (ξ : ℝ) (hx : ξ ∈ ({0}ᶜ:Set ℝ)) : 0 < (2*π*ξ)^2 :=
    sq_pos_of_ne_zero (mul_ne_zero (by positivity) (show ξ ≠ 0 from hx))
  have hmaps : MapsTo k {0}ᶜ Complex.slitPlane := fun x hx =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (hp x hx))
  apply (((Stieltjes.differentiableOn_extension μ).continuousOn).comp hk.continuousOn hmaps).congr
  intro ξ hx
  have h := Stieltjes.extension_posReal μ ⟨_, hp ξ hx⟩
  rw [hm] at h
  unfold spectrum
  rw [integral_complex_ofReal]
  simpa [k] using h.symm

private theorem test_integrable_mul {g : ℝ → ℝ} (hg : Continuous g) (hk : HasCompactSupport g)
    (hs : tsupport g ⊆ ({0}ᶜ : Set ℝ)) (f : ℝ → ℂ) (hc : ContinuousOn f {0}ᶜ) :
    Integrable (fun x => (g x:ℂ)*f x) := by
  apply (ContinuousOn.integrableOn_compact hk
    ((Complex.continuous_ofReal.comp hg).continuousOn.mul (hc.mono hs))).integrable_of_forall_notMem_eq_zero
  intro x hx
  have hzero : g x = 0 := by
    by_contra hh
    exact hx (subset_tsupport g hh)
  simp [hzero]

private theorem norm_packet (ρ : Measure ℝ≥0) (t : ℝ) :
    ‖packet ρ t‖ = ∫ E : ℝ≥0, Real.exp (-(E:ℝ)*|t|) ∂ρ := by
  rw [packet,integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun E => (Real.exp_pos _).le))]

theorem integrable_schwartz_time_pair {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    (s : 𝓢(ℝ,ℂ)) : Integrable (fun t : ℝ => packet ρ t * s t) := by
  let B := SchwartzMap.seminorm ℝ 0 0 s
  have hb (t : ℝ) : ‖s t‖ ≤ B := SchwartzMap.norm_le_seminorm ℝ s t
  have hB : 0 ≤ B := (norm_nonneg (s 0)).trans (hb 0)
  have hD : Integrable (damped ρ 1) := integrable_abel_packet hρ zero_lt_one 0
  have hnon (t : ℝ) : mode 1 0 t ≠ 0 := Complex.exp_ne_zero _
  have hmeas : AEStronglyMeasurable (packet ρ) volume := by
    have hp : Continuous (mode 1 0) := by unfold mode; fun_prop
    have hprod := (hp.inv₀ hnon).aestronglyMeasurable.mul hD.aestronglyMeasurable
    change AEStronglyMeasurable (fun t : ℝ => (mode 1 0 t)⁻¹ * damped ρ 1 t) volume at hprod
    simpa only [damped,← mul_assoc, inv_mul_cancel₀ (hnon _),one_mul] using hprod
  have h1 : Integrable (fun E : ℝ≥0 => Real.exp (-(E:ℝ)*|1|)) ρ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      (integrable_packet_at hρ (t := 1) one_ne_zero).norm
  have hn := (hD.norm.const_mul (Real.exp 1 * B)).add (s.integrable.norm.const_mul ‖packet ρ 1‖)
  apply hn.mono' (hmeas.mul s.continuous.aestronglyMeasurable)
  apply ae_of_all
  intro t
  change ‖packet ρ t * s t‖ ≤ Real.exp 1 * B * ‖damped ρ 1 t‖ + ‖packet ρ 1‖ * ‖s t‖
  rw [norm_mul]
  by_cases lo : |t| ≤ 1
  · have hg : 1 ≤ Real.exp 1*Real.exp (-1*|t|) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    have hl : ‖packet ρ t‖ ≤ Real.exp 1 * ‖damped ρ 1 t‖ := by
      rw [damped,norm_mul,norm_mode,← mul_assoc]
      exact le_mul_of_one_le_left (norm_nonneg _) hg
    apply (mul_le_mul hl (hb _) (norm_nonneg _) (by positivity)).trans
    nlinarith [mul_nonneg (norm_nonneg (packet ρ 1)) (norm_nonneg (s t))]
  · have ht : ‖packet ρ t‖ ≤ ‖packet ρ 1‖ := by
      simp only [norm_packet]
      refine integral_mono_of_nonneg (ae_of_all _ fun E => (Real.exp_pos _).le) h1 (ae_of_all _ ?_)
      intro E
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr E.coe_nonneg)
      simpa using le_of_not_ge lo
    apply (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans
    exact le_add_of_nonneg_left (by positivity)

/-- Distributional Fourier density of the scalar packet on the complement
of zero, in the cycles convention. Real test functions suffice for
identification of a complex density. -/
def IsPacketFourierDensity (ρ : Measure ℝ≥0) (c : ℂ) (h : ℝ → ℂ) : Prop :=
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ ({0}ᶜ : Set ℝ) →
      let ψ : ℝ → ℂ := fun x => (g x:ℂ)
      (∫ ξ : ℝ, h ξ * ψ ξ) = c*(∫ ξ : ℝ, ψ ξ) + ∫ t : ℝ, packet ρ t * 𝓕 ψ t

/-- Ordinary Fourier-distribution testing identifies the density pointwise
off zero. The absolute convergence of the time pairing is proved here. -/
theorem spectrum_eq_of_distribution {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    (c : ℂ) (h : ℝ → ℂ) (hc : ContinuousOn h {0}ᶜ)
    (hweak : IsPacketFourierDensity ρ c h)
    (ξ : ℝ) (hξ : ξ ≠ 0) : h ξ = c+spectrum ρ ξ := by
  let U : Set ℝ := {0}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  let F (x : ℝ) := c+spectrum ρ x
  have hF : ContinuousOn F U := continuousOn_const.add (continuousOn_spectrum hρ)
  have hdiff : ContinuousOn (fun x => h x-F x) U := hc.sub hF
  have he := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hdiff.locallyIntegrableOn hU.measurableSet)
  have htest (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgk : HasCompactSupport g) (hs : tsupport g ⊆ U) :
      (∫ x : ℝ, g x • (h x-F x)) = 0 := by
    let ψ : ℝ → ℂ := fun x => (g x:ℂ)
    have hψ : Integrable ψ := (Complex.continuous_ofReal.comp hg.continuous).integrable_of_hasCompactSupport
      (hgk.comp_left (show ((0:ℝ):ℂ)=0 from rfl))
    have h0 : 0 ∈ (tsupport g)ᶜ := fun hh => (hs hh) rfl
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (isClosed_tsupport g).isOpen_compl 0 h0
    have hsep (x : ℝ) (hh : ψ x ≠ 0) : r ≤ |x| := by
      by_contra! hsmall
      have hmem := hb (show x ∈ Metric.ball 0 r by simpa [Metric.mem_ball,Real.dist_eq] using hsmall)
      exact hmem (subset_tsupport g (fun h' => hh (by simp [ψ,h'])))
    have hw := hweak g hg hgk hs
    change (∫ x : ℝ, h x * ψ x) = c * (∫ x : ℝ, ψ x) + ∫ t : ℝ, packet ρ t * 𝓕 ψ t at hw
    have hgd : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
    have hgk' : HasCompactSupport ψ := hgk.comp_left (show ((0:ℝ):ℂ)=0 from rfl)
    have hi : Integrable (fun t : ℝ => packet ρ t * 𝓕 ψ t) :=
      integrable_schwartz_time_pair hρ (𝓕 (hgk'.toSchwartzMap hgd))
    have hid := integral_spectrum_mul_test hρ ψ hψ hr hsep hi
    have heq : (∫ x : ℝ, (g x:ℂ)*h x) = ∫ x : ℝ, (g x:ℂ)*F x := by
      simp_rw [F, mul_add]
      rw [integral_add (hψ.mul_const c)
        (test_integrable_mul hg.continuous hgk hs _ (continuousOn_spectrum hρ))]
      rw [integral_mul_const]
      rw [← hid] at hw
      simpa [ψ,mul_comm] using hw
    simp_rw [Complex.real_smul, mul_sub]
    rw [integral_sub (test_integrable_mul hg.continuous hgk hs _ hc)
      (test_integrable_mul hg.continuous hgk hs _ hF), heq, sub_self]
  have hAE := he htest
  have hh : h =ᵐ[volume.restrict U] F := (ae_restrict_iff' hU.measurableSet).mpr
    (hAE.mono (fun x hh hx => sub_eq_zero.mp (hh hx)))
  exact (Measure.eqOn_open_of_ae_eq hh hU hc hF) (show ξ ∈ U from hξ)

/-- As Abel damping vanishes, the contact term plus the damped normal
Fourier transform tends to the physical density at every nonzero frequency. -/
theorem tendsto_abel_of_distribution {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    (c : ℂ) (h : ℝ → ℂ) (hc : ContinuousOn h {0}ᶜ)
    (hweak : IsPacketFourierDensity ρ c h) {ξ : ℝ} (hx : ξ ≠ 0) :
    Tendsto (fun ε : ℝ => c + ∫ t : ℝ, mode ε (2*π*ξ) t * packet ρ t)
      (𝓝[>] (0:ℝ)) (𝓝 (h ξ)) := by
  rw [spectrum_eq_of_distribution hρ c h hc hweak ξ hx]
  exact (tendsto_abel_packet hρ (mul_ne_zero (by positivity : (2*π:ℝ) ≠ 0) hx)).const_add c

/-- A single measure represents every positive squared normal frequency
of the given physical Fourier density. Neither an Abel comparison nor a
pointwise Fourier identity is required as an input. -/
theorem exists_profile_of_distribution {ρ : Measure ℝ≥0} (hρ : Integrable weight ρ)
    (c : ℝ≥0) (h : ℝ → ℂ) (hc : ContinuousOn h {0}ᶜ)
    (hweak : IsPacketFourierDensity ρ ((c:ℝ):ℂ) h) :
    ∃ μ : FiniteMeasure Stieltjes.Parameter, ∀ (ξ : ℝ) (hx : ξ ≠ 0),
      h ξ = (Stieltjes.profile μ ⟨ξ^2,sq_pos_of_ne_zero hx⟩ : ℂ) := by
  obtain ⟨μ, hm⟩ := exists_profile_abel_cycles hρ c
  refine ⟨μ, fun ξ hx => ?_⟩
  rw [spectrum_eq_of_distribution hρ _ h hc hweak ξ hx]
  exact tendsto_nhds_unique ((tendsto_abel_packet hρ
    (mul_ne_zero (by positivity : (2*π:ℝ) ≠ 0) hx)).const_add ((c:ℝ):ℂ)) (hm ξ hx)

/-- Positive-time transfer data and the physical distributional Fourier
identity give a common Stieltjes measure for the entire punctured normal
frequency axis. The value assigned to the time correlation at zero is
irrelevant; the time Dirac contact is included separately. -/
theorem exists_profile_of_even_time_tests (ρ : Measure ℝ≥0) (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioc 0 1))
    (hlap : ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = K t)
    (c : ℝ≥0) (h : ℝ → ℂ) (hc : ContinuousOn h {0}ᶜ)
    (htest : ∀ s : 𝓢(ℝ,ℂ), (∫ ξ : ℝ, h ξ * s ξ) =
      ((c:ℝ):ℂ) * (∫ ξ : ℝ, s ξ) + ∫ t : ℝ, (K |t|:ℂ) * (𝓕 s) t) :
    ∃ μ : FiniteMeasure Stieltjes.Parameter, ∀ (ξ : ℝ) (hx : ξ ≠ 0),
      h ξ = (Stieltjes.profile μ ⟨ξ^2,sq_pos_of_ne_zero hx⟩ : ℂ) := by
  apply exists_profile_of_distribution (integrable_weight_of_time_correlation K hK hlap) c h hc
  intro g hg hgk _
  let ψ : ℝ → ℂ := fun x => (g x:ℂ)
  have hd : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
  have hk : HasCompactSupport ψ := hgk.comp_left (show ((0:ℝ):ℂ)=0 from rfl)
  let s := hk.toSchwartzMap hd
  change (∫ ξ : ℝ, h ξ * ψ ξ) = ((c:ℝ):ℂ) * (∫ ξ : ℝ, ψ ξ) +
    ∫ t : ℝ, packet ρ t * 𝓕 ψ t
  apply (htest s).trans
  congr 1
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht
  have he := (hlap |t| (abs_pos.mpr ht)).2
  have hp : packet ρ t = (K |t|:ℂ) := by
    rw [packet, integral_complex_ofReal, ← he]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun E => congrArg Real.exp
      (show -(E:ℝ) * abs t = -(abs t) * (E:ℝ) by ring)
  rw [hp]
  rfl

end IsingRotation.PacketFourier
