import MathlibProbe.IsingPacketTimeIntegrability
import MathlibProbe.IsingPacketFrames
import MathlibProbe.ThreeDimensionalPacketFourier

/-! The physical lattice normal has speed 2 or 2√2. Changing the time,
the transverse Lebesgue coordinates and the energy measure together
gives the positive spectrum in the orthonormal Fourier frame. -/
noncomputable section
open MeasureTheory Set
open scoped Real NNReal ENNReal ComplexConjugate
namespace IsingScaling.Packet
open IsingRotation

private def stretchTransverse (b : ℝ) (hb : b ≠ 0) : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) where
  toFun p := (b*p.1,p.2)
  invFun p := (b⁻¹*p.1,p.2)
  left_inv p := by ext <;> simp [hb]
  right_inv p := by ext <;> simp [hb]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem stretch_preserving {b : ℝ} (hb : 0 < b) :
    MeasurePreserving (stretchTransverse b hb.ne') volume (ENNReal.ofReal b⁻¹ • volume) := by
  have h : MeasurePreserving (b * ·) volume (ENNReal.ofReal b⁻¹ • volume) :=
    ⟨by fun_prop, (Real.map_volume_mul_left hb.ne').trans (by rw [abs_of_pos (inv_pos.mpr hb)])⟩
  have h2 := h.prod (MeasurePreserving.id (volume : Measure ℝ))
  rwa [Measure.prod_smul_left] at h2

private theorem integral_pair_stretch {b : ℝ} (hb : 0 < b) (F : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) :
    (∫ p : (ℝ×ℝ)×(ℝ×ℝ), F ((b*p.1.1,p.1.2),(b*p.2.1,p.2.2))) =
      (b⁻¹:ℝ) • ((b⁻¹:ℝ) • ∫ p, F p) := by
  let e := (stretchTransverse b hb.ne').toMeasurableEquiv
  let j := ENNReal.ofReal b⁻¹
  have h : MeasurePreserving e volume (j • volume) := stretch_preserving hb
  have hh : MeasurePreserving (e.prodCongr e) volume (j • j • volume) := by
    have hh := h.prod h
    rwa [Measure.prod_smul_left, Measure.prod_smul_right] at hh
  have hI := hh.integral_comp' F
  rw [integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity : 0 ≤ b⁻¹)] at hI
  exact hI

private theorem energy_units {ρ : Measure ℝ≥0} (hρ : Integrable PacketFourier.weight ρ)
    (a : ℝ≥0) (ha : 0 < a) :
    ∃ σ : Measure ℝ≥0, Integrable PacketFourier.weight σ ∧
      ∀ t : ℝ, PacketFourier.packet σ t = PacketFourier.packet ρ (t/(a:ℝ)) := by
  let m (E : ℝ≥0) := E/a
  have hm : Measurable m := by dsimp [m]; fun_prop
  refine ⟨ρ.map m, (integrable_map_measure (by unfold PacketFourier.weight; fun_prop)
    hm.aemeasurable).2 ?_, fun t => ?_⟩
  · apply (hρ.const_mul (1+(a:ℝ))).mono'
      (by unfold PacketFourier.weight; dsimp [Function.comp_def,m]; fun_prop)
    apply ae_of_all
    intro E
    have ha' : 0 < (a:ℝ) := ha
    change ‖(1+((E/a:ℝ≥0):ℝ))⁻¹‖ ≤ (1+(a:ℝ))*(1+(E:ℝ))⁻¹
    rw [NNReal.coe_div, Real.norm_of_nonneg (by positivity)]
    field_simp
    nlinarith [NNReal.coe_nonneg E, NNReal.coe_nonneg a]
  · rw [PacketFourier.packet, integral_map hm.aemeasurable (by fun_prop)]
    apply integral_congr_ae
    exact ae_of_all _ fun E => by
      simp [m, abs_of_nonneg (NNReal.coe_nonneg a), div_eq_mul_inv]; ring_nf

def unitSpatialSlice (d : Bool) (f : Space → ℝ) (φ ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ k : ℝ × ℝ, (f (planeFrequency (frameAngle d) t k.1 k.2) : ℂ) *
    (packetAutocorrelation φ k.1 * packetAutocorrelation ψ k.2)

/-- This is derived from the lattice Gibbs spectrum and off-origin spatial
convergence, with the energy scaling fixed by the actual lattice mesh. -/
theorem unitNormal_packet_spectrum_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Filter.Tendsto R Filter.atTop Filter.atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (d : Bool) (φ ψ : ℝ → ℂ)
    (hφ : Continuous φ) (kφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (kψ : HasCompactSupport ψ) :
    ∃ σ : Measure ℝ≥0, Integrable PacketFourier.weight σ ∧
      ∀ t : ℝ, t ≠ 0 → PacketFourier.packet σ t = unitSpatialSlice d f φ ψ t := by
  let b := transverseStretch d
  let a := normalStretch d
  have hb : 0 < b := transverseStretch_pos d
  have ha : 0 < a := normalStretch_pos d
  let W (z : ℝ×ℝ) := φ z.1 * ψ z.2
  let e := stretchTransverse b hb.ne'
  let Φ (z : ℝ×ℝ) : ℂ := (b:ℂ) * conj (W (e z))
  have hW : Continuous W := (hφ.comp continuous_fst).mul (hψ.comp continuous_snd)
  have kW : HasCompactSupport W := by
    apply HasCompactSupport.intro (kφ.prod kψ)
    intro z hz
    by_cases h : z.1 ∈ tsupport φ
    · simp [W, image_eq_zero_of_notMem_tsupport (show z.2 ∉ tsupport ψ from fun h' => hz ⟨h,h'⟩)]
    · simp [W, image_eq_zero_of_notMem_tsupport h]
  have hΦ : Continuous Φ := continuous_const.mul (Complex.continuous_conj.comp (hW.comp e.continuous))
  have kΦ : HasCompactSupport Φ := (kW.comp_homeomorph e).comp_left
    (g := fun z : ℂ => (b:ℂ)*conj z) (by simp)
  obtain ⟨ρ,hρ,hr⟩ := complexPlaneTimePacket_weighted_of_source src hR hf hsp hloc d Φ hΦ kΦ
  obtain ⟨σ,hσ,hs⟩ := energy_units hρ (⟨a,ha.le⟩ : ℝ≥0) ha
  refine ⟨σ,hσ,fun t ht => (hs t).trans ?_⟩
  let F (k : ℝ×ℝ) : ℂ := f (planeFrequency (frameAngle d) t k.1 k.2)
  have hF : Continuous F := Complex.continuous_ofReal.comp (hf.comp_continuous
    (continuous_xyz (continuous_const.sub (continuous_fst.mul continuous_const))
      (continuous_const.add (continuous_fst.mul continuous_const)) continuous_snd) (by
      intro k h
      have hn := norm_planeFrequency_sq (frameAngle d) t k.1 k.2
      rw [h,norm_zero] at hn
      nlinarith [sq_pos_of_ne_zero ht, sq_nonneg k.1, sq_nonneg k.2]))
  let J (p : (ℝ×ℝ)×(ℝ×ℝ)) := W p.1 * conj (W p.2) * F (p.1-p.2)
  have hj (z : ℝ×ℝ) :
      f (packetVector d (t/a) z.1 z.2) = f (planeFrequency (frameAngle d) t (b*z.1) z.2) := by
    apply congrArg f
    apply (horizontalFrame (frameAngle d)).injective
    rw [physical_frame, ← horizontalFrame_inv, LinearIsometryEquiv.apply_symm_apply]
    change xyz (a*(t/a)) (b*z.1) z.2 = xyz t (b*z.1) z.2
    rw [show a*(t/a)=t by field_simp]
  change PacketFourier.packet ρ (t / a) = _
  rw [hr (t/a) (div_ne_zero ht ha.ne')]
  calc
    _ = ∫ p : (ℝ×ℝ)×(ℝ×ℝ), (b:ℂ)^2 * J (e p.1,e p.2) := by
      apply integral_congr_ae
      apply ae_of_all
      intro p
      have h := hj (p.1-p.2)
      dsimp only [Prod.fst_sub,Prod.snd_sub] at h
      simp [Φ,J,W,e,stretchTransverse,F,map_mul,h,mul_sub]; ring
    _ = ∫ p, J p := by
      rw [integral_const_mul, show (∫ p : (ℝ×ℝ)×(ℝ×ℝ), J (e p.1,e p.2)) =
          b⁻¹ • (b⁻¹ • ∫ p, J p) from integral_pair_stretch hb J]
      simp [Complex.real_smul]
      field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
    _ = _ := packet_displacement_integral φ ψ hφ kφ hψ kψ F hF

/-- Specialization to the free Ising two-point kernel. -/
theorem unitNormal_packet_spectrum {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Filter.Tendsto R Filter.atTop Filter.atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (d : Bool) (φ ψ : ℝ → ℂ)
    (hφ : Continuous φ) (kφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (kψ : HasCompactSupport ψ) :
    ∃ σ : Measure ℝ≥0, Integrable PacketFourier.weight σ ∧
      ∀ t : ℝ, t ≠ 0 → PacketFourier.packet σ t = unitSpatialSlice d f φ ψ t :=
  unitNormal_packet_spectrum_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp hloc d φ ψ hφ kφ hψ kψ

end IsingScaling.Packet
