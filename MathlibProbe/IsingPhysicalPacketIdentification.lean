import MathlibProbe.IsingUnitNormalPackets
import MathlibProbe.PacketFourierTest
import MathlibProbe.PhysicalPacketRotation

/-! Identify the transfer spectrum of the original spin packets with
normal-frequency tests of the spatial Fourier density, retaining the
spatial contact and using mathlib's cycles-per-unit convention. -/
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap ContDiff Topology NNReal ENNReal
namespace IsingScaling.Packet
open IsingRotation

theorem weighted_schwartz {A : Space → ℝ} (hL : LocallyIntegrable A)
    (hB : BoundedAwayFromOrigin A) (hm : Measurable A) (v : 𝓢(Space,ℂ)) :
    Integrable (fun x => (A x:ℂ)*v x) := by
  let K := Metric.closedBall (0:Space) 1
  have kK : IsCompact K := isCompact_closedBall _ _
  have hK : IntegrableOn (fun x => (A x:ℂ)*v x) K :=
    ((hL.integrableOn_isCompact kK).ofReal).mul_continuousOn v.continuous.continuousOn kK
  obtain ⟨b,hb⟩ := hB 1 one_pos
  have hK' : IntegrableOn (fun x => (A x:ℂ)*v x) Kᶜ :=
    v.integrable.integrableOn.bdd_mul (Complex.measurable_ofReal.comp hm).aestronglyMeasurable
      (ae_restrict_of_forall_mem kK.measurableSet.compl fun x hx => by
        rw [Complex.norm_real]
        apply hb
        exact le_of_lt (by simpa [K, Metric.mem_closedBall, dist_zero_right] using hx))
  simpa using hK.union hK'

private def sectionWeight (O : Space ≃ₗᵢ[ℝ] Space) (A : Space → ℝ)
    (u w : 𝓢(ℝ,ℂ)) (t : ℝ) : ℂ :=
  ∫ k : ℝ × ℝ, (A (O.symm (xyz t k.1 k.2)) : ℂ) * (u k.1 * w k.2)

private def frameTensor (O : Space ≃ₗᵢ[ℝ] Space) (v u w : 𝓢(ℝ,ℂ)) : 𝓢(Space,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ O.toContinuousLinearEquiv
    (schwartzTensor ![v,u,w])

private theorem frameTensor_apply (O : Space ≃ₗᵢ[ℝ] Space)
    (v u w : 𝓢(ℝ,ℂ)) (x : Space) :
    frameTensor O v u w x = v ((O x) 0) * u ((O x) 1) * w ((O x) 2) := by
  change schwartzTensor _ (O x) = _
  simp [schwartzTensor_apply,tensorTest,Fin.prod_univ_three]

private theorem frame_pairing' (O : Space ≃ₗᵢ[ℝ] Space) {A : Space → ℝ}
    (v u w : 𝓢(ℝ,ℂ)) (hi : Integrable (fun x => (A x:ℂ) * frameTensor O v u w x)) :
    (∫ x : Space, (A x:ℂ) * (v ((O x) 0) * u ((O x) 1) * w ((O x) 2))) =
      ∫ t, v t * sectionWeight O A u w t := by
  simp only [frameTensor_apply] at hi
  let F (t : ℝ) (k : ℝ×ℝ) :=
    v t * ((A (O.symm (xyz t k.1 k.2)) : ℂ) * (u k.1*w k.2))
  have hx (p : Space) : xyz (p 0) (p 1) (p 2) = p := by ext i; fin_cases i <;> rfl
  have he (p : Space) : F ((O p) 0) ((O p) 1,(O p) 2) =
      (A p:ℂ)*(v ((O p) 0)*u ((O p) 1)*w ((O p) 2)) := by
    simp [F,hx]; ring
  have hiF : Integrable (Function.uncurry F) :=
    (integrable_normal_transverse_iff O F).mp (by simpa only [he] using hi)
  calc
    _ = ∫ p : Space, F ((O p) 0) ((O p) 1,(O p) 2) := by simp only [he]
    _ = _ := (integral_normal_transverse O F hiF).trans (by
      apply integral_congr_ae
      exact ae_of_all _ fun t => integral_const_mul _ _)

private theorem fourier_frameTensor (O : Space ≃ₗᵢ[ℝ] Space)
    (v u w : 𝓢(ℝ,ℂ)) (x : Space) :
    (𝓕 (frameTensor O v u w)) x = (𝓕 v) ((O x) 0) * (𝓕 u) ((O x) 1) * (𝓕 w) ((O x) 2) := by
  rw [SchwartzMap.fourier_coe]
  change 𝓕 ((schwartzTensor ![v,u,w] : Space → ℂ) ∘ O) x = _
  rw [Real.fourier_comp_linearIsometry,
    show (schwartzTensor ![v,u,w] : Space → ℂ) = tensorTest (fun i => (![v,u,w] i : 𝓢(ℝ,ℂ))) from
      funext (schwartzTensor_apply _), fourier_tensorTest, Fin.prod_univ_three]
  rfl

private theorem sectionWeight_continuousOn (O : Space ≃ₗᵢ[ℝ] Space) {A : Space → ℝ}
    (hc : ContinuousOn A {0}ᶜ) (hB : BoundedAwayFromOrigin A) (u w : 𝓢(ℝ,ℂ)) :
    ContinuousOn (sectionWeight O A u w) {0}ᶜ := by
  have hm := measurable_of_continuousOn_compl_singleton 0 hc
  let p (t : ℝ) (k : ℝ×ℝ) := O.symm (xyz t k.1 k.2)
  have hn (t : ℝ) (k : ℝ×ℝ) : ‖t‖ ≤ ‖p t k‖ := by
    rw [show ‖p t k‖ = ‖xyz t k.1 k.2‖ from O.symm.norm_map _]
    exact PiLp.norm_apply_le (p := 2) (xyz t k.1 k.2) (0:Fin 3)
  have hclock (k : ℝ×ℝ) : Continuous (fun t => p t k) :=
    O.symm.continuous.comp (continuous_xyz continuous_id continuous_const continuous_const)
  have hplane (t : ℝ) : Continuous (p t) :=
    O.symm.continuous.comp (continuous_xyz continuous_const continuous_fst continuous_snd)
  intro t ht
  have ht₀ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  obtain ⟨b,hb⟩ := hB (‖t‖/2) (by positivity)
  have hi : Integrable (fun k : ℝ×ℝ => u k.1 * w k.2) := u.integrable.mul_prod w.integrable
  suffices h : ContinuousAt (sectionWeight O A u w) t from h.continuousWithinAt
  change Tendsto (fun r => ∫ k : ℝ×ℝ, (A (p r k):ℂ) * (u k.1*w k.2)) (𝓝 t) _
  apply tendsto_integral_filter_of_dominated_convergence (fun k : ℝ×ℝ => b*‖u k.1*w k.2‖)
  · apply Filter.Eventually.of_forall
    intro r
    exact (((Complex.measurable_ofReal.comp hm).comp (hplane r).measurable).mul
      (u.continuous.measurable.comp measurable_fst |>.mul
        (w.continuous.measurable.comp measurable_snd))).aestronglyMeasurable
  · filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith : ‖t‖/2 < ‖t‖))] with r hr
    apply ae_of_all
    intro k
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hb _ (le_trans (le_of_lt hr) (hn _ k))) (norm_nonneg _)
  · exact hi.norm.const_mul b
  · apply ae_of_all
    intro k
    have hz : p t k ≠ 0 := norm_pos_iff.mp (ht₀.trans_le (hn t k))
    have hcomp : Tendsto (fun r : ℝ => A (p r k)) (𝓝 t) (𝓝 (A (p t k))) :=
      (hc.continuousAt (isOpen_compl_singleton.mem_nhds hz)).tendsto.comp
        ((hclock k).continuousAt (x := t)).tendsto
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hcomp).mul_const _

/-- The full real AS-8 profile for one smooth transverse product packet.
Spatial convergence, the density decomposition and the Fourier estimates
are explicit inputs. The frequency profile is derived from the Gibbs law. -/
theorem physical_spectralSlice_profile_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (hbound : BoundedAwayFromOrigin f) (hn : ∀ x, 0 ≤ f x)
    {μ : Measure Space} (c : ℝ≥0)
    (hμ : μ = (c:ℝ≥0∞) • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {C : Space → ℝ} (hF : ∀ q : 𝓢(Space,ℂ), q 0 = 0 →
      (∫ x, (𝓕 q) x ∂μ) = ∫ p, (C p:ℂ)*q p)
    (hc : ContinuousOn C {0}ᶜ) (hB : BoundedAwayFromOrigin C)
    (d : Bool) (φ ψ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (kφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (kψ : HasCompactSupport ψ) :
    ∃ m : FiniteMeasure Stieltjes.Parameter, ∀ (ξ : ℝ) (hx : ξ ≠ 0),
      spectralSlice (horizontalFrame (frameAngle d)) C φ ψ ξ =
        (Stieltjes.profile m ⟨ξ^2,sq_pos_of_ne_zero hx⟩ : ℂ) := by
  obtain ⟨σ,hσ,hphys⟩ := unitNormal_packet_spectrum_of_source src hR hf hsp hloc d φ ψ
    hφ.continuous kφ hψ.continuous kψ
  let O := horizontalFrame (frameAngle d)
  obtain ⟨sφ,tφ⟩ := packetAutocorrelation_regular hφ kφ
  obtain ⟨sψ,tψ⟩ := packetAutocorrelation_regular hψ kψ
  let u := tφ.toSchwartzMap sφ
  let w := tψ.toSchwartzMap sψ
  have hu (t : ℝ) : (𝓕⁻ u) t = ((‖𝓕 φ (-t)‖^2:ℝ):ℂ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    exact fourier_packetAutocorrelation hφ.continuous kφ _
  have hw (t : ℝ) : (𝓕⁻ w) t = ((‖𝓕 ψ (-t)‖^2:ℝ):ℂ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    exact fourier_packetAutocorrelation hψ.continuous kψ _
  have hsl : sectionWeight O C (𝓕⁻ u) (𝓕⁻ w) = spectralSlice O C φ ψ := by
    funext t; simp only [sectionWeight,spectralSlice,transverseIntensity,hu,hw]
  let c' : ℝ≥0 := ⟨(c:ℝ)*(∫ t, ‖φ t‖^2)*(∫ t, ‖ψ t‖^2), by positivity⟩
  apply PacketFourier.exists_profile_of_distribution hσ c' _
    (hsl ▸ sectionWeight_continuousOn O hc hB (𝓕⁻ u) (𝓕⁻ w))
  intro v hv kv hv0
  let s := (kv.comp_left (g := Complex.ofReal) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hv)
  have hs (t : ℝ) : s t = (v t:ℂ) := rfl
  let ν : Measure Space := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let F (x : Space) := (𝓕 s) ((O x) 0) * u ((O x) 1) * w ((O x) 2)
  have hfM := measurable_of_continuousOn_compl_singleton 0 hf
  have hνM : Measurable (fun x => ENNReal.ofReal (f x)) := hfM.ennreal_ofReal
  have hfin : ∀ᵐ x ∂(volume:Measure Space), ENNReal.ofReal (f x) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hiφ := weighted_schwartz hloc hbound hfM (frameTensor O (𝓕 s) u w)
  have hspat := frame_pairing' O (𝓕 s) u w hiφ
  have hi : Integrable F ν := by
    apply (integrable_withDensity_iff_integrable_smul' hνM hfin).2
    simpa only [F, frameTensor_apply, ENNReal.toReal_ofReal (hn _), Complex.real_smul] using hiφ
  let T := frameTensor O s (𝓕⁻ u) (𝓕⁻ w)
  have hnull : (0:ℝ) ∉ tsupport v := fun h => (hv0 h) rfl
  have hT0 : T 0 = 0 := by simp [T,frameTensor_apply,hs,image_eq_zero_of_notMem_tsupport hnull]
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (isClosed_tsupport _ |>.isOpen_compl.mem_nhds hnull)
  obtain ⟨b,hb⟩ := hB ε hε
  have hmc := measurable_of_continuousOn_compl_singleton 0 hc
  have hzero (x : Space) (hx : ‖x‖ < ε) : T x = 0 := by
    have hnorm : ‖(O x) 0‖ ≤ ‖x‖ := (PiLp.norm_apply_le (p:=2) (O x) 0).trans_eq (O.norm_map x)
    have hnot : (O x) 0 ∉ tsupport v := he (by simpa [Metric.mem_ball] using hnorm.trans_lt hx)
    simp [T,frameTensor_apply,hs,image_eq_zero_of_notMem_tsupport hnot]
  have hit : Integrable (fun p => (C p:ℂ)*T p) := by
    apply (T.integrable.norm.const_mul b).mono'
      ((Complex.measurable_ofReal.comp hmc).aestronglyMeasurable.mul T.continuous.aestronglyMeasurable)
    apply ae_of_all
    intro p
    change ‖(C p:ℂ)*T p‖ ≤ b*‖T p‖
    by_cases hp : ε ≤ ‖p‖
    · rw [norm_mul, Complex.norm_real]; exact mul_le_mul_of_nonneg_right (hb _ hp) (norm_nonneg _)
    · simp [hzero p (lt_of_not_ge hp)]
  have hfreq := frame_pairing' O s (𝓕⁻ u) (𝓕⁻ w) hit
  have hTφ (p : Space) : (𝓕 T) p = F p := by
    simp only [T, fourier_frameTensor, FourierTransform.fourier_fourierInv_eq, F]
  have hfrom := (hF T hT0).symm
  simp only [T,frameTensor_apply,hTφ] at hfrom
  rw [hfreq,hsl,hμ] at hfrom
  have hzeroF : F 0 = (∫ t, s t) * ((∫ u, ‖φ u‖^2:ℝ):ℂ) * ((∫ u, ‖ψ u‖^2:ℝ):ℂ) := by
    have hsz : (𝓕 s) 0 = ∫ t, s t := by rw [SchwartzMap.fourier_coe,Real.fourier_eq']; simp
    simpa [F,hsz,u,w] using congrArg₂ (fun (a b:ℂ) => (∫ t, s t)*a*b)
      (packetAutocorrelation_zero φ) (packetAutocorrelation_zero ψ)
  have hid : Integrable F ((c:ℝ≥0∞) • Measure.dirac (0:Space)) :=
    (integrable_dirac (f := F) (by simp)).smul_measure (by simp)
  rw [integral_add_measure hid hi,integral_smul_measure,integral_dirac,hzeroF] at hfrom
  have hres : (∫ x, F x ∂ν) = ∫ t : ℝ, PacketFourier.packet σ t * (𝓕 s) t := by
    rw [integral_withDensity_eq_integral_toReal_smul hνM hfin]
    simp only [ENNReal.toReal_ofReal (hn _), Complex.real_smul]
    apply hspat.trans
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    rw [hphys t ht,mul_comm]
    rfl
  change _ = ((c:ℝ):ℂ)*_ + (∫ x, F x ∂ν) at hfrom
  rw [hres] at hfrom
  change (∫ t, spectralSlice O C φ ψ t * s t) = (c':ℂ) * (∫ t, s t) +
    ∫ t, PacketFourier.packet σ t * (𝓕 s) t
  calc
    _ = ∫ t, s t * spectralSlice O C φ ψ t := by
      apply integral_congr_ae; exact ae_of_all _ fun _ => mul_comm _ _
    _ = _ := hfrom.trans (by
      change _ = (((c:ℝ)*(∫ t, ‖φ t‖^2)*(∫ t, ‖ψ t‖^2):ℝ):ℂ) * _ + _
      simp only [Complex.ofReal_mul]
      ring)

/-- Specialization to the free Ising two-point kernel. -/
theorem physical_spectralSlice_profile {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (hbound : BoundedAwayFromOrigin f) (hn : ∀ x, 0 ≤ f x)
    {μ : Measure Space} (c : ℝ≥0)
    (hμ : μ = (c:ℝ≥0∞) • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {C : Space → ℝ} (hF : ∀ q : 𝓢(Space,ℂ), q 0 = 0 →
      (∫ x, (𝓕 q) x ∂μ) = ∫ p, (C p:ℂ)*q p)
    (hc : ContinuousOn C {0}ᶜ) (hB : BoundedAwayFromOrigin C)
    (d : Bool) (φ ψ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (kφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (kψ : HasCompactSupport ψ) :
    ∃ m : FiniteMeasure Stieltjes.Parameter, ∀ (ξ : ℝ) (hx : ξ ≠ 0),
      spectralSlice (horizontalFrame (frameAngle d)) C φ ψ ξ =
        (Stieltjes.profile m ⟨ξ^2,sq_pos_of_ne_zero hx⟩ : ℂ) :=
  physical_spectralSlice_profile_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp hloc hbound hn c hμ hF hc hB d φ ψ hφ kφ hψ kψ

end IsingScaling.Packet

namespace IsingScaling
open IsingRotation Packet

/-- For a lattice Gibbs tangent with the stated spatial and Fourier estimates,
both parts of the rotation conclusion follow from the Gibbs packet spectrum. -/
theorem tangent_rotation_of_gibbs_spatial_limit {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    {g : Site → ℝ} (hβ : 0 ≤ β) (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (hbound : BoundedAwayFromOrigin f) (hn : ∀ x, 0 ≤ f x)
    (c : ℝ≥0)
    (hμ : μ = (c:ℝ≥0∞) • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {C : Space → ℝ} (hF : HasTwoPointFourierDensity μ C)
    (hL : LocallyIntegrable C) (hc : ContinuousOn C {0}ᶜ) (hB : BoundedAwayFromOrigin C) :
    ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  have hP : HasPhysicalPacketProfiles C :=
    physical_spectralSlice_profile hβ hg hR hf hsp hloc hbound hn c hμ (fun q _ => hF q) hc hB
  intro O
  obtain ⟨hmap, hd⟩ := tangent_rotation_of_physical_packet_profiles ht hF hL hc hB hP O
  refine ⟨hmap, fun x hx => (ENNReal.ofReal_eq_ofReal_iff (hn _) (hn _)).1 ?_⟩
  exact hd c (by simp) _ (measurable_of_continuousOn_compl_singleton 0 hf).ennreal_ofReal
    (ENNReal.continuous_ofReal.comp_continuousOn hf) hμ x hx

end IsingScaling
