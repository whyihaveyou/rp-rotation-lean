import MathlibProbe.PhysicalPacketRotation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Orthogonal invariance with the zero value of the frequency test removed.
No local integrability of the spectral density at the frequency origin is used. -/
noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform SchwartzMap Topology ContDiff ENNReal Real
namespace IsingRotation

def HasPuncturedFourierDensity (μ : Measure Space3) (C : Space3 → ℝ) : Prop :=
  ∀ ψ : 𝓢(Space3,ℂ), ψ 0 = 0 → (∫ x, (𝓕 ψ) x ∂μ) = ∫ p, (C p:ℂ) * ψ p

private theorem integrable_off_test (C g : Space3 → ℝ) (hC : ContinuousOn C {0}ᶜ)
    (hg : Continuous g) (hk : HasCompactSupport g) (hs : tsupport g ⊆ {0}ᶜ) :
    Integrable (fun p => g p * C p) := by
  apply (ContinuousOn.integrableOn_compact hk
    (hg.continuousOn.mul (hC.mono hs))).integrable_of_forall_notMem_eq_zero
  intro x hx
  have h0 : g x = 0 := by
    by_contra hn
    exact hx (subset_tsupport g hn)
  simp [h0]

theorem puncturedDensity_invariant_of_map_eq {μ : Measure Space3} {C : Space3 → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hC : ContinuousOn C {0}ᶜ)
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (hO : μ.map O = μ) (p : Space3) : C (O p) = C p := by
  have hvol (φ : 𝓢(Space3,ℂ)) (h0 : φ 0 = 0) :
      (∫ p, (C (O.symm p):ℂ) * φ p) = ∫ p, (C p:ℂ) * φ p := by
    let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ O.toContinuousLinearEquiv φ
    have hψ0 : ψ 0 = 0 := by change φ (O 0) = 0; rw [O.map_zero,h0]
    have hcomp (x : Space3) : (𝓕 ψ) x = (𝓕 φ) (O x) :=
      Real.fourier_comp_linearIsometry O (φ : Space3 → ℂ) x
    calc
      _ = ∫ p, (C (O.symm (O p)):ℂ) * φ (O p) :=
        (O.measurePreserving.integral_comp O.toHomeomorph.measurableEmbedding
          (fun v : Space3 => (C (O.symm v):ℂ)*φ v)).symm
      _ = ∫ p, (C p:ℂ)*ψ p := by simp [ψ]
      _ = ∫ x, (𝓕 ψ) x ∂μ := (hF ψ hψ0).symm
      _ = ∫ x, (𝓕 φ) x ∂μ.map O := by
        simp only [hcomp]
        exact (integral_map O.continuous.measurable.aemeasurable
          (𝓕 φ).continuous.aestronglyMeasurable).symm
      _ = _ := by rw [hO,hF φ h0]
  let U : Set Space3 := {0}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hcomp : ContinuousOn (C ∘ O.symm) U :=
    hC.comp O.symm.continuous.continuousOn (fun x hx he => hx
      (O.symm.injective (he.trans O.symm.map_zero.symm)))
  have hd := hcomp.sub hC
  have he := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hd.locallyIntegrableOn hU.measurableSet)
  have hae := he (by
    intro g hg hk hs
    have hg0 : g 0 = 0 := by
      by_contra hn
      exact (hs (subset_tsupport g hn)) rfl
    have hkc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hk.comp_left rfl
    have hgc : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg
    let φ := hkc.toSchwartzMap hgc
    have h0 : φ 0 = 0 := by change ((g 0:ℝ):ℂ) = 0; simp [hg0]
    have hv := hvol φ h0
    change (∫ p, (C (O.symm p):ℂ)*(g p:ℂ)) = ∫ p, (C p:ℂ)*(g p:ℂ) at hv
    have hreal : (∫ p, g p*(C ∘ O.symm) p) = ∫ p, g p*C p := by
      apply Complex.ofReal_injective
      simpa only [Function.comp_apply, mul_comm (g _), ← Complex.ofReal_mul,
        integral_complex_ofReal] using hv
    change (∫ p, g p * ((C ∘ O.symm) p - C p)) = 0
    simp_rw [mul_sub]
    rw [integral_sub (integrable_off_test _ g hcomp hg.continuous hk hs)
      (integrable_off_test _ g hC hg.continuous hk hs),hreal,sub_self])
  have hAE : (C ∘ O.symm) =ᵐ[volume.restrict U] C := (ae_restrict_iff' hU.measurableSet).mpr
    (hae.mono fun x h hx => sub_eq_zero.mp (h hx))
  by_cases hp : p = 0
  · simp [hp]
  · have hn : O p ∈ U := fun h => hp (O.injective (h.trans O.map_zero.symm))
    simpa using ((Measure.eqOn_open_of_ae_eq hAE hU hcomp hC) hn).symm

private theorem exists_radial_reference :
    ∃ b : 𝓢(Space3,ℂ), b 0 = 1 ∧ ∀ (O : Space3 ≃ₗᵢ[ℝ] Space3) x, b (O x) = b x := by
  let b : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
  let f (x : Space3) : ℂ := (b (‖x‖^2):ℝ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp
    (b.contDiff.comp (contDiff_norm_sq ℝ))
  have hk : HasCompactSupport f := by
    apply HasCompactSupport.intro' (isCompact_closedBall (0:Space3) 2) Metric.isClosed_closedBall
    intro x hx
    have hh : 2 < ‖x‖ := by simpa [Metric.mem_closedBall,dist_zero_right] using hx
    have hn : ‖x‖^2 ∉ Function.support b := by
      rw [b.support_eq, Metric.mem_ball,dist_zero_right, Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change ¬ ‖x‖^2 < 2
      nlinarith [sq_nonneg (‖x‖-2)]
    change ((b (‖x‖^2):ℝ):ℂ) = 0
    simp [Function.notMem_support.mp hn]
  refine ⟨hk.toSchwartzMap hf, ?_, ?_⟩
  · change ((b (‖(0:Space3)‖^2):ℝ):ℂ) = 1
    simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  · intro O x
    change ((b (‖O x‖^2):ℝ):ℂ) = _
    rw [O.norm_map]
    rfl

/-- The radial reference subtracts the common test value at zero before
the Fourier equation is applied. Physical Schwartz integrability is used
only to cancel the ordinary spatial integrals of that reference. -/
theorem schwartz_integral_rotation_of_puncturedDensity {μ : Measure Space3} {C : Space3 → ℝ}
    (hF : HasPuncturedFourierDensity μ C)
    (hI : ∀ s : 𝓢(Space3,ℂ), Integrable (s : Space3 → ℂ) μ)
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (hinv : ∀ p : Space3, C (O p) = C p)
    (φ : 𝓢(Space3,ℂ)) : (∫ x, φ (O x) ∂μ) = ∫ x, φ x ∂μ := by
  obtain ⟨b,hb,hbr⟩ := exists_radial_reference
  let f := 𝓕⁻ φ
  let fO := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ O.toContinuousLinearEquiv f
  let β := (f 0) • b
  let s := f - β
  let u := fO - β
  have hs : s 0 = 0 := by change f 0 - (f 0)*b 0=0; rw [hb,mul_one,sub_self]
  have hu' (p : Space3) : u p = s (O p) := by
    change f (O p) - (f 0)*b p = f (O p) - (f 0)*b (O p)
    rw [hbr]
  have hu : u 0 = 0 := by rw [hu', O.map_zero, hs]
  have he : (∫ x, (𝓕 u) x ∂μ) = ∫ x, (𝓕 s) x ∂μ := by
    rw [hF u hu,hF s hs]
    calc _ = ∫ p, (C (O p):ℂ) * s (O p) := by simp only [hinv,hu']
         _ = _ := O.measurePreserving.integral_comp O.toHomeomorph.measurableEmbedding
           (fun p : Space3 => (C p:ℂ)*s p)
  have hsub (a : 𝓢(Space3,ℂ)) :
      (∫ x, (𝓕 (a-β)) x ∂μ) = (∫ x, (𝓕 a) x ∂μ) - ∫ x, (𝓕 β) x ∂μ := by
    have hh : 𝓕 (a-β) = 𝓕 a - 𝓕 β := (FourierTransform.fourierCLM ℂ 𝓢(Space3,ℂ)).map_sub a β
    rw [hh]
    exact integral_sub (hI (𝓕 a)) (hI (𝓕 β))
  change (∫ x, (𝓕 (fO-β)) x ∂μ) = ∫ x, (𝓕 (f-β)) x ∂μ at he
  rw [hsub,hsub] at he
  have hφ : 𝓕 f = φ := by simp [f]
  have ho (x : Space3) : (𝓕 fO) x = φ (O x) := by
    rw [← hφ]
    exact Real.fourier_comp_linearIsometry O (f : Space3 → ℂ) x
  simpa only [ho,hφ] using sub_left_inj.mp he

end IsingRotation
namespace IsingScaling
open IsingRotation


/-- The signed permutations of the original cubic lattice acting on a measure. -/
def CubicMeasureInvariant (μ : Measure Space) : Prop :=
  ∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), μ.map (cubicMotion p s) = μ

private theorem punctured_quarter_of_cubic {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (hcu : CubicMeasureInvariant μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (x y z : ℝ) : C (xyz (-y) x z) = C (xyz x y z) := by
  have hh := puncturedDensity_invariant_of_map_eq hF hc
    (cubicMotion (Equiv.swap 0 1) (fun i => decide (i=0))) (hcu _ _) (xyz x y z)
  have he : cubicMotion (Equiv.swap 0 1) (fun i => decide (i=0)) (xyz x y z) =
      xyz (-y) x z := by ext i; fin_cases i <;> rfl
  rwa [he] at hh

theorem punctured_frequency_base_of_cubic {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (hcu : CubicMeasureInvariant μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (i : ℤ) : ∃ d : Bool, ∀ v u z, C (planeFrequency ((i:ℝ)*(π/4)) v u z) =
      C (planeFrequency (Packet.frameAngle d) v u z) := by
  have hper (v u z : ℝ) : Function.Periodic (fun a => C (planeFrequency a v u z)) (π/2) := by
    intro a
    change C (planeFrequency (a+π/2) v u z) = C (planeFrequency a v u z)
    unfold planeFrequency
    rw [← punctured_quarter_of_cubic hcu hF hc (v*Real.cos a-u*Real.sin a)
      (v*Real.sin a+u*Real.cos a) z]
    simp [Real.cos_add, Real.sin_add]
    congr 1
    ring
  let j : ℤ := (i+1)/2
  have hcases : i=2*j ∨ i=2*j-1 := by dsimp [j]; omega
  rcases hcases with he | he
  · refine ⟨false, fun v u z => ?_⟩
    have ha : (i:ℝ)*(π/4) = Packet.frameAngle false + (j:ℝ)*(π/2) := by
      rw [he]; simp [Packet.frameAngle]; ring
    rw [ha]; exact (hper v u z).int_mul j _
  · refine ⟨true, fun v u z => ?_⟩
    have ha : (i:ℝ)*(π/4) = Packet.frameAngle true + (j:ℝ)*(π/2) := by
      rw [he]; simp [Packet.frameAngle]; ring
    rw [ha]; exact (hper v u z).int_mul j _

theorem punctured_tangent_frequency_base {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (i : ℤ) : ∃ d : Bool, ∀ v u z, C (planeFrequency ((i:ℝ)*(π/4)) v u z) =
      C (planeFrequency (Packet.frameAngle d) v u z) :=
  punctured_frequency_base_of_cubic (fun p s => ht.cubic_invariant p s) hF hc i

theorem rotation_of_cubic_punctured_directionalProfiles {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (hcu : CubicMeasureInvariant μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hI : ∀ s : 𝓢(Space3,ℂ), Integrable (s : Space → ℂ) μ)
    (hp : HasDirectionalProfiles C) (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ := by
  let p : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  have hcyc (x y z : ℝ) : C (xyz x y z) = C (xyz z x y) := by
    have hh := puncturedDensity_invariant_of_map_eq hF hc (cubicMotion p (fun _ => false))
      (hcu _ _) (xyz x y z)
    have he : cubicMotion p (fun _ => false) (xyz x y z) = xyz z x y := by
      ext i; fin_cases i <;> rfl
    rwa [he,eq_comm] at hh
  apply map_eq_of_rotated_schwartz O
  exact schwartz_integral_rotation_of_puncturedDensity hF hI O
    (orthogonal_of_angularStrips _ C hc hB.on_spectator hcyc (punctured_quarter_of_cubic hcu hF hc)
      (angularCharts_of_directionalProfiles C hc hB.on_spectator hp) O)

theorem tangent_rotation_of_punctured_directionalProfiles {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hI : ∀ s : 𝓢(Space3,ℂ), Integrable (s : Space → ℂ) μ)
    (hp : HasDirectionalProfiles C) (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ :=
  rotation_of_cubic_punctured_directionalProfiles (fun p s => ht.cubic_invariant p s) hF hc hB hI hp O

/-- Both rotational conclusions under a punctured Fourier identity and
the compact physical packets. The spectral density need not be locally
integrable at zero in this statement. -/
theorem rotation_of_cubic_punctured_physical_profiles {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (hcu : CubicMeasureInvariant μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hI : ∀ s : 𝓢(Space3,ℂ), Integrable (s : Space → ℂ) μ)
    (hp : HasPhysicalPacketProfiles C) : ∀ O : Space ≃ₗᵢ[ℝ] Space,
      μ.map O = μ ∧ ∀ c : ℝ≥0∞, c ≠ ⊤ → ∀ f : Space → ℝ≥0∞,
        Measurable f → ContinuousOn f {0}ᶜ → μ = c • Measure.dirac 0 + volume.withDensity f →
        ∀ x : Space, x ≠ 0 → f (O x) = f x := by
  intro O
  have hd := directionalProfiles_of_packet_profiles_and_base
    (punctured_frequency_base_of_cubic hcu hF hc) hc hB hp
  have h := rotation_of_cubic_punctured_directionalProfiles hcu hF hc hB hI hd O
  exact ⟨h, fun c hc' f hf hfc hm => spatialDensity_invariant_of_map_eq μ c hc' f hf hfc hm O h⟩

theorem tangent_rotation_of_punctured_physical_profiles {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) {C : Space → ℝ}
    (hF : HasPuncturedFourierDensity μ C) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hI : ∀ s : 𝓢(Space3,ℂ), Integrable (s : Space → ℂ) μ)
    (hp : HasPhysicalPacketProfiles C) : ∀ O : Space ≃ₗᵢ[ℝ] Space,
      μ.map O = μ ∧ ∀ c : ℝ≥0∞, c ≠ ⊤ → ∀ f : Space → ℝ≥0∞,
        Measurable f → ContinuousOn f {0}ᶜ → μ = c • Measure.dirac 0 + volume.withDensity f →
        ∀ x : Space, x ≠ 0 → f (O x) = f x :=
  rotation_of_cubic_punctured_physical_profiles (fun p s => ht.cubic_invariant p s) hF hc hB hI hp

end IsingScaling
