import MathlibProbe.IsingPhysicalPacketIdentification
import MathlibProbe.FourierShellDensity
import MathlibProbe.IsingOffOriginBounds
import MathlibProbe.IsingTangentContact
import MathlibProbe.PuncturedFourierRotation
import MathlibProbe.PuncturedFourierShells
import MathlibProbe.IsingTangentAnnularPartition

/-! Assemble the original-lattice rotation proof using only spatial data. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal FourierTransform SchwartzMap CompactlySupported
namespace IsingScaling
open IsingRotation FourierShell Packet

private theorem exists_fourierDensity_of_shells
    (μ : Measure Space) (c : ℝ) (u : Space → ℝ) (sh : ℕ → Space → ℝ) (A : ℝ)
    (hi : Integrable (fun x => (u x:ℂ))) (he : ∀ x, u (-x) = u x)
    (hs : SpatialShells (fun j x => (sh j x:ℂ)) A)
    (hse : ∀ j x, sh j (-x) = sh j x)
    (hμ : ∀ ψ : 𝓢(Space,ℂ), Tendsto (fun N => (c:ℂ)*ψ 0 + (∫ x, (u x:ℂ)*ψ x) +
       ∑ j ∈ Finset.range N, ∫ x, (sh j x:ℂ)*ψ x)
      atTop (𝓝 (∫ x, ψ x ∂μ))) :
    ∃ C : Space → ℝ, HasTwoPointFourierDensity μ C ∧ LocallyIntegrable C ∧
      ContinuousOn C {0}ᶜ ∧ BoundedAwayFromOrigin C := by
  let U (x : Space) : ℂ := u x
  let S : Space → ℂ := shellDensity (fun j x => (sh j x:ℂ))
  let D (p : Space) : ℂ := (c:ℂ) + 𝓕 U p + S p
  have hu : Continuous (𝓕 U) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ (E:=Space)).continuous₂ hi
  have hS : LocallyIntegrable S := hs.density_locallyIntegrable
  have h₁ : Continuous (fun p => (c:ℂ) + 𝓕 U p) := continuous_const.add hu
  have hD : LocallyIntegrable D := h₁.locallyIntegrable.add hS
  refine ⟨fun p => (D p).re, hasTwoPointFourierDensity_of_spatialShells μ c u sh A
    hi he hs hse hμ, fun x => Complex.reCLM.integrableAtFilter_comp (hD x),
    Complex.continuous_re.comp_continuousOn (h₁.continuousOn.add hs.continuousOn_density), ?_⟩
  intro ε hε
  refine ⟨‖(c:ℂ)‖ + (∫ x, ‖U x‖) + 6*A/ε^2, fun p hp => ?_⟩
  have hne : p ≠ 0 := norm_pos_iff.mp (hε.trans_le hp)
  calc
    ‖(D p).re‖ ≤ ‖D p‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(c:ℂ)‖ + ‖𝓕 U p‖ + ‖S p‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ _ := add_le_add
      (add_le_add_right (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) _)
      ((hs.density_bound hne).trans (div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) hs.nonneg) (sq_pos_of_pos hε) (by gcongr)))

/-- Same-sequence spatial version. Only the off-origin lattice limit and
the large-annulus estimates enter. Its continuity, integrability, contact,
Fourier density and directional spectral measures are derived. -/
theorem gibbs_rotation_of_spatial_shells {β : ℝ} {g : Site → ℝ}
    (hβ : 0 ≤ β) (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ ψ : C_c(Space,ℝ), Tendsto (fun j => ∫ x, ψ x ∂twoPointMeasure g (R j))
        atTop (𝓝 (∫ x, ψ x ∂μ)))
    {f : Space → ℝ} (hsp : OffOriginLimit g R f)
    (u : Space → ℝ) (sh : ℕ → Space → ℝ) (A : ℝ)
    (hi : Integrable (fun x => (u x:ℂ))) (he : ∀ x, u (-x) = u x)
    (hs : SpatialShells (fun j x => (sh j x:ℂ)) A) (hse : ∀ j x, sh j (-x) = sh j x)
    (hpart : ∀ ψ : 𝓢(Space,ℂ), Tendsto (fun N => ((μ {0}).toReal:ℂ)*ψ 0 +
       (∫ x, (u x:ℂ)*ψ x) + ∑ j ∈ Finset.range N, ∫ x, (sh j x:ℂ)*ψ x)
      atTop (𝓝 (∫ x, ψ x ∂μ))) :
    ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  obtain ⟨gn,gχ⟩ := hg.positive_cube_mass hβ
  have hχ (j : ℕ) := gχ (R j)
  have ht : IsTwoPointTangent β μ := ⟨g, R, hg, gn, hχ, hR, hv⟩
  let F (x : Space) := max (f x) 0
  have hpos (x : Space) (hx : x ≠ 0) : F x = f x :=
    max_eq_left (OffOriginLimit.nonneg_of_free hg hβ hR hsp x hx)
  have hspF : OffOriginLimit g R F := fun x hx q hq => hpos x hx ▸ hsp x hx q hq
  have hcnt := hspF.continuousOn hR
  let c := (μ {0}).toNNReal
  have hμ := tangent_eq_contact_add_density gn hR hχ hspF hv
  have hce : (c:ℝ≥0∞) = μ {0} := ENNReal.coe_toNNReal measure_singleton_lt_top.ne
  rw [← hce] at hμ
  obtain ⟨C, hF, hL, hc, hB⟩ := exists_fourierDensity_of_shells μ (μ {0}).toReal
    u sh A hi he hs hse hpart
  have hall := tangent_rotation_of_gibbs_spatial_limit ht hβ hg hR hcnt hspF
    (offOrigin_locallyIntegrable gn hR hχ hcnt hspF)
    (OffOriginLimit.boundedAwayFromOrigin_of_free hg hβ hR hspF) (fun _ => le_max_right _ _)
    c hμ hF hL hc hB
  intro O
  obtain ⟨hmap, hrot⟩ := hall O
  refine ⟨hmap, fun x hx => ?_⟩
  simpa only [hpos x hx, hpos (O x) ((map_ne_zero_iff O O.injective).2 hx)] using hrot x hx

/-- At bounded spatial amplitude the inverse-cube Fourier majorant is
tested only after removal of the value at zero frequency. -/
theorem exists_puncturedFourierDensity_of_volume_shells
    (μ : Measure Space) (c : ℝ) (u : Space → ℝ) (sh : ℕ → Space → ℝ) {A : ℝ}
    (hi : Integrable (fun x => (u x:ℂ))) (he : ∀ x, u (-x) = u x)
    (hs : VolumeShellBounds (fun j x => (sh j x:ℂ)) A)
    (hse : ∀ j x, sh j (-x) = sh j x)
    (hpart : ∀ q : 𝓢(Space,ℂ), Tendsto (fun N => (c:ℂ)*q 0 + (∫ x, (u x:ℂ)*q x) +
       ∑ j ∈ Finset.range N, ∫ x, (sh j x:ℂ)*q x) atTop (𝓝 (∫ x, q x ∂μ))) :
    ∃ C : Space → ℝ, HasPuncturedFourierDensity μ C ∧ ContinuousOn C {0}ᶜ ∧
      BoundedAwayFromOrigin C := by
  let U (x : Space) : ℂ := u x
  let S := shellDensity (fun j x => (sh j x:ℂ))
  let D (p : Space) : ℂ := (c:ℂ) + 𝓕 U p + S p
  have hu : Continuous (𝓕 U) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ (E:=Space)).continuous₂ hi
  have hsC : ContinuousOn S {0}ᶜ := hs.continuousOff
  have hbS (p : Space) (hp : p ≠ 0) : ‖S p‖ ≤ 10*A/‖p‖^3 :=
    (norm_tsum_le_tsum_norm (hs.summable_norm hp)).trans (hs.absolute_bound hp)
  refine ⟨fun p => (D p).re, ?_, Complex.continuous_re.comp_continuousOn
    ((continuous_const.add hu).continuousOn.add hsC), ?_⟩
  · intro φ hφ
    apply fourier_test_of_even_partition μ c u sh hi he hse hpart φ _ (hs.tested hφ)
    apply (inverse_cube_test_integrable (10*A) (mul_nonneg (by norm_num) hs.nonneg) φ hφ).mono'
      ((measurable_of_continuousOn_compl_singleton 0 hsC).aestronglyMeasurable.mul
        φ.continuous.aestronglyMeasurable)
    filter_upwards [volume.ae_ne (0:Space)] with p hp
    change ‖S p*φ p‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbS p hp) (norm_nonneg _)
  · intro ε hε
    refine ⟨‖(c:ℂ)‖ + (∫ x, ‖U x‖) + 10*A/ε^3, fun p hp => ?_⟩
    have hne : p ≠ 0 := norm_pos_iff.mp (hε.trans_le hp)
    calc
      ‖(D p).re‖ ≤ ‖D p‖ := Complex.abs_re_le_norm _
      _ ≤ ‖(c:ℂ)‖ + ‖𝓕 U p‖ + ‖S p‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := add_le_add
        (add_le_add_right (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) _)
        ((hbS p hne).trans (div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hs.nonneg) (pow_pos hε 3) (by gcongr)))

/-- For the concrete mother shell of a Gibbs tangent, only two numerical
Fourier bounds per shell are needed. All input measures and spatial
profiles in the packet laws are those of this same subsequence. -/
theorem gibbs_rotation_of_volume_annuli {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    {g : Site → ℝ} (hβ : 0 ≤ β) (hg : IsFreeTwoPoint β g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ} (hsp : OffOriginLimit g R f)
    (hf : ContinuousOn f {0}ᶜ) (hL : LocallyIntegrable f) (hB : BoundedAwayFromOrigin f)
    (hn : ∀ x, 0 ≤ f x)
    (hμ : μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {A : ℝ} (hs : VolumeShellBounds (fun j x => (spatialShell f j x:ℂ)) A) :
    ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧
      ∀ c : ℝ≥0∞, c ≠ ⊤ → ∀ F : Space → ℝ≥0∞, Measurable F → ContinuousOn F {0}ᶜ →
        μ = c • Measure.dirac 0 + volume.withDensity F → ∀ x ≠ 0, F (O x) = F x := by
  have hp := spatialShell_test_partition hL hB (measurable_of_continuousOn_compl_singleton 0 hf)
    hn hμ
  have he := hsp.even hg hR
  obtain ⟨C,hF,hcont,hbound⟩ := exists_puncturedFourierDensity_of_volume_shells μ
    (μ {0}).toReal (spatialShellInner f) (spatialShell f) (spatialShellInner_integrable hL)
    (spatialShellInner_even he) hs (spatialShell_even he) (fun ψ => (hp ψ).2)
  let c := (μ {0}).toNNReal
  have hce : (c:ℝ≥0∞) = μ {0} := ENNReal.coe_toNNReal measure_singleton_lt_top.ne
  rw [← hce] at hμ
  have hspec : HasPhysicalPacketProfiles C :=
    physical_spectralSlice_profile hβ hg hR hf hsp hL hB hn c hμ hF hcont hbound
  exact tangent_rotation_of_punctured_physical_profiles ht hF hcont hbound (fun ψ => (hp ψ).1) hspec

end IsingScaling
