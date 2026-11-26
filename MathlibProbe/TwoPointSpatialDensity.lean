import MathlibProbe.TwoPointAngularRotation
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The final continuous-density conclusion in AS-7, including contact at zero. -/
open MeasureTheory
open scoped ENNReal Topology SchwartzMap FourierTransform ContDiff
namespace IsingRotation

/-- An invariant measure of the form cδ₀ + f dx has an invariant continuous
representative off the origin, for any finite contact coefficient. -/
theorem spatialDensity_invariant_of_map_eq
    (μ : Measure Space3) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (f : Space3 → ℝ≥0∞) (hf : Measurable f) (hfcont : ContinuousOn f {0}ᶜ)
    (hdecomp : μ = c • Measure.dirac 0 + volume.withDensity f)
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (hinv : μ.map O = μ) :
    ∀ x : Space3, x ≠ 0 → f (O x) = f x := by
  classical
  have hv : (volume.withDensity f).map O = volume.withDensity f := by
    rw [hdecomp, Measure.map_add _ _ O.continuous.measurable, Measure.map_smul,
      Measure.map_dirac' O.continuous.measurable, O.map_zero] at hinv
    ext s hs
    have he := congrArg (fun m : Measure Space3 ↦ m s) hinv
    simp only [Measure.add_apply] at he
    apply (ENNReal.add_right_inj (a := (c • Measure.dirac (0 : Space3)) s) ?_).mp he
    simpa [Measure.smul_apply, Measure.dirac_apply' _ hs, Set.indicator_apply] using
      (show (if (0 : Space3) ∈ s then c else 0) ≠ ⊤ by split <;> simp_all)
  have hdensity : volume.withDensity (f ∘ O.symm) = volume.withDensity f := by
    rw [← hv]
    ext s hs
    rw [withDensity_apply _ hs, Measure.map_apply O.continuous.measurable hs,
      withDensity_apply _ (O.continuous.measurable hs)]
    have he := O.measurePreserving.setLIntegral_comp_preimage hs
      (hf.comp O.symm.continuous.measurable)
    simpa [Function.comp_def] using he.symm
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (μ := (volume : Measure Space3)) (hf.comp O.symm.continuous.measurable).aemeasurable
    hf.aemeasurable).mp hdensity
  have hpt := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (s := ({0}ᶜ : Set Space3)) hae)
    isOpen_compl_singleton (hfcont.comp O.symm.continuous.continuousOn
      (fun x hx hzero ↦ hx (O.symm.injective (hzero.trans O.symm.map_zero.symm)))) hfcont
  intro x hx
  have hm : O x ≠ 0 := fun h ↦ hx (O.injective (h.trans O.map_zero.symm))
  simpa using (hpt hm).symm

/-- Spatial symmetry transfers to the continuous Fourier density.  The
local integrability is on the Fourier side; the value at zero is arbitrary. -/
theorem fourierDensity_invariant_of_map_eq {μ : Measure Space3} {C : Space3 → ℝ}
    (hF : HasTwoPointFourierDensity μ C) (hL : LocallyIntegrable C volume)
    (hC : ContinuousOn C {0}ᶜ) (O : Space3 ≃ₗᵢ[ℝ] Space3) (hO : μ.map O = μ)
    (p : Space3) : C (O p) = C p := by
  have hL' : LocallyIntegrable (C ∘ O.symm) volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact (O.symm.measurePreserving.integrableOn_image O.symm.toHomeomorph.measurableEmbedding).mp
      (hL.integrableOn_isCompact (hK.image O.symm.continuous))
  have hvol (φ : 𝓢(Space3, ℂ)) :
      (∫ p, (C (O.symm p) : ℂ) * φ p) = ∫ p, (C p : ℂ) * φ p := by
    let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ O.toContinuousLinearEquiv φ
    have hcomp (x : Space3) : (𝓕 ψ) x = (𝓕 φ) (O x) :=
      Real.fourier_comp_linearIsometry O (φ : Space3 → ℂ) x
    calc
      _ = ∫ p, (C (O.symm (O p)) : ℂ) * φ (O p) :=
        (O.measurePreserving.integral_comp O.toHomeomorph.measurableEmbedding
          (fun v : Space3 ↦ (C (O.symm v) : ℂ) * φ v)).symm
      _ = ∫ p, (C p : ℂ) * ψ p := by simp [ψ]
      _ = ∫ x, (𝓕 ψ) x ∂μ := (hF ψ).symm
      _ = ∫ x, (𝓕 φ) x ∂μ.map O := by
        simp only [hcomp]
        exact (integral_map O.continuous.measurable.aemeasurable
          (𝓕 φ).continuous.aestronglyMeasurable).symm
      _ = _ := by rw [hO, hF φ]
  have hae : C ∘ O.symm =ᵐ[volume] C := by
    apply ae_eq_of_integral_contDiff_smul_eq hL' hL
    intro g hg hgc
    have hgcc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hgd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    have he := hvol (hgcc.toSchwartzMap hgd)
    change (∫ p, (C (O.symm p) : ℂ) * (g p : ℂ)) = (∫ p, (C p : ℂ) * (g p : ℂ)) at he
    apply Complex.ofReal_injective
    simpa only [Function.comp_apply,
      smul_eq_mul, mul_comm (g _), ← Complex.ofReal_mul, integral_complex_ofReal] using he
  have hpt := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (s := ({0}ᶜ : Set Space3)) hae)
    isOpen_compl_singleton (hC.comp O.symm.continuous.continuousOn
      (fun x hx hzero ↦ hx (O.symm.injective (hzero.trans O.symm.map_zero.symm)))) hC
  by_cases hp : p = 0
  · simp [hp]
  · have hm : O p ≠ 0 := fun h ↦ hp (O.injective (h.trans O.map_zero.symm))
    simpa using (hpt hm).symm

end IsingRotation
