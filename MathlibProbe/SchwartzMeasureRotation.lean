import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Uniqueness for locally finite covariance measures from Schwartz tests.
No finite total mass or exclusion of a contact atom is required. -/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap CompactlySupported ContDiff

namespace IsingScaling

abbrev CovSpace := EuclideanSpace ℝ (Fin 3)

theorem measure_eq_of_schwartz_integrals {μ ν : Measure CovSpace}
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (h : ∀ φ : 𝓢(CovSpace, ℂ), ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  by_contra hn
  let a := ∫ x, f x ∂μ
  let b := ∫ x, f x ∂ν
  let ε := |a - b| / 4
  have hε : 0 < ε := div_pos (abs_pos.mpr (sub_ne_zero.mpr hn)) (by norm_num)
  have : IsFiniteMeasureOnCompacts (μ + ν) :=
    ⟨fun _ hK => ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  obtain ⟨g, hgc, hgd, hL⟩ := f.hasCompactSupport.exist_eLpNorm_sub_le_of_continuous
    (μ + ν) (p := 1) hε f.continuous
  have hcast : HasCompactSupport (fun x => (g x : ℂ)) := by
    simpa [HasCompactSupport, tsupport, Function.support] using hgc
  have hdiff : ContDiff ℝ ∞ (fun x => (g x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hgd
  have he := h (hcast.toSchwartzMap hdiff)
  change ∫ x, (g x : ℂ) ∂μ = ∫ x, (g x : ℂ) ∂ν at he
  rw [integral_complex_ofReal, integral_complex_ofReal, Complex.ofReal_inj] at he
  have estimate (ξ : Measure CovSpace) [IsLocallyFiniteMeasure ξ] (hle : ξ ≤ μ + ν) :
      |(∫ x, f x ∂ξ) - ∫ x, g x ∂ξ| ≤ ε := by
    have hi := (enorm_integral_le_lintegral_enorm (μ := ξ) ((f : CovSpace → ℝ) - g)).trans
      ((eLpNorm_one_eq_lintegral_enorm (μ := ξ)).symm.le.trans
        ((eLpNorm_mono_measure _ hle).trans hL))
    rw [show (∫ x, ((f : CovSpace → ℝ) - g) x ∂ξ) =
      (∫ x, f x ∂ξ) - ∫ x, g x ∂ξ from integral_sub
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
        (hgd.continuous.integrable_of_hasCompactSupport hgc)] at hi
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
    simpa [ENNReal.toReal_ofReal hε.le, Real.norm_eq_abs] using hr
  have ha := estimate μ (Measure.le_add_right le_rfl)
  have hb := estimate ν (Measure.le_add_left le_rfl)
  rw [← he] at hb
  have ht := abs_sub_le a (∫ x, g x ∂μ) b
  rw [abs_sub_comm (∫ x, g x ∂μ) b] at ht
  change |a - _| ≤ ε at ha
  change |b - _| ≤ ε at hb
  dsimp [ε] at ha hb hε
  linarith

theorem map_eq_of_rotated_schwartz {μ : Measure CovSpace} [IsLocallyFiniteMeasure μ]
    (O : CovSpace ≃ₗᵢ[ℝ] CovSpace)
    (h : ∀ φ : 𝓢(CovSpace, ℂ), ∫ x, φ (O x) ∂μ = ∫ x, φ x ∂μ) :
    μ.map O = μ := by
  have : IsFiniteMeasureOnCompacts (μ.map O) := Measure.IsFiniteMeasureOnCompacts.map μ O.toHomeomorph
  apply measure_eq_of_schwartz_integrals
  intro φ
  rw [integral_map O.continuous.measurable.aemeasurable φ.continuous.aestronglyMeasurable]
  exact h φ

end IsingScaling
