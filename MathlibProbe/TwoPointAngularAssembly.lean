import MathlibProbe.TwoPointAngularRotation
import MathlibProbe.AngularStrip

/-! The nine-direction argument from the analytic charts for the smoothed
fixed-spectator density through to the spatial Schwartz tests. -/
open MeasureTheory
open scoped Real Topology SchwartzMap

noncomputable section
namespace IsingRotation

/-- Data to be supplied by the Stieltjes normal-frequency representation
and the complex integral in AS-6 for each positive smoothing width. -/
def HasAngularCharts (ν : Measure ℝ) (C : Space3 → ℝ) : Prop :=
  ∀ z : ℝ, z ≠ 0 → ∀ a : ℝ, ∀ n : ℕ, ∃ H : ℤ → ℂ → ℂ,
    (∀ i, DifferentiableOn ℂ (H i) (angularStrip i)) ∧
    (∀ i (θ : ℝ), (θ : ℂ) ∈ angularStrip i → H i θ = (logAverage ν C z a θ n : ℂ)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, ∃ i, w ∈ angularStrip i ∧
                                            ‖H i w‖ ≤ B * Real.exp (2 * |w.im|)

theorem orthogonal_of_angularStrips (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ)
    (hbound : ∀ z : ℝ, z ≠ 0 → ∃ B : ℝ, ∀ x y, ‖C (xyz x y z)‖ ≤ B)
    (hcycle : ∀ x y z, C (xyz x y z) = C (xyz z x y))
    (hquarter : ∀ x y z, C (xyz (-y) x z) = C (xyz x y z))
    (hcharts : HasAngularCharts ν C)
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (p : Space3) : C (O p) = C p := by
  apply orthogonal_of_radial C _ O p
  apply radial_of_circles C hc hcycle
  intro z hz r hr θ
  apply circleValue_eq_of_angularExtensions ν C hc hbound _ hz hr θ
  intro z hz a n
  obtain ⟨H, hd, hr, B, hB, hg⟩ := hcharts z hz a n
  let h (t : ℝ) : ℂ := logAverage ν C z a t n
  have hper : Function.Periodic h (π / 2) := by
    intro t
    unfold h logAverage
    simp only [circleValue, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      mul_neg, hquarter]
  obtain ⟨F, hF, hp, hloc, hreal⟩ := glue_angularStrips H h hd hr hper
  refine ⟨F, hF, hp, ⟨B, hB, ?_⟩, hreal⟩
  intro w
  obtain ⟨i, hi, hb⟩ := hg w
  rwa [hloc i hi]

#print axioms orthogonal_of_angularStrips
end IsingRotation
