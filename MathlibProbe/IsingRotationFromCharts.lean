import MathlibProbe.IsingTwoPointTangent
import MathlibProbe.SchwartzMeasureRotation
import MathlibProbe.TwoPointAngularAssembly
import MathlibProbe.TwoPointSpatialDensity

/-! AS-7 from the Fourier-density and angular-chart inputs in §§12.3–12.4.
These inputs are explicit hypotheses about a susceptibility-normalized
tangent. The signed lattice symmetries are proved from the finite Gibbs sums. -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace IsingScaling
open IsingRotation

private def cycle3 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem cubic_cycle (x y z : ℝ) :
    cubicMotion cycle3 (fun _ => false) (xyz x y z) = xyz z x y := by
  ext i; fin_cases i <;> rfl

private theorem cubic_quarter (x y z : ℝ) :
    cubicMotion (Equiv.swap 0 1) (fun i => decide (i = 0)) (xyz x y z) = xyz (-y) x z := by
  ext i; fin_cases i <;> rfl

/-- Conditional formalization of AS-7. No B1 or rotational invariance
is an input. Existence of the density and of the strip charts for actual
critical tangents requires the transfer and analytic estimates in the paper. -/
theorem tangent_rotation_of_fourier_charts {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (C : Space → ℝ)
    (hF : HasTwoPointFourierDensity μ C) (hL : LocallyIntegrable C volume)
    (hc : ContinuousOn C {0}ᶜ)
    (hbound : ∀ z : ℝ, z ≠ 0 → ∃ B : ℝ, ∀ x y, ‖C (xyz x y z)‖ ≤ B)
    (hcharts : HasAngularCharts ν C) (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ := by
  have hcub (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : Space) :=
    fourierDensity_invariant_of_map_eq hF hL hc (cubicMotion p s) (ht.cubic_invariant p s) v
  have hcyc (x y z : ℝ) : C (xyz x y z) = C (xyz z x y) := by
    rw [← cubic_cycle x y z, hcub]
  have hquarter (x y z : ℝ) : C (xyz (-y) x z) = C (xyz x y z) := by
    rw [← cubic_quarter x y z, hcub]
  apply map_eq_of_rotated_schwartz O
  exact schwartz_integral_rotation_of_fourierDensity hF O
    (orthogonal_of_angularStrips ν C hc hbound hcyc hquarter hcharts O)

end IsingScaling
