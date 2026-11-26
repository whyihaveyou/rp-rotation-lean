import MathlibProbe.TwoPointAngularRotation
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The real change of variables from the log-radius average AS-5 to the
transverse Stieltjes profile in AS-6. Angles are measured from the chart's
normal; the real overlap uses the open first quadrant. -/

open MeasureTheory ProbabilityTheory
open scoped Real NNReal
noncomputable section
namespace IsingRotation

def smoothingWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def smoothingVariance (n : ℕ) : ℝ≥0 := ⟨(smoothingWidth n)^2, sq_nonneg _⟩
def gaussianRate (n : ℕ) : ℝ := (2 * (smoothingVariance n : ℝ))⁻¹
def gaussianFactor (n : ℕ) : ℝ := (Real.sqrt (2 * π * (smoothingVariance n : ℝ)))⁻¹

theorem gaussianRate_pos (n : ℕ) : 0 < gaussianRate n := by
  change 0 < (2 * (1 / ((n:ℝ)+1))^2)⁻¹
  positivity

/-- Coordinates for transverse length exp(w) and positive normal length
exp(w) q in the coordinate frame rotated through α. -/
def transverseValue (C : Space3 → ℝ) (z α w q : ℝ) : ℝ :=
  C (xyz (Real.exp w * (q * Real.cos α - Real.sin α))
         (Real.exp w * (q * Real.sin α + Real.cos α)) z)

theorem continuous_transverseValue {C : Space3 → ℝ} (hc : ContinuousOn C {0}ᶜ)
    {z : ℝ} (hz : z ≠ 0) (α q : ℝ) :
    Continuous (fun w => transverseValue C z α w q) := by
  apply hc.comp_continuous (continuous_xyz (Real.continuous_exp.mul continuous_const)
      (Real.continuous_exp.mul continuous_const) continuous_const)
  exact fun _ => xyz_nonzero hz

theorem transverseValue_log_sin (C : Space3 → ℝ) (z α u v : ℝ)
    (hs : 0 < Real.sin u) :
    transverseValue C z α (v + Real.log (Real.sin u)) (Real.cos u / Real.sin u) =
    circleValue C z (Real.exp v) (α + u) := by
  unfold transverseValue circleValue
  rw [Real.exp_add, Real.exp_log hs, Real.cos_add, Real.sin_add]
  congr 2 <;> field_simp [hs.ne']

private theorem gaussian_affine_map (n : ℕ) (m : ℝ) :
    (gaussianReal 0 1).map (fun u : ℝ => m + smoothingWidth n * u) =
      gaussianReal m (smoothingVariance n) := by
  rw [show (fun u : ℝ => m + smoothingWidth n * u) =
      (m + ·) ∘ (smoothingWidth n * ·) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp [smoothingVariance]
  rfl

/-- Exact normalized Gaussian integral with the original covariance values.
The pointwise spectral representation enters only after this equality. -/
theorem logAverage_gaussian_chart {C : Space3 → ℝ} (hc : ContinuousOn C {0}ᶜ)
    {z : ℝ} (hz : z ≠ 0) (a α u : ℝ) (n : ℕ) (hs : 0 < Real.sin u) :
    logAverage (gaussianReal 0 1) C z a (α+u) n =
      gaussianFactor n * ∫ w : ℝ,
        Real.exp (-(gaussianRate n)*(w-(a+Real.log (Real.sin u)))^2) *
        transverseValue C z α w (Real.cos u / Real.sin u) := by
  let m := a + Real.log (Real.sin u)
  let F := fun w => transverseValue C z α w (Real.cos u / Real.sin u)
  have hF : Continuous F := continuous_transverseValue hc hz _ _
  have hv : smoothingVariance n ≠ 0 := by
    apply ne_of_gt
    change 0 < (⟨(smoothingWidth n)^2, sq_nonneg _⟩ : ℝ≥0)
    change (0 : ℝ) < (smoothingWidth n)^2
    dsimp [smoothingWidth]
    positivity
  calc logAverage (gaussianReal 0 1) C z a (α+u) n =
      ∫ v : ℝ, F (m + smoothingWidth n * v) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        apply ae_of_all
        intro v
        dsimp only [F, m]
        rw [show a + Real.log (Real.sin u) + smoothingWidth n * v =
          (a + smoothingWidth n * v) + Real.log (Real.sin u) by ring,
          transverseValue_log_sin C z α u _ hs]
        rfl
    _ = ∫ w : ℝ, F w ∂gaussianReal m (smoothingVariance n) := by
      rw [← gaussian_affine_map n m, integral_map (by fun_prop) hF.aestronglyMeasurable]
    _ = _ := by
      rw [integral_gaussianReal_eq_integral_smul hv, ← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro w
      dsimp only [F, m, gaussianPDFReal, gaussianFactor, gaussianRate, smul_eq_mul]
      rw [mul_assoc]
      congr 2
      congr 1
      ring

end IsingRotation
