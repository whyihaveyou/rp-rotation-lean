import MathlibProbe.AngularKernel
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The positive Stieltjes measure and the shifted log-radius Gaussian in AS-6. -/

noncomputable section
open MeasureTheory Set Complex
open scoped Real

namespace IsingRotation

theorem angular_sin_re_pos (t : ℂ) (hl : 0 < t.re) (hr : t.re < π/2) :
    0 < (Complex.sin t).re := by
  have hp := Real.sin_pos_of_pos_of_lt_pi hl (by linarith [Real.pi_pos] : t.re < π)
  rw [Complex.sin_eq]
  simpa [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_sinh, Complex.sin_ofReal_re] using
    mul_pos hp (Real.cosh_pos t.im)

theorem angular_cotSq_slit (t : ℂ) (hl : 0 < t.re) (hr : t.re < π/2) :
    (Complex.cos t / Complex.sin t)^2 ∈ Complex.slitPlane := by
  have hs := angular_sin_re_pos t hl hr
  have sn : Complex.sin t ≠ 0 := fun h => by simp [h] at hs
  have cospos := Real.cos_pos_of_mem_Ioo (show t.re ∈ Ioo (-(π/2)) (π/2) from
    ⟨by linarith [Real.pi_pos], hr⟩)
  have sinpos := Real.sin_pos_of_pos_of_lt_pi hl (by linarith [Real.pi_pos] : t.re < π)
  have hc : 0 < (Complex.cos t / Complex.sin t).re := by
    rw [Complex.div_re, ← add_div]
    apply div_pos _ (Complex.normSq_pos.mpr sn)
    have hid : (Complex.cos t).re * (Complex.sin t).re +
        (Complex.cos t).im * (Complex.sin t).im = Real.cos t.re * Real.sin t.re := by
      simp only [Complex.cos_eq t, Complex.sin_eq t, Complex.add_re, Complex.sub_re,
        Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im,
        Complex.cos_ofReal_im, Complex.I_re, Complex.I_im]
      linear_combination (Real.cos t.re * Real.sin t.re) * Real.cosh_sq_sub_sinh_sq t.im
    exact hid.symm ▸ mul_pos cospos sinpos
  apply Complex.mem_slitPlane_iff.mpr
  let w := Complex.cos t / Complex.sin t
  change 0 < (w^2).re ∨ (w^2).im ≠ 0
  change 0 < w.re at hc
  by_cases hi : w.im = 0
  · left
    simpa [sq, Complex.mul_re, hi] using mul_pos hc hc
  · right
    rw [sq, Complex.mul_im]
    rw [mul_comm w.im w.re]
    intro h
    exact (mul_ne_zero hc.ne' hi) (by linarith)

abbrev AngularParameter := Icc (0:ℝ) 1

/-- The finite-measure Stieltjes profile evaluated at cotangent squared. -/
def angularStieltjes (μ : FiniteMeasure AngularParameter) (t : ℂ) : ℂ :=
  ∫ u, (1 - ((u:ℝ):ℂ) + ((u:ℝ):ℂ) * (Complex.cos t / Complex.sin t)^2)⁻¹
    ∂(μ : Measure AngularParameter)

theorem norm_angularStieltjes (μ : FiniteMeasure AngularParameter) (t : ℂ)
    (hl : 0 < t.re) (hr : t.re < π/2) (hg : |Real.cos (2*t.re)| ≤ 3/4) :
    ‖angularStieltjes μ t‖ ≤ (μ.mass:ℝ) * (16 * Real.exp (2*|t.im|)) := by
  have hs := angular_sin_re_pos t hl hr
  have sn : Complex.sin t ≠ 0 := fun e => by simp [e] at hs
  rw [mul_comm]
  apply norm_integral_le_of_norm_le_const
  apply ae_of_all
  intro u
  have hv : |2*(u:ℝ)-1| ≤ 1 := abs_le.mpr ⟨by linarith [u.2.1],by linarith [u.2.2]⟩
  have hb := angularDenominator_lower (2*t) (2*(u:ℝ)-1) hv (by simpa using hg)
  push_cast at hb
  rw [angularKernel_identity _ _ sn (norm_pos_iff.mp (by linarith))]
  exact angularKernel_bound _ _ u.2.1 u.2.2 hg

def gaussianShift (b w : ℝ) (l : ℂ) : ℂ := Complex.exp (-(b:ℂ)*((w:ℂ)-l)^2)

theorem norm_gaussianShift (b w : ℝ) (l : ℂ) :
    ‖gaussianShift b w l‖ = Real.exp (b*l.im^2)*Real.exp (-b*(w-l.re)^2) := by
  rw [gaussianShift, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [sq, Complex.mul_re, Complex.mul_im]
  ring

/-- The unnormalized Gaussian chart. A positive scalar normalization may be
restored uniformly after the angular constancy assertion. -/
def angularChart (b a : ℝ) (μ : ℝ → FiniteMeasure AngularParameter) (t : ℂ) : ℂ :=
  ∫ w:ℝ, gaussianShift b w ((a:ℂ)+Complex.log (Complex.sin t)) * angularStieltjes (μ w) t

/-- The real part of the logarithmic shift translates a Gaussian of fixed
mass. The imaginary part is uniformly bounded by half a turn of the
right half-plane. The resulting constant works in every good chart. -/
theorem norm_angularChart (b a M : ℝ) (hb : 0 < b)
    (μ : ℝ → FiniteMeasure AngularParameter) (hm : ∀ w, ((μ w).mass:ℝ) ≤ M)
    (t : ℂ) (hl : 0 < t.re) (hr : t.re < π/2) (hg : |Real.cos (2*t.re)| ≤ 3/4) :
    ‖angularChart b a μ t‖ ≤
        (16*M*Real.exp (b*(π/2)^2)*Real.sqrt (π/b))*Real.exp (2*|t.im|) := by
  let l := (a:ℂ) + Complex.log (Complex.sin t)
  have hi : |l.im| ≤ π/2 := by
    simpa [l, Complex.log_im] using
      (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (angular_sin_re_pos t hl hr))).le
  have hsq : l.im^2 ≤ (π/2)^2 := by
    nlinarith [sq_abs l.im, mul_self_le_mul_self (abs_nonneg l.im) hi]
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hb.le)
  let A := Real.exp (b*(π/2)^2) * (M * (16 * Real.exp (2*|t.im|)))
  have hM : 0 ≤ M := (NNReal.coe_nonneg _).trans (hm 0)
  have hbound : ∀ w : ℝ, ‖gaussianShift b w l * angularStieltjes (μ w) t‖ ≤
      A * Real.exp (-b*(w-l.re)^2) := by
    intro w
    rw [norm_mul, norm_gaussianShift]
    calc
      _ ≤ (Real.exp (b*(π/2)^2)*Real.exp (-b*(w-l.re)^2)) *
          (M*(16*Real.exp (2*|t.im|))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le)
        · exact (norm_angularStieltjes _ _ hl hr hg).trans
            (mul_le_mul_of_nonneg_right (hm w) (by positivity))
        · positivity
        · positivity
      _ = _ := by dsimp [A]; ring
  calc
    _ ≤ ∫ w : ℝ, A * Real.exp (-b*(w-l.re)^2) :=
      norm_integral_le_of_norm_le (((integrable_exp_neg_mul_sq hb).comp_sub_right l.re).const_mul A)
         (ae_of_all _ hbound)
    _ = _ := by
      rw [integral_const_mul, integral_sub_right_eq_self
        (f := fun x : ℝ => Real.exp (-b*x^2)), integral_gaussian]
      dsimp [A]; ring

/-- Good normals cover the plane with the same growth constant when the
spectral masses are bounded uniformly in the normal and log radius. -/
theorem exists_angularChart_bound (b a M : ℝ) (hb : 0 < b)
    (μ : ℤ → ℝ → FiniteMeasure AngularParameter)
    (hm : ∀ i w, ((μ i w).mass:ℝ) ≤ M) (z : ℂ) :
    ∃ i : ℤ, z ∈ angularStrip i ∧
      ‖angularChart b a (μ i) (z - (((i:ℝ)*(π/4):ℝ):ℂ))‖ ≤
        (16*M*Real.exp (b*(π/2)^2)*Real.sqrt (π/b))*Real.exp (2*|z.im|) := by
  obtain ⟨i, hi, hg⟩ := angularStrip_good_normal z
  refine ⟨i,hi,?_⟩
  rcases hi with ⟨h₁,h₂⟩
  have hb' := norm_angularChart b a M hb (μ i) (hm i) (z - (((i:ℝ)*(π/4):ℝ):ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hb'
  exact hb' (by linarith) (by linarith) hg

end IsingRotation
