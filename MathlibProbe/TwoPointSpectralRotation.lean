import MathlibProbe.AngularRealProfiles
import MathlibProbe.StieltjesStrip
import MathlibProbe.IsingRotationFromCharts

/-! From real one-direction spectral profiles to AS-7. The strip charts,
their agreement, analytic growth, and real desmoothing are conclusions.
The physical input still required is the Fourier-density and directional
spectral representation of an actual critical lattice tangent. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real
namespace IsingRotation

/-- Real Stieltjes representations on the horizontal axis and face-diagonal
normal directions, with all orientations encoded by the integer index.
The third frequency z is held nonzero. The squared normal frequency is
measured in units of the squared transverse length exp(2w). -/
def HasDirectionalProfiles (C : Space3 → ℝ) : Prop :=
  ∀ z : ℝ, z ≠ 0 → ∀ (i : ℤ) (w : ℝ), ∃ μ : FiniteMeasure Stieltjes.Parameter,
    ∀ x : Stieltjes.Frequency, Stieltjes.profile μ x =
      transverseValue C z ((i : ℝ)*(π/4)) w (Real.sqrt (x:ℝ))

private theorem angularChart_real (b a α u : ℝ) (μ : ℝ → FiniteMeasure Stieltjes.Parameter)
    (C : Space3 → ℝ) (z : ℝ) (hu : 0 < u) (hu' : u < π/2)
    (hr : ∀ w (x : Stieltjes.Frequency), Stieltjes.profile (μ w) x =
      transverseValue C z α w (Real.sqrt (x:ℝ))) :
    angularChart b a μ (u:ℂ) =
      ((∫ w : ℝ, Real.exp (-b*(w-(a+Real.log (Real.sin u)))^2) *
        transverseValue C z α w (Real.cos u / Real.sin u)) : ℝ) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos] : u < π)
  have hc := Real.cos_pos_of_mem_Ioo
    (show u ∈ Set.Ioo (-(π/2)) (π/2) from ⟨by linarith [Real.pi_pos], hu'⟩)
  let q := Real.cos u / Real.sin u
  have hq : 0 < q := div_pos hc hs
  let x : Stieltjes.Frequency := ⟨q^2, sq_pos_of_pos hq⟩
  have hval (w : ℝ) : angularStieltjes (μ w) (u:ℂ) =
      (transverseValue C z α w q : ℂ) := by
    have ht := Stieltjes.extension_posReal (μ w) x
    have hx : Real.sqrt (x:ℝ) = q := Real.sqrt_sq hq.le
    rw [hr, hx] at ht
    change Stieltjes.extension (μ w) _ = _
    convert ht using 2
    simp [x, q, Complex.ofReal_sin, Complex.ofReal_cos]
  unfold angularChart
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only
  rw [hval w, gaussianShift, ← Complex.ofReal_sin, ← Complex.ofReal_log hs.le]
  push_cast
  rfl

theorem angularCharts_of_directionalProfiles (C : Space3 → ℝ)
    (hc : ContinuousOn C {0}ᶜ)
    (hbound : ∀ z : ℝ, z ≠ 0 → ∃ B : ℝ, ∀ x y, ‖C (xyz x y z)‖ ≤ B)
    (hdir : HasDirectionalProfiles C) : HasAngularCharts (gaussianReal 0 1) C := by
  classical
  intro z hz a n
  choose μ hμ using hdir z hz
  obtain ⟨B, hB⟩ := hbound z hz
  let M := B.toNNReal
  have hm (i : ℤ) (w : ℝ) : (μ i w).mass ≤ M := by
    change ((μ i w).mass : ℝ) ≤ (M:ℝ)
    rw [← Stieltjes.profile_one, hμ]
    exact (le_abs_self _).trans ((hB _ _).trans (Real.le_coe_toNNReal _))
  have hr (i : ℤ) (x : Stieltjes.Frequency) : Continuous
      (fun w => Stieltjes.profile (μ i w) x) := by
    simp_rw [hμ]
    exact continuous_transverseValue hc hz _ _
  let b := gaussianRate n
  let c := gaussianFactor n
  let H (i : ℤ) (Z : ℂ) := (c:ℂ)*angularChart b a (μ i) (Z-(i:ℂ)*(π/4))
  refine ⟨H, ?_, ?_, ?_⟩
  · intro i
    apply DifferentiableOn.mul
    · exact differentiableOn_const _
    · exact differentiableOn_angularChart i b a (gaussianRate_pos n) (μ i) M (hm i) (hr i)
  · intro i θ hθ
    let α := (i:ℝ)*(π/4)
    let u := θ-α
    obtain ⟨hl, hh⟩ := hθ
    have hu : 0 < u := sub_pos.mpr hl
    have hu' : u < π/2 := by
      change θ < ((i:ℝ)+2)*(π/4) at hh
      dsimp [u,α]
      linarith
    have he : (θ:ℂ)-(i:ℂ)*(π/4) = (u:ℂ) := by simp [u,α]
    have hs := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos] : u < π)
    have hav := logAverage_gaussian_chart hc hz a α u n hs
    rw [show α+u=θ by dsimp [u]; ring] at hav
    dsimp only [H]
    rw [he, angularChart_real _ _ α u _ C z hu hu' (hμ i), hav, Complex.ofReal_mul]
  · let D := 16*(M:ℝ)*Real.exp (b*(π/2)^2)*Real.sqrt (π/b)
    refine ⟨‖(c:ℂ)‖*D, mul_nonneg (norm_nonneg _) (by dsimp [D]; positivity), ?_⟩
    intro Z
    obtain ⟨i, hi, hg⟩ := angularStrip_good_normal Z
    refine ⟨i, hi, ?_⟩
    let t := Z-(i:ℂ)*(π/4)
    have htr : t.re = Z.re-(i:ℝ)*(π/4) := by simp [t, Complex.mul_re]
    have hti : t.im = Z.im := by simp [t, Complex.mul_im]
    obtain ⟨hl, hh⟩ := hi
    have hlo : 0 < t.re := by rw [htr]; exact sub_pos.mpr hl
    have hhi : t.re < π/2 := by
      change Z.re < ((i:ℝ)+2)*(π/4) at hh
      rw [htr]
      linarith
    have hbnd := norm_angularChart b a (M:ℝ) (gaussianRate_pos n) (μ i)
      (fun w => show ((μ i w).mass : ℝ) ≤ (M:ℝ) from hm i w) t hlo hhi (htr ▸ hg)
    change ‖(c:ℂ)*angularChart b a (μ i) t‖ ≤ _
    rw [norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [hti, D] using hbnd

end IsingRotation

namespace IsingScaling
open IsingRotation

/-- The measure conclusion of AS-7 from its real spectral
inputs. The lattice cubic symmetries are consequences of the Gibbs sums. -/
theorem tangent_rotation_of_directionalProfiles {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    {C : Space → ℝ} (hF : HasTwoPointFourierDensity μ C)
    (hL : LocallyIntegrable C volume) (hc : ContinuousOn C {0}ᶜ)
    (hbound : ∀ z : ℝ, z ≠ 0 → ∃ B : ℝ, ∀ x y, ‖C (xyz x y z)‖ ≤ B)
    (hdir : HasDirectionalProfiles C) (O : Space ≃ₗᵢ[ℝ] Space) :
    μ.map O = μ :=
  tangent_rotation_of_fourier_charts ht (gaussianReal 0 1) C hF hL hc hbound
    (angularCharts_of_directionalProfiles C hc hbound hdir) O

end IsingScaling
