import MathlibProbe.StieltjesAngular
import MathlibProbe.AngularGaussian
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The positive Stieltjes profile and the log-radius Gaussian on the actual
axis and diagonal strips of AS-6. Continuity of the real profiles suffices,
including when the representing measures are chosen separately at each radius. -/

open Set MeasureTheory Complex
open scoped NNReal Real

noncomputable section
namespace IsingRotation

/-- Scaling the positive squared frequency transports the representing
measure by a positive reweighting and a fractional linear coordinate change. -/
theorem Stieltjes.exists_profile_rescaled (μ : FiniteMeasure Stieltjes.Parameter)
    (c : ℝ) (hc : 0 < c) :
    ∃ ν : FiniteMeasure Stieltjes.Parameter, ∀ z : Stieltjes.Frequency,
      Stieltjes.profile ν z = Stieltjes.profile μ ⟨c * (z:ℝ), mul_pos hc z.2⟩ := by
  let d (u : Stieltjes.Parameter) := 1 - (u:ℝ) + c * u
  have hd (u : Stieltjes.Parameter) : 0 < d u := by
    by_cases hz : (u:ℝ) = 0
    · simp [d, hz]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr u.2.2)
        (mul_pos hc (lt_of_le_of_ne u.2.1 (Ne.symm hz)))
  let T (u : Stieltjes.Parameter) : Stieltjes.Parameter :=
    ⟨c * u / d u, div_nonneg (mul_nonneg hc.le u.2.1) (hd u).le,
      (div_le_one (hd u)).mpr (by dsimp [d]; linarith [u.2.2])⟩
  have hdc : Continuous d := by unfold d; fun_prop
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).div hdc fun u => (hd u).ne'
  let f (u : Stieltjes.Parameter) := (d u)⁻¹
  have hf : Continuous f := hdc.inv₀ fun u => (hd u).ne'
  have hfi : Integrable f (μ:Measure Stieltjes.Parameter) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let τ := (μ:Measure Stieltjes.Parameter).withDensity fun u => ENNReal.ofReal (f u)
  have : IsFiniteMeasure τ := isFiniteMeasure_withDensity_ofReal hfi.2
  refine ⟨⟨τ.map T, inferInstance⟩, ?_⟩
  intro z
  change (∫ u, Stieltjes.kernel z u ∂(τ.map T)) = _
  rw [integral_map hT.aemeasurable (Stieltjes.kernel z).continuous.aestronglyMeasurable]
  unfold τ
  rw [integral_withDensity_eq_integral_toReal_smul (μ := (μ : Measure Stieltjes.Parameter))
    (f := fun u => ENNReal.ofReal (f u)) (ENNReal.measurable_ofReal.comp hf.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun u => Stieltjes.kernel z (T u))]
  apply integral_congr_ae
  filter_upwards with u
  rw [ENNReal.toReal_ofReal (show 0 ≤ f u from inv_nonneg.mpr (hd u).le), smul_eq_mul]
  change (d u)⁻¹ * (1-c*(u:ℝ)/d u + (c*u/d u)*(z:ℝ))⁻¹ =
      (1 - (u:ℝ) + u * (c * (z:ℝ)))⁻¹
  rw [← mul_inv]
  congr 1
  field_simp [(hd u).ne']
  dsimp [d]
  ring

theorem differentiableOn_angularChart (i : ℤ) (b a : ℝ) (hb : 0 < b)
    (ν : ℝ → FiniteMeasure AngularParameter) (M : ℝ≥0)
    (hm : ∀ w, (ν w).mass ≤ M)
    (hreal : ∀ x : Stieltjes.Frequency, Continuous fun w => Stieltjes.profile (ν w) x) :
    DifferentiableOn ℂ (fun Z => angularChart b a ν (Z - (i : ℂ) * (π / 4)))
      (angularStrip i) := by
  let u (Z : ℂ) := Z - (i : ℂ) * (π / 4)
  have hu : Differentiable ℂ u := differentiable_id.sub_const _
  have hopen : IsOpen (angularStrip i) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hrange (Z : ℂ) (hz : Z ∈ angularStrip i) : 0 < (u Z).re ∧ (u Z).re < π/2 := by
    change (i : ℝ) * (π / 4) < Z.re ∧ Z.re < ((i : ℝ) + 2) * (π / 4) at hz
    have hre : (u Z).re = Z.re - (i : ℝ) * (π / 4) := by simp [u, Complex.mul_re]
    rw [hre]
    constructor <;> linarith [hz.1, hz.2]
  have hs (Z : ℂ) (hz : Z ∈ angularStrip i) : Complex.sin (u Z) ∈ slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (angular_sin_re_pos _ (hrange Z hz).1 (hrange Z hz).2))
  have hk (Z : ℂ) (hz : Z ∈ angularStrip i) :
      (Complex.cos (u Z) / Complex.sin (u Z))^2 ∈ slitPlane :=
    angular_cotSq_slit _ (hrange Z hz).1 (hrange Z hz).2
  have hsin := Complex.differentiable_sin.comp hu
  have hcos := Complex.differentiable_cos.comp hu
  refine Stieltjes.gaussian_stieltjes_chart_holomorphic b hb hopen
    (fun Z => (a:ℂ) + Complex.log (Complex.sin (u Z)))
    (fun Z => (Complex.cos (u Z) / Complex.sin (u Z))^2) ?_ ?_ hk ν (M:ℝ)
    (fun w => by exact_mod_cast hm w) ?_
  · intro Z hZ
    exact ((differentiableAt_const (a:ℂ)).add ((Complex.differentiableAt_log (hs Z hZ)).comp Z
      (hsin Z))).differentiableWithinAt
  · apply DifferentiableOn.pow
    apply DifferentiableOn.div hcos.differentiableOn hsin.differentiableOn
    exact fun Z hz => Complex.slitPlane_ne_zero (hs Z hz)
  · intro Z hz
    exact (Stieltjes.continuous_extension_family ν M hm hreal (hk Z hz)).aestronglyMeasurable

end IsingRotation
