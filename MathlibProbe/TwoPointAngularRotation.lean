import MathlibProbe.AngularEntire
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Desmoothing and the Euclidean and Fourier steps in §§12.3–12.4.
The analytic extension of each angular average is an explicit input. -/

open Filter MeasureTheory
open scoped Topology Real FourierTransform SchwartzMap

noncomputable section
namespace IsingRotation

abbrev Space3 := EuclideanSpace ℝ (Fin 3)

def xyz (x y z : ℝ) : Space3 := WithLp.toLp 2 ![x, y, z]

theorem continuous_xyz {X : Type*} [TopologicalSpace X] {a b c : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun t ↦ xyz (a t) (b t) (c t)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

theorem xyz_nonzero {x y z : ℝ} (hz : z ≠ 0) : xyz x y z ≠ 0 := by
  intro h
  exact hz (congrArg (fun v : Space3 ↦ v 2) h)

def circleValue (C : Space3 → ℝ) (z r θ : ℝ) : ℝ :=
  C (xyz (r * Real.cos θ) (r * Real.sin θ) z)

/-- Standardized log-radius smoothing. Take ν to be standard normal for AS-5. -/
def logAverage (ν : Measure ℝ) (C : Space3 → ℝ) (z a θ : ℝ) (n : ℕ) : ℝ :=
  ∫ u, circleValue C z (Real.exp (a + (1 / ((n : ℝ) + 1)) * u)) θ ∂ν

private theorem logAverage_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ) (z a θ : ℝ) (hz : z ≠ 0)
    (B : ℝ) (hb : ∀ x y, ‖C (xyz x y z)‖ ≤ B) :
    Tendsto (logAverage ν C z a θ) atTop (𝓝 (circleValue C z (Real.exp a) θ)) := by
  have hcirc : Continuous (circleValue C z · θ) := by
    apply hc.comp_continuous (continuous_xyz (continuous_id.mul continuous_const)
      (continuous_id.mul continuous_const) continuous_const)
    intro r
    exact xyz_nonzero hz
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun n (u : ℝ) ↦ circleValue C z (Real.exp (a + (1 / ((n : ℝ) + 1)) * u)) θ)
    (f := fun _ ↦ circleValue C z (Real.exp a) θ) (fun _ ↦ B)
    (fun n ↦ (hcirc.comp (Real.continuous_exp.comp
      (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ Filter.Eventually.of_forall (fun _ ↦ hb _ _)) (by
      refine Filter.Eventually.of_forall fun u ↦ ?_
      have ht := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const u
      have hs : Tendsto (fun n : ℕ ↦ a + (1 / ((n : ℝ) + 1)) * u) atTop (𝓝 a) := by
        simpa using ht.const_add a
      exact hcirc.continuousAt.tendsto.comp (Real.continuous_exp.continuousAt.tendsto.comp hs))
  change Tendsto (fun n : ℕ ↦ ∫ u, circleValue C z (Real.exp (a + (1 / ((n : ℝ) + 1)) * u)) θ ∂ν) atTop _
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Complex angular continuation, growth and period imply pointwise constancy
after removing the log-radius smoothing. No all-scale power-law hypothesis. -/
theorem circleValue_eq_of_angularExtensions (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ)
    (hbound : ∀ z : ℝ, z ≠ 0 → ∃ B : ℝ, ∀ x y, ‖C (xyz x y z)‖ ≤ B)
    (hext : ∀ z : ℝ, z ≠ 0 → ∀ a : ℝ, ∀ n : ℕ, ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧ Function.Periodic F ((Real.pi / 2 : ℝ) : ℂ) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖F w‖ ≤ B * Real.exp (2 * |w.im|)) ∧
      ∀ θ : ℝ, F θ = (logAverage ν C z a θ n : ℂ))
    {z r : ℝ} (hz : z ≠ 0) (hr : 0 < r) (θ : ℝ) :
    circleValue C z r θ = circleValue C z r 0 := by
  obtain ⟨B, hb⟩ := hbound z hz
  have heq : logAverage ν C z (Real.log r) θ = logAverage ν C z (Real.log r) 0 := by
    funext n
    obtain ⟨F, hF, hp, ⟨b, hb0, hG⟩, hreal⟩ := hext z hz _ n
    apply Complex.ofReal_injective
    rw [← hreal θ, ← hreal 0]
    exact angularEntire_constant F hF hp b hb0 hG _ _
  have h1 := logAverage_tendsto ν C hc z (Real.log r) θ hz B hb
  have h2 := logAverage_tendsto ν C hc z (Real.log r) 0 hz B hb
  rw [heq] at h1
  simpa [Real.exp_log hr] using tendsto_nhds_unique h1 h2

private theorem collapse_plane (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ)
    (hθ : ∀ z : ℝ, z ≠ 0 → ∀ r : ℝ, 0 < r → ∀ θ, circleValue C z r θ = circleValue C z r 0)
    (x y z : ℝ) : C (xyz x y z) = C (xyz ‖(⟨x,y⟩ : ℂ)‖ 0 z) := by
  let w : ℂ := ⟨x,y⟩
  by_cases hw : w = 0
  · have hx : x = 0 := congrArg Complex.re hw
    have hy : y = 0 := congrArg Complex.im hw
    change C (xyz x y z) = C (xyz ‖w‖ 0 z)
    rw [hw, norm_zero, hx, hy]
  have heq : ∀ b : ℝ, b ≠ 0 → C (xyz x y b) = C (xyz ‖w‖ 0 b) := by
    intro b hb
    simpa [circleValue, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg, w] using
      hθ b hb ‖w‖ (norm_pos_iff.mpr hw) w.arg
  by_cases hz : z ≠ 0
  · exact heq z hz
  have hxy : xyz x y z ≠ 0 := by
    intro h
    apply hw
    exact Complex.ext (congrArg (fun v : Space3 ↦ v 0) h) (congrArg (fun v : Space3 ↦ v 1) h)
  have hr : xyz ‖w‖ 0 z ≠ 0 := by
    intro h
    exact hw (norm_eq_zero.mp (congrArg (fun v : Space3 ↦ v 0) h))
  have hz0 := not_ne_iff.mp hz
  subst z
  have cont (u v : ℝ) (huv : xyz u v 0 ≠ 0) : ContinuousAt (fun t ↦ C (xyz u v t)) 0 :=
    (hc.continuousAt (isOpen_compl_singleton.mem_nhds huv)).comp
      (continuous_xyz continuous_const continuous_const continuous_id).continuousAt
  have h1 := (cont x y hxy).tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := (cont ‖w‖ 0 hr).tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_nhds_unique _ h2
  exact h1.congr (fun n ↦ heq _ (by positivity : 0 < 1 / ((n : ℝ) + 1)).ne')

/-- A single coordinate-plane circle result off the spectator zero plane,
continuity away from the origin, and the cyclic lattice permutation suffice. -/
theorem radial_of_circles (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ)
    (hcycle : ∀ x y z, C (xyz x y z) = C (xyz z x y))
    (hθ : ∀ z : ℝ, z ≠ 0 → ∀ r : ℝ, 0 < r → ∀ θ, circleValue C z r θ = circleValue C z r 0)
    (p : Space3) : C p = C (xyz ‖p‖ 0 0) := by
  have hrep : p = xyz (p 0) (p 1) (p 2) := by ext i; fin_cases i <;> rfl
  let w : ℂ := ⟨p 0,p 1⟩
  let v : ℂ := ⟨p 2,‖w‖⟩
  have hv : ‖v‖ = ‖p‖ := by
    have hv2 := Complex.sq_norm v
    have hw2 := Complex.sq_norm w
    have hp2 := EuclideanSpace.real_norm_sq_eq p
    simp [Fin.sum_univ_three] at hp2
    simp only [Complex.normSq_apply, v, w] at hv2 hw2
    nlinarith [norm_nonneg v, norm_nonneg p, sq_nonneg (‖v‖ - ‖p‖)]
  calc C p = C (xyz (p 0) (p 1) (p 2)) := congrArg C hrep
       _ = C (xyz ‖w‖ 0 (p 2)) := collapse_plane C hc hθ _ _ _
       _ = C (xyz (p 2) ‖w‖ 0) := hcycle _ _ _
       _ = C (xyz ‖v‖ 0 0) := collapse_plane C hc hθ _ _ _
       _ = C (xyz ‖p‖ 0 0) := by rw [hv]

theorem orthogonal_of_radial (C : Space3 → ℝ)
    (h : ∀ p : Space3, C p = C (xyz ‖p‖ 0 0))
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (p : Space3) : C (O p) = C p := by
  rw [h (O p), h p, O.norm_map]

/-- Fourier density identification in the Fourier convention of mathlib.
This permits an arbitrary contact in the spatial measure. -/
def HasTwoPointFourierDensity (μ : Measure Space3) (C : Space3 → ℝ) : Prop :=
  ∀ f : 𝓢(Space3, ℂ), (∫ x, (𝓕 f) x ∂μ) = ∫ p, (C p : ℂ) * f p

/-- Inverting a radial Fourier density preserves every spatial Schwartz test. -/
theorem schwartz_integral_rotation_of_fourierDensity
    {μ : Measure Space3} {C : Space3 → ℝ} (hμ : HasTwoPointFourierDensity μ C)
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (hinv : ∀ p : Space3, C (O p) = C p)
    (φ : 𝓢(Space3, ℂ)) : (∫ x, φ (O x) ∂μ) = ∫ x, φ x ∂μ := by
  let f := 𝓕⁻ φ
  let fO := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ O.toContinuousLinearEquiv f
  have hφ : 𝓕 f = φ := by simp [f]
  have hcomp (x : Space3) : (𝓕 fO) x = φ (O x) := by
    rw [← hφ]
    exact Real.fourier_comp_linearIsometry O (f : Space3 → ℂ) x
  calc
    _ = ∫ x, (𝓕 fO) x ∂μ := by simp only [hcomp]
    _ = ∫ p, (C p : ℂ) * fO p := hμ fO
    _ = ∫ p, (C (O p) : ℂ) * f (O p) := by simp only [hinv]; rfl
    _ = ∫ p, (C p : ℂ) * f p :=
      O.measurePreserving.integral_comp O.toHomeomorph.measurableEmbedding (fun p : Space3 ↦ (C p : ℂ) * f p)
    _ = ∫ x, φ x ∂μ := by rw [← hμ f, hφ]

end IsingRotation
