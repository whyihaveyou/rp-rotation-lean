import MathlibProbe.IsingTwoPointTangent
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.UniformSpace.HeineCantor

/-! For a compactly supported test, small translates have a common compact
support. Choose a nonnegative compact cutoff equal to one there. Vague
convergence bounds the integrals of the cutoff. Uniform continuity controls
the oscillation of the test, so the translated and original integrals differ
by a quantity tending to zero. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology CompactlySupported ENNReal

namespace IsingScaling.Packet.ParitySmoothing

/-- Eventual bounds on compact cutoffs control moving tests, without needing
a limit of the sequence of measures. -/
theorem tendsto_integral_sub_small_translation
    {μn : ℕ → Measure Space}
    [∀ n, IsFiniteMeasureOnCompacts (μn n)]
    (hb : ∀ ψ : C_c(Space, ℝ), (∀ x, 0 ≤ ψ x) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (∫ x, ψ x ∂μn n) < C)
    {u : ℕ → Space} (hu : Tendsto u atTop (𝓝 0)) (φ : C_c(Space, ℝ)) :
    Tendsto (fun n => (∫ x, φ (x + u n) ∂μn n) - ∫ x, φ x ∂μn n)
      atTop (𝓝 0) := by
  obtain ⟨r, hr⟩ := φ.hasCompactSupport.isBounded.subset_closedBall (0 : Space)
  let R : ℝ := max r 0 + 2
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right r 0]
  let bump : ContDiffBump (0 : Space) := ⟨R, R+1, hR, by linarith⟩
  let ψ : C_c(Space, ℝ) := ⟨⟨bump, bump.continuous⟩, bump.hasCompactSupport⟩
  obtain ⟨C, hC, hcut⟩ := hb ψ (fun _ => bump.nonneg)
  have h0 : ∀ z : Space, r < ‖z‖ → φ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hr hm
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := ε / (2 * C)
  have ht : 0 < t := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (φ.hasCompactSupport.uniformContinuous_of_continuous φ.continuous) t ht
  filter_upwards [hcut, Metric.tendsto_nhds.mp hu δ hδ,
    Metric.tendsto_nhds.mp hu 1 zero_lt_one] with n hn hsmall hunit
  simp only [dist_zero_right] at hsmall hunit
  have hdiff (x : Space) : |φ (x + u n) - φ x| ≤ t * ψ x := by
    by_cases hx : ‖x‖ ≤ R
    · have hψ : ψ x = 1 := bump.one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
      rw [hψ, mul_one]
      apply le_of_lt
      rw [← Real.dist_eq]
      apply hmod
      simpa [dist_eq_norm] using hsmall
    · have hrx : r < ‖x‖ := by
        dsimp [R] at hx
        linarith [le_max_left r 0]
      have hshift : r < ‖x + u n‖ := by
        have hnorm : ‖x‖ ≤ ‖x + u n‖ + ‖u n‖ := by
          simpa using norm_sub_le (x + u n) (u n)
        dsimp [R] at hx
        linarith [le_max_left r 0]
      rw [h0 _ hshift, h0 _ hrx, sub_zero, abs_zero]
      exact mul_nonneg ht.le bump.nonneg
  let trans := φ.comp (Homeomorph.addRight (u n)).toCocompactMap
  have hi : Integrable (fun x => φ (x + u n)) (μn n) :=
    trans.continuous.integrable_of_hasCompactSupport trans.hasCompactSupport
  have hj : Integrable (fun x => φ x) (μn n) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hk : Integrable (fun x => ψ x) (μn n) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  rw [Real.dist_eq, sub_zero, ← integral_sub hi hj]
  calc
    _ ≤ ∫ x, |φ (x + u n) - φ x| ∂μn n := abs_integral_le_integral_abs
    _ ≤ ∫ x, t * ψ x ∂μn n := integral_mono (hi.sub hj).abs (hk.const_mul t) hdiff
    _ = t * (∫ x, ψ x ∂μn n) := integral_const_mul _ _
    _ < t * C := mul_lt_mul_of_pos_left hn ht
    _ = ε / 2 := by dsimp [t]; field_simp [ne_of_gt hC]
    _ < ε := by linarith

/-- Vague convergence supplies local cutoff bounds, also for a sequence
eventually dominated by the convergent measures. -/
theorem eventually_bounded_integral_of_vague_domination
    {μn νn : ℕ → Measure Space} {ν : Measure Space}
    [∀ n, IsFiniteMeasureOnCompacts (νn n)]
    (hv : ∀ ψ : C_c(Space, ℝ),
      Tendsto (fun n => ∫ x, ψ x ∂νn n) atTop (𝓝 (∫ x, ψ x ∂ν)))
    (hdom : ∀ᶠ n in atTop, μn n ≤ νn n) (ψ : C_c(Space, ℝ)) (hψ : ∀ x, 0 ≤ ψ x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (∫ x, ψ x ∂μn n) < C := by
  let C := |∫ x, ψ x ∂ν| + 2
  have hC : 0 < C := by dsimp [C]; linarith [abs_nonneg (∫ x, ψ x ∂ν)]
  refine ⟨C, hC, ?_⟩
  have hcut : ∀ᶠ n in atTop, (∫ x, ψ x ∂νn n) < C := (hv ψ).eventually_lt_const
    (by dsimp [C]; linarith [le_abs_self (∫ x, ψ x ∂ν)])
  filter_upwards [hdom, hcut] with n hle hlt
  have hi : Integrable (fun x => ψ x) (νn n) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  exact (integral_mono_measure hle (Filter.Eventually.of_forall hψ) hi).trans_lt hlt

/-- Vanishing translations of the test preserve its vague limiting integral,
even when the approximating measures have infinite total mass. -/
theorem tendsto_integral_small_translation
    {μn : ℕ → Measure Space} {μ : Measure Space}
    [∀ n, IsFiniteMeasureOnCompacts (μn n)]
    (hv : ∀ ψ : C_c(Space, ℝ),
      Tendsto (fun n => ∫ x, ψ x ∂μn n) atTop (𝓝 (∫ x, ψ x ∂μ)))
    {u : ℕ → Space} (hu : Tendsto u atTop (𝓝 0)) (φ : C_c(Space, ℝ)) :
    Tendsto (fun n => ∫ x, φ (x + u n) ∂μn n) atTop (𝓝 (∫ x, φ x ∂μ)) := by
  have hmove := tendsto_integral_sub_small_translation (μn := μn)
    (eventually_bounded_integral_of_vague_domination hv (Eventually.of_forall fun _ => le_rfl))
    hu φ
  simpa only [sub_add_cancel, zero_add] using hmove.add (hv φ)

/-- A finite normalized sum of microscopic translates preserves and reflects
vague convergence. For the reverse implication domination by a fixed finite
multiple of the smoothed measures supplies cutoff bounds for the original
measures. The normalization ratio tends to one and the exact stencil identity
need only hold eventually for each test. -/
theorem vague_finite_stencil_iff
    {ι : Type*} [Fintype ι]
    {μn σn : ℕ → Measure Space} {μ : Measure Space}
    [∀ n, IsFiniteMeasureOnCompacts (μn n)] [∀ n, IsFiniteMeasureOnCompacts (σn n)]
    {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 1))
    (w : ι → ℝ) (hw : ∑ i, w i = 1) (u : ι → ℕ → Space)
    (hu : ∀ i, Tendsto (u i) atTop (𝓝 0))
    (hid : ∀ φ : C_c(Space, ℝ), ∀ᶠ n in atTop,
      q n * (∫ x, φ x ∂σn n) = ∑ i, w i * (∫ x, φ (x + u i n) ∂μn n))
    {K : ℝ≥0∞} (hdom : ∀ᶠ n in atTop, μn n ≤ K • σn n) (hK : K ≠ ⊤ := by finiteness) :
    (∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ x, φ x ∂σn n) atTop (𝓝 (∫ x, φ x ∂μ))) ↔
    (∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ x, φ x ∂μn n) atTop (𝓝 (∫ x, φ x ∂μ))) := by
  classical
  constructor
  · intro hs φ
    let : ∀ n, IsFiniteMeasureOnCompacts (K • σn n) := fun n =>
      IsFiniteMeasureOnCompacts.smul _ hK
    have hscaled (ψ : C_c(Space, ℝ)) : Tendsto (fun n => ∫ x, ψ x ∂(K • σn n))
        atTop (𝓝 (∫ x, ψ x ∂(K • μ))) := by
      simpa only [integral_smul_measure, smul_eq_mul] using (hs ψ).const_mul K.toReal
    have hb := eventually_bounded_integral_of_vague_domination hscaled hdom
    have hterm (i : ι) := (tendsto_integral_sub_small_translation hb (hu i) φ).const_mul (w i)
    have herr : Tendsto (fun n => ∑ i, w i *
        ((∫ x, φ (x + u i n) ∂μn n) - ∫ x, φ x ∂μn n)) atTop (𝓝 0) := by
      simpa only [mul_zero, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
        (fun i _ => hterm i)
    have hprod := (hq.mul (hs φ)).sub herr
    simp only [one_mul, sub_zero] at hprod
    apply hprod.congr'
    filter_upwards [hid φ] with n hn
    simp only [mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw, one_mul, hn, sub_sub_cancel]
  · intro hm φ
    have hsum : Tendsto (fun n => ∑ i, w i * (∫ x, φ (x + u i n) ∂μn n))
        atTop (𝓝 (∫ x, φ x ∂μ)) := by
      simpa only [← Finset.sum_mul, hw, one_mul] using tendsto_finsetSum Finset.univ
        (fun i _ => (tendsto_integral_small_translation hm (hu i) φ).const_mul (w i))
    have hquot := hsum.div hq one_ne_zero
    simp only [div_one] at hquot
    apply hquot.congr'
    filter_upwards [hid φ, hq.eventually_ne one_ne_zero] with n hn hnonzero
    simp only [Pi.div_apply, ← hn, mul_div_cancel_left₀ _ hnonzero]

end IsingScaling.Packet.ParitySmoothing
