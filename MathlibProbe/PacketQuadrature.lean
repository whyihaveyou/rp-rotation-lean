import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import MathlibProbe.PositiveTimeLaplace

/-! Finite point packets approximate every continuous two-point kernel on
a common compact transverse support, with signed quadrature coefficients
independent of the positive separation used by the kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IsingRotation.Quadrature

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
private theorem integrate_cells (q : SimpleFunc X X) (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) :
    (∫ x, f x * g (q x) ∂μ) = ∑ i ∈ q.range, (∫ x in q ⁻¹' {i}, f x ∂μ) * g i := by
  classical
  let F (i : X) := (q ⁻¹' {i}).indicator fun x => f x * g i
  have hrep (x : X) : f x * g (q x) = ∑ i ∈ q.range, F i x := by
    rw [Finset.sum_eq_single (q x)]
    · simp [F]
    · intro i _ hi
      simp [F, hi.symm]
    · intro hx
      exact (hx (q.mem_range_self x)).elim
  simp_rw [hrep]
  rw [integral_finsetSum _ (fun i _ => (hf.mul_const (g i)).indicator (q.measurableSet_fiber i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (q.measurableSet_fiber i), integral_mul_const]

theorem exists_signed_packet_quadrature [Nonempty X] (μ : Measure X) [SFinite μ]
    (f : X → ℝ) (hf : Integrable f μ) (hfm : Measurable f) :
    ∃ (S : ℕ → Finset X) (c : ℕ → X → ℝ), ∀ K : C(X × X, ℝ),
      Tendsto (fun n => ∑ i ∈ S n, ∑ j ∈ S n, c n i * c n j * K (i,j)) atTop
        (𝓝 (∫ p : X × X, f p.1 * f p.2 * K p ∂μ.prod μ)) := by
  classical
  let x₀ := Classical.arbitrary X
  let q (n : ℕ) : SimpleFunc X X := SimpleFunc.approxOn id measurable_id univ x₀ (mem_univ _) n
  have hq (x : X) : Tendsto (fun n => q n x) atTop (𝓝 x) :=
    SimpleFunc.tendsto_approxOn measurable_id (mem_univ _) (by simp)
  let c (n : ℕ) (i : X) := ∫ x in q n ⁻¹' {i}, f x ∂μ
  refine ⟨fun n => (q n).range, c, ?_⟩
  intro K
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn K.continuous.continuousOn
  have hb (p : X×X) := hB p (mem_univ _)
  let G (n : ℕ) (p : X × X) := f p.1 * f p.2 * K (q n p.1,q n p.2)
  let bnd (p : X × X) := ‖f p.1‖ * ‖f p.2‖ * B
  have hi : Integrable bnd (μ.prod μ) := (hf.norm.mul_prod hf.norm).mul_const _
  have hm (n : ℕ) : Measurable (G n) :=
    (hfm.comp measurable_fst).mul (hfm.comp measurable_snd) |>.mul
      (K.continuous.measurable.comp (((q n).measurable.comp measurable_fst).prodMk
        ((q n).measurable.comp measurable_snd)))
  have hbound (n : ℕ) : ∀ p, ‖G n p‖ ≤ bnd p := by
    intro p
    simp only [G,bnd,norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have heq (n : ℕ) : (∫ p, G n p ∂μ.prod μ) =
      ∑ i ∈ (q n).range, ∑ j ∈ (q n).range, c n i*c n j*K (i,j) := by
    rw [integral_prod _ (hi.mono' (hm n).aestronglyMeasurable (ae_of_all _ (hbound n)))]
    have hin (x : X) : (∫ y, G n (x,y) ∂μ) =
        f x * ∑ j ∈ (q n).range, c n j * K (q n x,j) := by
      change (∫ y, f x * f y * K (q n x,q n y) ∂μ) = _
      simp_rw [mul_assoc, integral_const_mul, integrate_cells (q n) μ f
        (fun j => K (q n x,j)) hf]
      rfl
    simp_rw [hin, integrate_cells (q n) μ f
      (fun i => ∑ j ∈ (q n).range, c n j * K (i,j)) hf]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.mul_sum, c, mul_assoc]
  simp_rw [← heq]
  apply tendsto_integral_of_dominated_convergence bnd (fun n => (hm n).aestronglyMeasurable)
    hi (fun n => ae_of_all _ (hbound n))
  apply ae_of_all
  intro p
  exact (K.continuous.continuousAt.tendsto.comp ((hq p.1).prodMk_nhds (hq p.2))).const_mul _

/-- A positive energy spectrum for all finite signed point packets gives
a positive energy spectrum for their compactly smeared autocorrelation. -/
theorem exists_smooth_packet_laplace [Nonempty X] (μ : Measure X) [SFinite μ]
    (f : X → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (K : Laplace.Time → C(X × X, ℝ))
    (hfinite : ∀ (S : Finset X) (c : X → ℝ), ∃ ρ : Measure ℝ≥0, ∀ t : Laplace.Time,
      Integrable (fun E : ℝ≥0 => Real.exp (-t.val*E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t.val*E) ∂ρ) =
        ∑ i ∈ S, ∑ j ∈ S, c i*c j*K t (i,j)) :
    ∃ ρ : Measure ℝ≥0, ∀ t : Laplace.Time,
      Integrable (fun E : ℝ≥0 => Real.exp (-t.val*E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t.val*E) ∂ρ) =
        ∫ p : X×X, f p.1*f p.2*K t p ∂μ.prod μ := by
  obtain ⟨S,c,h⟩ := exists_signed_packet_quadrature μ f hf hfm
  choose σ hσ using fun n : ℕ => hfinite (S n) (c n)
  apply Laplace.exists_laplace_measure_of_laplace_limits σ _
    (fun n t => (hσ n t).1)
  intro t
  simpa only [fun n => (hσ n t).2] using h (K t)

end IsingRotation.Quadrature
