import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import MathlibProbe.RotorHeisenbergComplexPartition
import MathlibProbe.RightHalfPlaneLogDerivative

/-! # Local complex bounds for the two-point Heisenberg comparison

On a disk in the uniform field, an unperturbed real Gibbs magnetization at
the centre has norm at most one. The one-site logarithmic derivative estimate
gives real part at least minus two throughout the disk. Borel–Carathéodory
then bounds the modulus at the target independently of volume. On a second
disk, differentiation in a local field recovers the connected two-point
moment. Cauchy's estimate bounds the original two-point moment there.
-/

noncomputable section
open Metric Set
namespace IsingScaling.Rotor.HeisenbergField.ComplexBounds

open ComplexPartition

theorem norm_magnetization_disk {m : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hd : DifferentiableOn ℂ m (ball 0 ρ)) (h0 : ‖m 0‖ ≤ 1)
    (hre : ∀ w ∈ ball (0 : ℂ) ρ, -2 ≤ (m w).re) :
    ‖m 1‖ ≤ 1 + 6 / (ρ - 1) := by
  have hzero : (m 0).re ≤ 1 := (Complex.re_le_norm _).trans h0
  have hmap : MapsTo (fun w => m 0 - m w) (ball (0 : ℂ) ρ) {v : ℂ | v.re ≤ 3} := by
    intro w hw
    change (m 0 - m w).re ≤ 3
    rw [Complex.sub_re]
    linarith [hre w hw]
  have h1 : (1 : ℂ) ∈ ball 0 ρ := mem_ball_zero_iff.mpr (by simpa using hρ)
  have hb := Complex.borelCaratheodory_zero (by norm_num : (0:ℝ) < 3)
    (hd.const_sub (m 0)) hmap (by linarith) h1 (sub_self _)
  have hdiff : ‖m 0 - m 1‖ ≤ 6 / (ρ - 1) := by norm_num at hb ⊢; exact hb
  calc ‖m 1‖ = ‖m 0 - (m 0 - m 1)‖ := by rw [sub_sub_cancel]
       _ ≤ ‖m 0‖ + ‖m 0 - m 1‖ := norm_sub_le _ _
       _ ≤ 1 + 6 / (ρ - 1) := add_le_add h0 hdiff

theorem norm_pair_from_response {m : ℂ → ℂ} {p m₁ m₂ : ℂ} {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hd : DiffContOnCl ℂ m (ball 0 δ))
    (hb : ∀ z ∈ sphere (0 : ℂ) δ, ‖m z‖ ≤ M)
    (hder : HasDerivAt m (p - m₁*m₂) 0) (h₁ : ‖m₁‖ ≤ M) (h₂ : ‖m₂‖ ≤ M) :
    ‖p‖ ≤ M / δ + M^2 := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hd hb
  rw [hder.deriv] at h
  calc ‖p‖ ≤ ‖p - m₁*m₂‖ + ‖m₁*m₂‖ := norm_le_norm_sub_add _ _
       _ ≤ M / δ + M^2 := by
         rw [norm_mul, pow_two]
         exact add_le_add h (mul_le_mul h₁ h₂ (norm_nonneg _) hM)

variable {V : Type*} [Fintype V]

/-- Normalized finite-volume expectation in a real unit direction. -/
def magnetization (J : V → V → ℝ) (H : ComplexPartition.Field V) (x : V) (u : Spin 3) : ℂ :=
  insertion J H x u / partition J H

/-- The nonvanishing used at a particular direction along an actual field
segment. The base is the real uniform field, and the second perturbation
is placed at the specified site of the same finite graph. -/
def shiftNonvanishing (J : V → V → ℝ) (h₀ ρ : ℝ) (H : ComplexPartition.Field V)
    (x : V) (u : Spin 3) : Prop :=
  ∀ w ∈ ball (0 : ℂ) ρ, ∀ v : ℂ, 0 ≤ v.re →
    partition J (addAt (affine (uniform h₀) (H - uniform h₀) w) x u v) ≠ 0

omit [Fintype V] in
private theorem affine_at_base (H D : ComplexPartition.Field V) : affine H D 0 = H := by
  funext x i
  simp [affine]

omit [Fintype V] in
private theorem affine_at_target (H K : ComplexPartition.Field V) : affine H (K - H) 1 = K := by
  funext x i
  simp [affine]

/-- The constant in the real-part bound is independent of the site, graph
and volume. The input concerns only the original finite partition. -/
theorem magnetization_re_lower (J : V → V → ℝ) (H : ComplexPartition.Field V) (x : V) (u : Spin 3)
    (hz : ∀ v : ℂ, 0 ≤ v.re → partition J (addAt H x u v) ≠ 0) :
    -2 ≤ (magnetization J H x u).re := by
  have bound := MathlibProbe.RightHalfPlaneLogDerivative.re_logDeriv_zero_ge_neg_two_type
    (T := 1) (entire_partition_addAt J H x u) hz
    (fun v => by simpa only [one_mul] using norm_partition_addAt J H x u v)
  simpa only [one_mul, mul_one, (hasDerivAt_partition_addAt J H x u 0).deriv, addAt_zero,
    magnetization] using bound

theorem norm_magnetization_of_nonvanishing (J : V → V → ℝ) (h₀ : ℝ) (H : ComplexPartition.Field V)
    (x : V) (u : Spin 3) {ρ : ℝ} (hρ : 1 < ρ)
    (hz : shiftNonvanishing J h₀ ρ H x u) :
    ‖magnetization J H x u‖ ≤ 1 + 6 / (ρ - 1) := by
  let B : ComplexPartition.Field V := uniform h₀
  let D := H - B
  have nozero (w : ℂ) (hw : w ∈ ball (0 : ℂ) ρ) : partition J (affine B D w) ≠ 0 := by
    simpa only [addAt_zero] using hz w hw 0 (by simp)
  have hd : DifferentiableOn ℂ (fun w => magnetization J (affine B D w) x u) (ball 0 ρ) := by
    unfold magnetization
    simp only [insertion_eq_marked]
    exact (entire_marked_affine J B D _).differentiableOn.div
      (entire_partition_affine J B D).differentiableOn nozero
  obtain ⟨r, hr, heq⟩ := magnetization_uniform_real J h₀ x u
  have hbase : ‖magnetization J (affine B D 0) x u‖ ≤ 1 := by
    simpa only [affine_at_base, B, magnetization, heq, Complex.norm_real, Real.norm_eq_abs] using hr
  have hb := norm_magnetization_disk hρ hd hbase
    (fun w hw => magnetization_re_lower J (affine B D w) x u (hz w hw))
  simpa only [D, affine_at_target] using hb

private def siteFieldDirection (y : V) (v : Spin 3) : ComplexPartition.Field V := by
  classical
  exact fun k i => if k = y then (v.val i : ℂ) else 0

omit [Fintype V] in
private theorem affine_site (H : ComplexPartition.Field V) (y : V) (v : Spin 3) (z : ℂ) :
    affine H (siteFieldDirection y v) z = addAt H y v z := by
  classical
  funext k i
  by_cases h : k = y <;> simp [affine, siteFieldDirection, addAt, h]

private theorem evaluation_site (y : V) (v : Spin 3) :
    fieldEvaluation (siteFieldDirection y v) = complexMark (component y v) := by
  classical
  ext s
  simp only [fieldEvaluation, siteFieldDirection, ContinuousMap.coe_mk, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    complexMark, component, PiLp.inner_apply, Real.inner_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]

omit [Fintype V] in
private theorem component_product (x y : V) (u v : Spin 3) :
    complexMark (component x u) * complexMark (component y v) =
      complexMark (component x u * component y v) := by
  ext s
  simp [complexMark]

/-- A local field derivative inserts the connected pair, including at
coincident sites. All three terms use the same physical normalizer. -/
theorem hasDerivAt_magnetization_site (J : V → V → ℝ) (H : ComplexPartition.Field V) (x y : V)
    (u v : Spin 3) (hZ : partition J H ≠ 0) :
    HasDerivAt (fun z => magnetization J (addAt H y v z) x u)
      (marked J H (complexMark (component x u * component y v)) / partition J H -
        magnetization J H x u * magnetization J H y v) 0 := by
  have hn := hasDerivAt_marked_affine J H (siteFieldDirection y v) (complexMark (component x u)) 0
  simp only [affine_site, addAt_zero, evaluation_site, component_product] at hn
  have hd := hasDerivAt_partition_addAt J H y v 0
  rw [addAt_zero] at hd
  have hquot := hn.fun_div hd (show partition J (addAt H y v 0) ≠ 0 by simpa only [addAt_zero] using hZ)
  simp only [addAt_zero, insertion_eq_marked] at hquot
  simp only [magnetization, insertion_eq_marked]
  apply hquot.congr_deriv
  field_simp [hZ]

/-- Bounded finite-volume dot components obtained from the finite partition
function's zero-free region along two explicit field segments. -/
theorem directional_pair_bound (J : V → V → ℝ) (h₀ : ℝ) (H : ComplexPartition.Field V) (x y : V)
    (u v : Spin 3) {ρ δ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hx : ∀ z ∈ closedBall (0 : ℂ) δ, shiftNonvanishing J h₀ ρ (addAt H y v z) x u)
    (hy : shiftNonvanishing J h₀ ρ H y v) :
    ‖marked J H (complexMark (component x u * component y v)) / partition J H‖ ≤
      (1 + 6 / (ρ - 1)) / δ + (1 + 6 / (ρ - 1))^2 := by
  let M := 1 + 6 / (ρ - 1)
  have hone : (1 : ℂ) ∈ ball 0 ρ := mem_ball_zero_iff.mpr (by simpa using hρ)
  have hz (z : ℂ) (h : z ∈ closedBall (0 : ℂ) δ) : partition J (addAt H y v z) ≠ 0 := by
    simpa only [affine_at_target, addAt_zero] using hx z h 1 hone 0 (by simp)
  have hb (z : ℂ) (h : z ∈ closedBall (0 : ℂ) δ) :
      ‖magnetization J (addAt H y v z) x u‖ ≤ M :=
    norm_magnetization_of_nonvanishing J h₀ _ x u hρ (hx z h)
  have hzero : (0 : ℂ) ∈ closedBall 0 δ := mem_closedBall_self hδ.le
  have hZ : partition J H ≠ 0 := by simpa only [addAt_zero] using hz 0 hzero
  have hdiff : DifferentiableOn ℂ (fun z => magnetization J (addAt H y v z) x u)
      (closedBall 0 δ) := by
    unfold magnetization
    simp only [insertion_eq_marked, ← affine_site]
    exact (entire_marked_affine J H _ _).differentiableOn.div
      (entire_partition_affine J H _).differentiableOn (fun z h => by simpa only [affine_site] using hz z h)
  have hM : 0 ≤ M := add_nonneg zero_le_one (div_nonneg (by norm_num) (sub_nonneg.mpr hρ.le))
  exact norm_pair_from_response hδ hM (hdiff.diffContOnCl_ball Subset.rfl)
    (fun z h => hb z (sphere_subset_closedBall h)) (hasDerivAt_magnetization_site J H x y u v hZ)
    (by simpa only [addAt_zero] using hb 0 hzero) (norm_magnetization_of_nonvanishing J h₀ H y v hρ hy)

#print axioms directional_pair_bound
end IsingScaling.Rotor.HeisenbergField.ComplexBounds
