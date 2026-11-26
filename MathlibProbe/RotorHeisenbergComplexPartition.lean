import MathlibProbe.RotorHeisenbergVanishingField
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Single-site complex field response of the finite Heisenberg model

The partition function integrates the nearest-neighbour dot interaction (or any
finite coupling matrix) against the product of normalized surface measures on
the real unit sphere. Each site has an independent complex three-vector field.
Differentiation at one site inserts the corresponding physical spin component.
The volume may enter the prefactor of the exponential bound. Its exponential
type in the single-site field is at most one in every real unit direction.
-/

noncomputable section
open MeasureTheory Finset Filter
open scoped Topology InnerProductSpace
namespace IsingScaling.Rotor.HeisenbergField.ComplexPartition
open PressureSelection

variable {V : Type*} [Fintype V]

abbrev Field (V : Type*) := V → Fin 3 → ℂ
abbrev Config (V : Type*) := V → Spin 3
abbrev surfaceProduct (V : Type*) [Fintype V] : Measure (Config V) :=
  Measure.pi fun _ : V => SiteReflection.surfacePrior 3

private lemma energy_cont (J : V → V → ℝ) :
    Continuous (PressureSelection.energy (N := 3) J) := by
  unfold PressureSelection.energy
  exact (continuous_finsetSum _ (fun _ _ => continuous_finsetSum _ (fun _ _ =>
    continuous_const.mul (by fun_prop)))).div_const _

/-- Physical complex weight before normalization. Each directed copy of a bond
is included with coefficient one half in the finite dot energy. -/
def weight (J : V → V → ℝ) (H : Field V) : C(Config V, ℂ) where
  toFun s := Complex.exp ((PressureSelection.energy J s : ℝ) +
    ∑ x : V, ∑ i : Fin 3, H x i * ((s x).val i : ℂ))
  continuous_toFun := by
    apply Complex.continuous_exp.comp
    apply Continuous.add (Complex.continuous_ofReal.comp (energy_cont J))
    exact continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ =>
      continuous_const.mul (by fun_prop)

def partition (J : V → V → ℝ) (H : Field V) : ℂ :=
  ∫ s, weight J H s ∂surfaceProduct V

/-- Product-sphere Gibbs numerator of a continuous complex spin observable. -/
def marked (J : V → V → ℝ) (H : Field V) (F : C(Config V,ℂ)) : ℂ :=
  ∫ s, weight J H s * F s ∂surfaceProduct V

/-- Simultaneously vary the complex field at any finite collection of sites. -/
def affine (H D : Field V) (w : ℂ) : Field V := fun x i => H x i + w * D x i

def fieldEvaluation (D : Field V) : C(Config V,ℂ) where
  toFun s := ∑ x : V, ∑ i : Fin 3, D x i * ((s x).val i : ℂ)
  continuous_toFun := continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ =>
    continuous_const.mul (by fun_prop)

theorem weight_affine (J : V → V → ℝ) (H D : Field V) (w : ℂ) (s : Config V) :
    weight J (affine H D w) s = weight J H s * Complex.exp (w * fieldEvaluation D s) := by
  change Complex.exp _ = Complex.exp _ * Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  simp only [affine,fieldEvaluation,ContinuousMap.coe_mk,add_mul,Finset.sum_add_distrib,
    Finset.mul_sum,mul_assoc,add_assoc]

private theorem bounded_spin_laplace (B D : C(Config V,ℂ)) (w : ℂ) :
    HasDerivAt (fun t : ℂ => ∫ s, B s * Complex.exp (t * D s) ∂surfaceProduct V)
      (∫ s, B s * Complex.exp (w * D s) * D s ∂surfaceProduct V) w := by
  let F (t : ℂ) (s : Config V) := B s * Complex.exp (t * D s)
  let F' (t : ℂ) (s : Config V) := F t s * D s
  have hF (t : ℂ) : Continuous (F t) := by dsimp [F]; fun_prop
  have hF' (t : ℂ) : Continuous (F' t) := (hF t).mul D.continuous
  let C := ‖B‖ * Real.exp ((‖w‖ + 1) * ‖D‖) * ‖D‖
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceProduct V) (F := F) (F' := F') (bound := fun _ => C)
    (Metric.ball_mem_nhds w zero_lt_one) (Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    ((hF w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hF' w).aestronglyMeasurable _ (integrable_const C) _).2
  · refine ae_of_all _ fun s t ht => ?_
    have ht' : ‖t‖ ≤ ‖w‖ + 1 :=
      norm_le_norm_add_const_of_dist_le (show dist t w < 1 from ht).le
    have hExp : ‖Complex.exp (t * D s)‖ ≤ Real.exp ((‖w‖ + 1) * ‖D‖) :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by
        rw [norm_mul]
        exact mul_le_mul ht' (D.norm_coe_le_norm s) (norm_nonneg _) (by positivity)))
    change ‖B s * Complex.exp (t * D s) * D s‖ ≤ _
    simp only [norm_mul]
    exact mul_le_mul (mul_le_mul (B.norm_coe_le_norm s) hExp (norm_nonneg _) (norm_nonneg _))
      (D.norm_coe_le_norm s) (norm_nonneg _) (by positivity)
  · refine ae_of_all _ fun s t _ => ?_
    have hd := ((hasDerivAt_id t).mul_const (D s)).cexp.const_mul (B s)
    simpa only [F,F',id_eq,one_mul,mul_assoc] using hd

/-- Along any affine line of complex inhomogeneous fields, differentiating
inserts the physical directional sum, also in the presence of a complex mark. -/
theorem hasDerivAt_marked_affine (J : V → V → ℝ) (H D : Field V) (F : C(Config V,ℂ)) (w : ℂ) :
    HasDerivAt (fun t => marked J (affine H D t) F)
      (marked J (affine H D w) (F * fieldEvaluation D)) w := by
  let B := weight J H * F
  let A := fieldEvaluation D
  have hval (t : ℂ) : marked J (affine H D t) F =
      ∫ s, B s * Complex.exp (t * A s) ∂surfaceProduct V := by
    apply integral_congr_ae
    refine ae_of_all _ fun s => ?_
    simp only [weight_affine,B,A,ContinuousMap.mul_apply]
    ring
  have hder : marked J (affine H D w) (F * fieldEvaluation D) =
      ∫ s, B s * Complex.exp (w * A s) * A s ∂surfaceProduct V := by
    apply integral_congr_ae
    refine ae_of_all _ fun s => ?_
    simp only [weight_affine,B,A,ContinuousMap.mul_apply]
    ring
  simp_rw [hval]
  rw [hder]
  exact bounded_spin_laplace B A w

theorem entire_marked_affine (J : V → V → ℝ) (H D : Field V) (F : C(Config V,ℂ)) :
    Differentiable ℂ (fun t => marked J (affine H D t) F) :=
  fun w => (hasDerivAt_marked_affine J H D F w).differentiableAt

theorem entire_partition_affine (J : V → V → ℝ) (H D : Field V) :
    Differentiable ℂ (fun t => partition J (affine H D t)) := by
  simpa only [marked,partition,ContinuousMap.one_apply,mul_one] using
    entire_marked_affine J H D (1 : C(Config V,ℂ))

/-- A physical linear spin component in an arbitrary real unit direction. -/
def component (x : V) (u : Spin 3) : C(Config V, ℝ) where
  toFun s := ⟪u.val, (s x).val⟫_ℝ
  continuous_toFun := by fun_prop

omit [Fintype V] in
theorem norm_component_le (x : V) (u : Spin 3) (s : Config V) :
    ‖((component x u s : ℝ) : ℂ)‖ ≤ 1 := by
  simpa [component,norm_eq_of_mem_sphere] using norm_inner_le_norm (𝕜 := ℝ) u.val (s x).val

/-- Add the complex multiple of a real unit vector to the external field
at the single specified site. -/
def addAt (H : Field V) (x : V) (u : Spin 3) (w : ℂ) : Field V := by
  classical
  exact fun y i => H y i + if y = x then w * (u.val i : ℂ) else 0

omit [Fintype V] in
@[simp] theorem addAt_zero (H : Field V) (x : V) (u : Spin 3) : addAt H x u 0 = H := by
  classical
  funext y i
  simp [addAt]

theorem weight_addAt (J : V → V → ℝ) (H : Field V) (x : V) (u : Spin 3)
    (w : ℂ) (s : Config V) :
    weight J (addAt H x u w) s = weight J H s *
      Complex.exp (w * (component x u s : ℂ)) := by
  classical
  change Complex.exp _ = Complex.exp _ * Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  simp only [addAt,add_mul,Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  congr 1
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, component, ContinuousMap.coe_mk, PiLp.inner_apply, Real.inner_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

/-- Unnormalized one-spin insertion in the same perturbed Gibbs integral. -/
def insertion (J : V → V → ℝ) (H : Field V) (x : V) (u : Spin 3) : ℂ :=
  ∫ s, weight J H s * (component x u s : ℂ) ∂surfaceProduct V

private theorem exp_component_bound (x : V) (u : Spin 3) (w : ℂ) (s : Config V) :
    ‖Complex.exp (w * (component x u s : ℂ))‖ ≤ Real.exp ‖w‖ :=
  (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_component_le x u s)))

theorem norm_partition_addAt (J : V → V → ℝ) (H : Field V) (x : V) (u : Spin 3) (w : ℂ) :
    ‖partition J (addAt H x u w)‖ ≤ ‖weight J H‖ * Real.exp ‖w‖ := by
  have hb (s : Config V) :
      ‖weight J (addAt H x u w) s‖ ≤ ‖weight J H‖ * Real.exp ‖w‖ := by
    rw [weight_addAt,norm_mul]
    exact mul_le_mul ((weight J H).norm_coe_le_norm s) (exp_component_bound x u w s)
      (norm_nonneg _) (norm_nonneg _)
  simpa only [partition,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all (surfaceProduct V) hb)

theorem hasDerivAt_partition_addAt (J : V → V → ℝ) (H : Field V) (x : V) (u : Spin 3)
    (w : ℂ) : HasDerivAt (fun t => partition J (addAt H x u t))
      (insertion J (addAt H x u w) x u) w := by
  let D : C(Config V,ℂ) := ⟨fun s => (component x u s : ℂ),
    Complex.continuous_ofReal.comp (component x u).continuous⟩
  simpa only [partition,insertion,weight_addAt,D,ContinuousMap.coe_mk] using
    bounded_spin_laplace (weight J H) D w

theorem entire_partition_addAt (J : V → V → ℝ) (H : Field V) (x : V) (u : Spin 3) :
    Differentiable ℂ (fun w => partition J (addAt H x u w)) :=
  fun w => (hasDerivAt_partition_addAt J H x u w).differentiableAt

/-- The graph matrix of the physical free nearest-neighbour cube. -/
def cubeCoupling (L : ℕ) (β : ℝ) (x y : BoxSite L) : ℝ :=
  if latticeDistance x y = 1 then β else 0

theorem cube_energy (L : ℕ) (β : ℝ) (s : Config (BoxSite L)) :
    PressureSelection.energy (cubeCoupling L β) s = β * SiteReflection.energy s := by
  change ((∑ x : BoxSite L, ∑ y : BoxSite L, (if latticeDistance x y = 1 then β else 0) *
      ⟪(s x).val,(s y).val⟫_ℝ) / 2) =
    β * ((∑ x : BoxSite L, ∑ y : BoxSite L, if latticeDistance x y = 1 then
      ⟪(s x).val,(s y).val⟫_ℝ else 0)/2)
  rw [← mul_div_assoc]
  simp only [Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]

def uniform (h : ℂ) : Field V := fun _ i => if i = 0 then h else 0

omit [Fintype V] in
theorem affine_uniform (z : ℂ) : affine (uniform (V := V) 0) (uniform 1) z = uniform z := by
  funext x i
  by_cases hi : i = 0 <;> simp [affine,uniform,hi]

theorem entire_marked_uniform (J : V → V → ℝ) (F : C(Config V,ℂ)) :
    Differentiable ℂ (fun z => marked J (uniform z) F) := by
  simpa only [affine_uniform] using entire_marked_affine J (uniform 0) (uniform 1) F

theorem entire_partition_uniform (J : V → V → ℝ) :
    Differentiable ℂ (fun z => partition J (uniform z)) := by
  simpa only [affine_uniform] using entire_partition_affine J (uniform 0) (uniform 1)

theorem weight_uniform_real (J : V → V → ℝ) (h : ℝ) (s : Config V) :
    weight J (uniform (h : ℂ)) s =
      ((Real.exp ((∑ x : V, siteField h (s x)) + PressureSelection.energy J s) : ℝ) : ℂ) := by
  change Complex.exp _ = _
  rw [Complex.ofReal_exp]
  congr 1
  simp [uniform,siteField,ite_mul,add_comm]

theorem cube_weight_uniform (L : ℕ) (β h : ℝ) (s : Config (BoxSite L)) :
    weight (cubeCoupling L β) (uniform h) s =
      ((Real.exp ((∑ x : BoxSite L, siteField h (s x)) + β * SiteReflection.energy s) : ℝ) : ℂ) := by
  rw [weight_uniform_real,cube_energy]

def complexMark (F : C(Config V, ℝ)) : C(Config V, ℂ) :=
  ⟨fun s => (F s : ℂ), Complex.continuous_ofReal.comp F.continuous⟩

theorem partition_uniform_real_pos (J : V → V → ℝ) (h : ℝ) :
    0 < (partition J (uniform (h : ℂ))).re := by
  unfold partition
  simp_rw [weight_uniform_real]
  rw [integral_complex_ofReal]
  apply integral_exp_pos
  have hf : Continuous (fun s : Config V => ∑ x : V, siteField h (s x)) :=
    continuous_finsetSum _ fun x _ => by unfold siteField; fun_prop
  exact ((hf.add (energy_cont J)).rexp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Real-field Gibbs expectation for every finite graph, with the original
single-site priors and the same finite interaction matrix as the partition. -/
theorem real_uniform_ratio (J : V → V → ℝ) (h : ℝ) (F : C(Config V,ℝ)) :
    Complex.ofReal (∫ s, F s ∂((Measure.pi fun _ : V => fieldPrior h).tilted (PressureSelection.energy J))) =
      marked J (uniform h) (complexMark F) / partition J (uniform h) := by
  rw [fieldPrior_product]
  have hc : Continuous (fun s : Config V => ∑ x : V, siteField h (s x)) :=
    continuous_finsetSum _ fun x _ => by unfold siteField; fun_prop
  rw [tilted_tilted (hc.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_tilted]
  unfold marked partition
  simp_rw [weight_uniform_real, complexMark, ContinuousMap.coe_mk, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal,integral_complex_ofReal,← Complex.ofReal_div]
  congr 1
  simp only [Pi.add_apply,smul_eq_mul,div_mul_eq_mul_div,integral_div]

theorem insertion_eq_marked (J : V → V → ℝ) (H : Field V) (x : V) (u : Spin 3) :
    insertion J H x u = marked J H (complexMark (component x u)) := rfl

/-- All finite real-field longitudinal or tilted-axis magnetizations are
real numbers in the physical interval, independently of the graph. -/
theorem magnetization_uniform_real (J : V → V → ℝ) (h : ℝ) (x : V) (u : Spin 3) :
    ∃ a : ℝ, |a| ≤ 1 ∧ insertion J (uniform h) x u / partition J (uniform h) = (a : ℂ) := by
  let θ := Measure.pi fun _ : V => fieldPrior h
  let μ := θ.tilted (PressureSelection.energy J)
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    ((energy_cont J).rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  refine ⟨∫ s, component x u s ∂μ, ?_, (real_uniform_ratio J h (component x u)).symm⟩
  have hb (s : Config V) : ‖component x u s‖ ≤ 1 := by
    simpa using norm_component_le x u s
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all μ hb)

/-- Normalization at a real field agrees with the original finite-volume
Gibbs probability, for every continuous measurement on the extended spins. -/
theorem cubeLaw_eq_complex_moment (L : ℕ) (β h : ℝ) (F : C(SpinField 3,ℝ)) :
    Complex.ofReal (∫ s, F s ∂(cubeLaw β h L : Measure _)) =
      (∫ s, weight (cubeCoupling L β) (uniform h) s * (F (extendCube L s) : ℂ)
        ∂surfaceProduct (BoxSite L)) / partition (cubeCoupling L β) (uniform h) := by
  rw [cubeLaw_integral]
  have he : PressureSelection.energy (N := 3) (cubeCoupling L β) =
      fun s => β * SiteReflection.energy s := funext (cube_energy L β)
  simpa only [he,marked,complexMark,ContinuousMap.coe_mk,ContinuousMap.comp_apply] using
    real_uniform_ratio (cubeCoupling L β) h (F.comp (extendCube L))

/-- The actual nearest-neighbour partition function at a real uniform field
is the integral of a strictly positive continuous density. -/
theorem cube_partition_uniform_pos (L : ℕ) (β h : ℝ) :
    0 < (partition (cubeCoupling L β) (uniform h)).re :=
  partition_uniform_real_pos (cubeCoupling L β) h

/-- At a real field, the logarithmic derivative in every real unit
direction is exactly the physical one-site magnetization of the free cube. -/
theorem cube_logDerivative_eq_magnetization (L : ℕ) (β h : ℝ) (x : BoxSite L) (u : Spin 3) :
    deriv (fun w => partition (cubeCoupling L β) (addAt (uniform h) x u w)) 0 /
      partition (cubeCoupling L β) (uniform h) =
      Complex.ofReal (∫ s : SpinField 3, ⟪u.val, (s x.val).val⟫_ℝ ∂(cubeLaw β h L : Measure _)) := by
  rw [(hasDerivAt_partition_addAt _ _ _ _ _).deriv, addAt_zero]
  let F : C(SpinField 3, ℝ) := ⟨fun s => ⟪u.val, (s x.val).val⟫_ℝ, by fun_prop⟩
  simpa [F,insertion,component,extendCube,x.property] using (cubeLaw_eq_complex_moment L β h F).symm

end IsingScaling.Rotor.HeisenbergField.ComplexPartition
