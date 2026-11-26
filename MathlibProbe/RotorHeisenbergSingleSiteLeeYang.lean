import MathlibProbe.RotorHeisenbergComplexPartition
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.ComplexMGF

/-! # The original Heisenberg single-spin Laplace transform

Write cₙ for the surface integral of S₀^(2n). Rotational invariance gives
the polynomial identity E[(S₀+tSⱼ)^(2n)] = cₙ(1+t²)^n for j = 1,2.
Comparing coefficients of t² and integrating ΣSⱼ² = 1 proves
(2n+3)cₙ₊₁ = (2n+1)cₙ. With c₀=1 and odd moments zero, summing the
exponential series yields the axial transform sinh(z)/z.

For real Euclidean vectors a,b the integrated even moment of (a+w b)·S
is a polynomial in complex w. At real w, it equals cₙ times
the n-th power of the algebraic field square. Equality of polynomials
extends the identity to all w. Consequently the physical partition is
the axial partition at either square root t of the complex field square.

For w=i a purely imaginary root would require a·b=0 and ‖a‖≤‖b‖.
When b₁²+b₂²<a₀², the orthogonality identity and Cauchy–Schwarz imply
b₀²≤a₁²+a₂² and hence ‖b‖<‖a‖. This proves the three-component
single-site Lee–Yang cone, including every local field with
Re H₀>‖H₁‖+‖H₂‖. Product integration gives the uncoupled finite-volume
statement for different complex fields at every site.

The Laplace transform of (1+S₀)/2 consequently equals that of Lebesgue
measure on the unit interval. Uniqueness of characteristic functions
identifies its physical law. Its moments are 1/(m+1); the mixed Bernstein
weights follow recursively from down = 1-up.
-/

noncomputable section
open MeasureTheory Finset Filter
open scoped Topology InnerProductSpace Polynomial
namespace IsingScaling.Rotor.HeisenbergField.SingleSiteLeeYang

private abbrev θ := SiteReflection.surfacePrior 3
private abbrev Ambient := EuclideanSpace ℝ (Fin 3)

private theorem ci {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Spin 3 → E} (h : Continuous F) : Integrable F θ :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def axialMoment (n : ℕ) : ℝ := ∫ s : Spin 3, (s.val 0)^(2*n) ∂θ

private theorem unit_moment (n : ℕ) (u : Spin 3) :
    (∫ s : Spin 3, ⟪u.val,s.val⟫_ℝ^(2*n) ∂θ) = axialMoment n := by
  let O := (Submodule.span ℝ ({firstSpin.val-u.val} : Set Ambient))ᗮ.reflection
  have hO : O firstSpin.val = u.val := Submodule.reflection_sub (by simp [norm_eq_of_mem_sphere])
  rw [← (SiteReflection.SphereSign.sphereMap_preserving O).integral_comp'
    (fun s : Spin 3 => ⟪u.val,s.val⟫_ℝ^(2*n))]
  apply integral_congr_ae
  filter_upwards with s
  simp [SiteReflection.SphereSign.sphereMap_val, ← hO, O.inner_map_map,
    firstSpin, EuclideanSpace.inner_single_left]

private theorem direction_moment (n : ℕ) (v : Ambient) (hv : v ≠ 0) :
    (∫ s : Spin 3, ⟪v,s.val⟫_ℝ^(2*n) ∂θ) = ‖v‖^(2*n) * axialMoment n := by
  have hn := norm_ne_zero_iff.mpr hv
  let u : Spin 3 := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]⟩
  have hvu : ‖v‖ • u.val = v := by simp [u, smul_smul, hn]
  have H (s : Spin 3) :
      ⟪v,s.val⟫_ℝ^(2*n) = ‖v‖^(2*n) * ⟪u.val,s.val⟫_ℝ^(2*n) := by
    conv_lhs => rw [← hvu, real_inner_smul_left, mul_pow]
  simp_rw [H]
  rw [integral_const_mul, unit_moment]

private theorem two_axis_moment (n : ℕ) (j : Fin 3) (hj : j ≠ 0) (t : ℝ) :
    (∫ s : Spin 3, (s.val 0 + t * s.val j)^(2*n) ∂θ) = (1+t^2)^n * axialMoment n := by
  let v : Ambient := EuclideanSpace.single 0 1 + EuclideanSpace.single j t
  have hn : ‖v‖^2 = 1+t^2 := by
    simp [v, norm_add_sq_real, EuclideanSpace.inner_single_left, Ne.symm hj, sq_abs]
  have hv : v ≠ 0 := by rintro h; rw [h] at hn; simp at hn; nlinarith [sq_nonneg t]
  have h := direction_moment n v hv
  rw [pow_mul, hn] at h
  simpa [v, inner_add_left, EuclideanSpace.inner_single_left] using h

private def mixed (n k : ℕ) (j : Fin 3) : ℝ :=
  ∫ s : Spin 3, (s.val j)^k * (s.val 0)^(n-k) ∂θ

private def momentPoly (n : ℕ) (j : Fin 3) : ℝ[X] :=
  ∑ k ∈ range (n+1), Polynomial.monomial k ((n.choose k : ℝ) * mixed n k j)

private theorem eval_momentPoly (n : ℕ) (j : Fin 3) (t : ℝ) :
    (momentPoly n j).eval t = ∫ s : Spin 3, (s.val 0+t*s.val j)^n ∂θ := by
  have expand (s : Spin 3) : (s.val 0+t*s.val j)^n =
      ∑ k ∈ range (n+1), ((n.choose k : ℝ)*t^k) * ((s.val j)^k * (s.val 0)^(n-k)) := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun k _ => ci (by fun_prop))]
  simp [momentPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial, integral_const_mul,
    mixed, mul_assoc, mul_comm]

private theorem square_coeff (k : ℕ) : (((1:ℝ[X])+Polynomial.X^2)^k).coeff 2 = (k : ℝ) := by
  induction k with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, ih]
    have h : ((((1:ℝ[X])+Polynomial.X^2)^k)*Polynomial.X^2).coeff 2 =
        (((1:ℝ[X])+Polynomial.X^2)^k).coeff 0 := Polynomial.coeff_mul_X_pow _ 2 0
    rw [h, Polynomial.coeff_zero_eq_eval_zero]
    simp

private theorem mixed_second (n : ℕ) (j : Fin 3) (hj : j ≠ 0) :
    (((2*n+2).choose 2 : ℕ) : ℝ) *
      (∫ s : Spin 3, (s.val j)^2*(s.val 0)^(2*n) ∂θ) =
      (n+1 : ℝ) * axialMoment (n+1) := by
  let N := 2*(n+1)
  have evalEq : momentPoly N j = Polynomial.C (axialMoment (n+1)) *
      ((1 : ℝ[X]) + Polynomial.X^2)^(n+1) := by
    apply Polynomial.funext
    intro t
    rw [eval_momentPoly, two_axis_moment (n+1) j hj t]
    simp [mul_comm]
  have h := congrArg (fun p : ℝ[X] => p.coeff 2) evalEq
  have hN : N = 2*n+2 := by dsimp [N]; omega
  have hmem : 2 < N+1 := by omega
  simpa [momentPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_C_mul,
    hmem, square_coeff, mixed, hN, Nat.cast_succ, mul_comm] using h

private theorem moment_rec (n : ℕ) :
    (2*(n:ℝ)+3) * axialMoment (n+1) = (2*n+1) * axialMoment n := by
  let J (j : Fin 3) := ∫ s : Spin 3, (s.val j)^2*(s.val 0)^(2*n) ∂θ
  have h1 : J 0 + J 1 + J 2 = axialMoment n := by
    have hI (j : Fin 3) : Integrable (fun s : Spin 3 => (s.val j)^2*(s.val 0)^(2*n)) θ :=
      ci (by fun_prop)
    have hi01 : Integrable (fun s : Spin 3 =>
        (s.val 0)^2*(s.val 0)^(2*n) + (s.val 1)^2*(s.val 0)^(2*n)) θ := (hI 0).add (hI 1)
    dsimp [J, axialMoment]
    rw [← integral_add (hI 0) (hI 1), ← integral_add hi01 (hI 2)]
    apply integral_congr_ae
    filter_upwards with s
    have hs := EuclideanSpace.real_norm_sq_eq s.val
    rw [mem_sphere_zero_iff_norm.mp s.property, Fin.sum_univ_three] at hs
    calc
      _ = ((s.val 0)^2+(s.val 1)^2+(s.val 2)^2)*(s.val 0)^(2*n) := by ring
      _ = _ := by rw [← hs]; ring
  have h0 : J 0 = axialMoment (n+1) := by
    dsimp [J, axialMoment]
    apply integral_congr_ae
    filter_upwards with s
    rw [← pow_add]
    congr 1
    omega
  have hj (j : Fin 3) (h : j ≠ 0) := mixed_second n j h
  have h2 := hj 1 (by decide)
  have h3 := hj 2 (by decide)
  change ((2*n+2).choose 2 : ℝ) * J 1 = _ at h2
  change ((2*n+2).choose 2 : ℝ) * J 2 = _ at h3
  rw [Nat.cast_choose_two] at h2 h3
  push_cast at h2 h3
  rw [h0] at h1
  have : (n:ℝ)+1 ≠ 0 := by positivity
  apply mul_left_cancel₀ this
  linear_combination (2*(n:ℝ)+1)*(n+1)*h1 - h2 - h3

/-- All even axial moments of the actual normalized sphere measure. -/
theorem axial_moment_eq (n : ℕ) : axialMoment n = 1/(2*(n:ℝ)+1) := by
  induction n with
  | zero => simp [axialMoment, measureReal_def]
  | succ n ih =>
    have h := moment_rec n
    rw [ih] at h
    push_cast
    have ha : (2*(n:ℝ)+1) ≠ 0 := by positivity
    field_simp [ha] at h ⊢
    linarith

/-- Laplace transform in the first spin direction with the normalized physical area law. -/
def axialPartition (z : ℂ) : ℂ :=
  ∫ s : Spin 3, Complex.exp (z * (s.val 0 : ℂ)) ∂θ

theorem axialPartition_zero : axialPartition 0 = 1 := by simp [axialPartition]

theorem axialPartition_analytic (z : ℂ) : AnalyticAt ℂ axialPartition z := by
  have H : ProbabilityTheory.integrableExpSet (fun s : Spin 3 => s.val 0) θ = Set.univ :=
    Set.eq_univ_of_forall fun t => ci (F := fun s : Spin 3 => Real.exp (t * s.val 0)) (by fun_prop)
  apply ProbabilityTheory.analyticAt_complexMGF (X := fun s : Spin 3 => s.val 0) (μ := θ)
  simp [H]

private theorem axialPartition_even (z : ℂ) : axialPartition (-z) = axialPartition z := by
  unfold axialPartition
  rw [← (SiteReflection.SphereSign.flipCoord_preserving (N := 3) 0).integral_comp'
    (fun s : Spin 3 => Complex.exp (z * (s.val 0 : ℂ)))]
  simp [SiteReflection.SphereSign.flipCoord_apply]

private theorem integral_cosh (z : ℂ) :
    (∫ s : Spin 3, Complex.cosh (z * (s.val 0 : ℂ)) ∂θ) = axialPartition z := by
  have hi (w : ℂ) : Integrable (fun s : Spin 3 => Complex.exp (w*(s.val 0 : ℂ))) θ :=
    ci (by fun_prop)
  simp only [Complex.cosh, ← neg_mul, integral_div, integral_add (hi z) (hi (-z))]
  change (axialPartition z + axialPartition (-z)) / 2 = _
  rw [axialPartition_even]
  ring

private theorem moment_series (z : ℂ) :
    HasSum (fun n : ℕ => (z^(2*n) / ((2*n).factorial : ℂ)) *
      (axialMoment n : ℂ)) (axialPartition z) := by
  let F (n : ℕ) (s : Spin 3) := (z*(s.val 0 : ℂ))^(2*n) / ((2*n).factorial : ℂ)
  let B (n : ℕ) := ‖z‖^(2*n) / ((2*n).factorial : ℝ)
  have major (n : ℕ) (s : Spin 3) : ‖F n s‖ ≤ B n := by
    have h : |s.val 0| ≤ 1 := by simpa [siteField] using abs_siteField_le 1 s
    dsimp [F, B]
    simp only [norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    gcongr
    exact mul_le_of_le_one_right (norm_nonneg _) h
  have hs := hasSum_integral_of_dominated_convergence (μ := θ) (F := F)
    (f := fun s : Spin 3 => Complex.cosh (z*(s.val 0 : ℂ))) (fun n _ => B n)
    (fun n => (ci (F := F n) (by unfold F; fun_prop)).aestronglyMeasurable)
    (fun n => Eventually.of_forall (major n))
    (Eventually.of_forall fun _ => (Real.hasSum_cosh ‖z‖).summable)
    (integrable_const _) (Eventually.of_forall fun s => Complex.hasSum_cosh (z*(s.val 0 : ℂ)))
  rw [integral_cosh] at hs
  apply hs.congr_fun
  intro n
  have hh (s : Spin 3) : F n s = (z^(2*n) / ((2*n).factorial : ℂ)) *
      (((s.val 0)^(2*n) : ℝ) : ℂ) := by
    simp [F, mul_pow, div_mul_eq_mul_div]
  simp only [hh, integral_const_mul, integral_complex_ofReal, axialMoment]

/-- The physical sphere integral satisfies the removable-singularity formula on all of ℂ. -/
theorem mul_axialPartition (z : ℂ) : z * axialPartition z = Complex.sinh z := by
  have hs := (moment_series z).mul_left z
  refine HasSum.unique ?_ (Complex.hasSum_sinh z)
  apply hs.congr_fun
  intro n
  rw [axial_moment_eq, Nat.factorial_succ, pow_succ]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem axialPartition_eq {z : ℂ} (hz : z ≠ 0) : axialPartition z = Complex.sinh z / z := by
  apply (eq_div_iff hz).2
  simpa [mul_comm] using mul_axialPartition z

/-- Single-site Lee–Yang nonvanishing for the original Heisenberg sphere law. -/
theorem axialPartition_ne_zero {z : ℂ} (hz : 0 < z.re) : axialPartition z ≠ 0 := by
  intro h
  have hs := mul_axialPartition z
  rw [h, mul_zero, Complex.sinh] at hs
  have he : Complex.exp z = Complex.exp (-z) := sub_eq_zero.mp
    ((div_eq_zero_iff.mp hs.symm).resolve_right (by norm_num))
  have hnorm := congrArg norm he
  simp [Complex.norm_exp] at hnorm
  linarith

/-- For any choice of real unit field direction at each site and complex field
strength, the zero-coupling physical product-area integral factors exactly. -/
theorem decoupled_partition_eq {V : Type*} [Fintype V] (u : V → Spin 3) (z : V → ℂ) :
    (∫ s : V → Spin 3, Complex.exp (∑ x, z x * (⟪(u x).val,(s x).val⟫_ℝ : ℂ))
      ∂Measure.pi (fun _ => θ)) = ∏ x, axialPartition (z x) := by
  classical
  simp_rw [Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun x (s : Spin 3) =>
    Complex.exp (z x * (⟪(u x).val,s.val⟫_ℝ : ℂ)))]
  apply Finset.prod_congr rfl
  intro x _
  let O := (Submodule.span ℝ ({firstSpin.val-(u x).val} : Set Ambient))ᗮ.reflection
  have hO : O firstSpin.val = (u x).val := Submodule.reflection_sub (by simp [norm_eq_of_mem_sphere])
  rw [← (SiteReflection.SphereSign.sphereMap_preserving O).integral_comp'
    (fun s : Spin 3 => Complex.exp (z x * (⟪(u x).val,s.val⟫_ℝ : ℂ)))]
  simp [SiteReflection.SphereSign.sphereMap_val, ← hO, O.inner_map_map,
    firstSpin, EuclideanSpace.inner_single_left, axialPartition]

theorem decoupled_partition_ne_zero {V : Type*} [Fintype V] (u : V → Spin 3) (z : V → ℂ)
    (h : ∀ x, 0 < (z x).re) :
    (∫ s : V → Spin 3, Complex.exp (∑ x, z x * (⟪(u x).val,(s x).val⟫_ℝ : ℂ))
      ∂Measure.pi (fun _ => θ)) ≠ 0 := by
  rw [decoupled_partition_eq]
  exact Finset.prod_ne_zero_iff.mpr fun x _ => axialPartition_ne_zero (h x)

/-- Real and imaginary vector field components enter the bilinear scalar product. -/
def vectorField (a b : EuclideanSpace ℝ (Fin 3)) (w : ℂ) (s : Spin 3) : ℂ :=
  (⟪a,s.val⟫_ℝ : ℂ) + w * (⟪b,s.val⟫_ℝ : ℂ)

/-- Algebraic square of the complex vector field a + w b. -/
def quadraticField (a b : EuclideanSpace ℝ (Fin 3)) (w : ℂ) : ℂ :=
  (‖a‖ : ℂ)^2 + (2 * (⟪a,b⟫_ℝ : ℂ)) * w + (‖b‖ : ℂ)^2 * w^2

private theorem all_direction_moment (n : ℕ) (v : Ambient) :
    (∫ s : Spin 3, ⟪v,s.val⟫_ℝ^(2*n) ∂θ) = ‖v‖^(2*n) * axialMoment n := by
  by_cases hv : v = 0
  · subst v
    cases n <;> simp [axialMoment, Nat.mul_succ]
  · exact direction_moment n v hv

private def dirPoly (N : ℕ) (a b : Ambient) : ℂ[X] :=
  ∑ k ∈ range (N+1), Polynomial.monomial k
    ((N.choose k : ℂ) * ∫ s : Spin 3, (⟪b,s.val⟫_ℝ : ℂ)^k*(⟪a,s.val⟫_ℝ : ℂ)^(N-k) ∂θ)

private theorem dirPoly_eval (N : ℕ) (a b : Ambient) (w : ℂ) :
    (dirPoly N a b).eval w = ∫ s : Spin 3, (vectorField a b w s)^N ∂θ := by
  have expand (s : Spin 3) : (vectorField a b w s)^N =
      ∑ k ∈ range (N+1), ((N.choose k : ℂ)*w^k) *
        ((⟪b,s.val⟫_ℝ : ℂ)^k*(⟪a,s.val⟫_ℝ : ℂ)^(N-k)) := by
    rw [vectorField, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun k _ => ci (by fun_prop))]
  simp [dirPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial, integral_const_mul,
    mul_assoc, mul_comm]

private theorem quad_real (a b : Ambient) (r : ℝ) :
    quadraticField a b (r : ℂ) = ((‖a+r • b‖^2 : ℝ) : ℂ) := by
  simp [quadraticField,norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow,sq_abs]
  ring

/-- All even moments of an arbitrary complex three-component field depend
only on its algebraic square. Real orthogonal invariance suffices: the
integrated degree-2n polynomials agree at every real value of w. -/
theorem vector_even_moment (n : ℕ) (a b : EuclideanSpace ℝ (Fin 3)) (w : ℂ) :
    (∫ s : Spin 3, (vectorField a b w s)^(2*n) ∂θ) =
      (quadraticField a b w)^n * (axialMoment n : ℂ) := by
  let Q : ℂ[X] := Polynomial.C ((‖a‖:ℂ)^2) +
    Polynomial.C (2*(⟪a,b⟫_ℝ : ℂ))*Polynomial.X + Polynomial.C ((‖b‖:ℂ)^2)*Polynomial.X^2
  have hQ (z : ℂ) : Q.eval z = quadraticField a b z := by simp [Q,quadraticField]
  have eqpoly : dirPoly (2*n) a b = Q^n * Polynomial.C (axialMoment n : ℂ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro _ ⟨r,rfl⟩
    change (dirPoly (2*n) a b).eval (r : ℂ) = _
    rw [dirPoly_eval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, hQ, quad_real]
    have e (s : Spin 3) : (vectorField a b (r : ℂ) s)^(2*n) =
        ((⟪a+r • b,s.val⟫_ℝ^(2*n) : ℝ) : ℂ) := by
      simp [vectorField, inner_add_left, real_inner_smul_left]
    simp only [e]
    rw [integral_complex_ofReal, all_direction_moment]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, pow_mul]
  rw [← dirPoly_eval, eqpoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, hQ]

private theorem complex_cosh_series (F : C(Spin 3,ℂ)) :
    HasSum (fun n : ℕ => (∫ s : Spin 3, (F s)^(2*n) ∂θ) / ((2*n).factorial : ℂ))
      (∫ s, Complex.cosh (F s) ∂θ) := by
  let B (n : ℕ) := ‖F‖^(2*n) / ((2*n).factorial : ℝ)
  let G (n : ℕ) (s : Spin 3) := (F s)^(2*n) / ((2*n).factorial : ℂ)
  have major (n : ℕ) (s : Spin 3) : ‖G n s‖ ≤ B n := by
    simp only [G, B, norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    exact F.norm_coe_le_norm s
  have hs := hasSum_integral_of_dominated_convergence (μ := θ) (F := G)
    (f := fun s : Spin 3 => Complex.cosh (F s)) (fun n _ => B n)
    (fun n => (ci (F := G n) (by unfold G; fun_prop)).aestronglyMeasurable)
    (fun n => Eventually.of_forall (major n))
    (Eventually.of_forall fun _ => (Real.hasSum_cosh ‖F‖).summable)
    (integrable_const _) (Eventually.of_forall fun s => Complex.hasSum_cosh (F s))
  simpa only [G, integral_div] using hs

/-- Physical moment generating function of a + w b equals the axial
partition at either square root of the algebraic field square. -/
theorem vector_partition_eq_axial (a b : EuclideanSpace ℝ (Fin 3)) (w t : ℂ)
    (ht : t^2 = quadraticField a b w) :
    (∫ s : Spin 3, Complex.exp (vectorField a b w s) ∂θ) = axialPartition t := by
  let F : C(Spin 3,ℂ) := ⟨vectorField a b w, by unfold vectorField; fun_prop⟩
  let O := (LinearIsometryEquiv.neg ℝ : Ambient ≃ₗᵢ[ℝ] Ambient)
  have odd (s : Spin 3) : F (SiteReflection.SphereSign.sphereMap O s) = -F s := by
    simp [F, O, vectorField, neg_add_rev, add_comm]
  have reflect : (∫ s : Spin 3, Complex.exp (-(F s)) ∂θ) =
      ∫ s : Spin 3, Complex.exp (F s) ∂θ := by
    rw [← (SiteReflection.SphereSign.sphereMap_preserving O).integral_comp'
      (fun s => Complex.exp (F s))]
    simp [odd]
  have project : (∫ s : Spin 3, Complex.cosh (F s) ∂θ) = ∫ s : Spin 3, Complex.exp (F s) ∂θ := by
    have hi : Integrable (fun s : Spin 3 => Complex.exp (F s)) θ := ci (by fun_prop)
    have hn : Integrable (fun s : Spin 3 => Complex.exp (-(F s))) θ := ci (by fun_prop)
    simp only [Complex.cosh, integral_div, integral_add hi hn, reflect]
    ring
  change (∫ s : Spin 3, Complex.exp (F s) ∂θ) = _
  rw [← project]
  refine (complex_cosh_series F).unique ?_
  apply (moment_series t).congr_fun
  intro n
  change (∫ s : Spin 3, (vectorField a b w s)^(2*n) ∂θ) / _ = _
  rw [vector_even_moment, ← ht, ← pow_mul]
  ring

private theorem norm_sq_gt_of_perp (a b : Ambient) (hab : ⟪a,b⟫_ℝ = 0)
    (ht : (b 1)^2 + (b 2)^2 < (a 0)^2) : ‖b‖^2 < ‖a‖^2 := by
  have hdot : a 0 * b 0 + a 1 * b 1 + a 2 * b 2 = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_three, mul_comm, add_assoc] using hab
  have eq : a 0 * b 0 = -(a 1 * b 1+a 2 * b 2) := by linarith
  have heq := congrArg (fun r : ℝ => r^2) eq
  dsimp at heq
  have hu : (a 0)^2 * (b 0)^2 ≤ ((a 1)^2+(a 2)^2) * ((b 1)^2+(b 2)^2) := by
    nlinarith only [heq,sq_nonneg (a 1*b 2-a 2*b 1)]
  have ha := add_nonneg (sq_nonneg (a 1)) (sq_nonneg (a 2))
  have h0 := lt_of_le_of_lt (add_nonneg (sq_nonneg (b 1)) (sq_nonneg (b 2))) ht
  have hb : (b 0)^2 ≤ (a 1)^2 + (a 2)^2 := by
    apply (mul_le_mul_iff_right₀ h0).mp
    exact hu.trans ((mul_le_mul_of_nonneg_left ht.le ha).trans_eq (mul_comm _ _))
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  linarith

/-- Single-spin Lee–Yang cone on the actual three-component complex field.
For H = a + i b the usual condition Re H₀ > |H₁| + |H₂| implies this
strict quadratic transverse condition. -/
theorem vector_partition_ne_zero (a b : EuclideanSpace ℝ (Fin 3))
    (h : (b 1)^2 + (b 2)^2 < (a 0)^2) :
    (∫ s : Spin 3, Complex.exp (vectorField a b Complex.I s) ∂θ) ≠ 0 := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq (quadraticField a b Complex.I) (n := 2) (by decide)
  have htre : t.re ≠ 0 := by
    intro hr
    have hi := congrArg Complex.im ht
    have hx := congrArg Complex.re ht
    simp [quadraticField, pow_two, Complex.mul_im, Complex.mul_re, hr] at hi hx
    have ortho : ⟪a,b⟫_ℝ = 0 := by linarith
    have hg := norm_sq_gt_of_perp a b ortho h
    nlinarith [sq_nonneg t.im]
  rw [vector_partition_eq_axial a b Complex.I t ht]
  rcases lt_or_gt_of_ne htre with hneg | hpos
  · rw [← axialPartition_even t]
    exact axialPartition_ne_zero (by simp; linarith)
  · exact axialPartition_ne_zero hpos

/-- Usual complex field cone, in the same three-coordinate convention as the
product-sphere partition function. -/
theorem single_site_cone (H : Fin 3 → ℂ) (h : ‖H 1‖ + ‖H 2‖ < (H 0).re) :
    (∫ s : Spin 3, Complex.exp (∑ j, H j * (s.val j : ℂ)) ∂θ) ≠ 0 := by
  let a : Ambient := WithLp.toLp 2 fun j => (H j).re
  let b : Ambient := WithLp.toLp 2 fun j => (H j).im
  have nn := add_nonneg (norm_nonneg (H 1)) (norm_nonneg (H 2))
  have bound (j : Fin 3) : (H j).im ^ 2 ≤ ‖H j‖^2 := by
    nlinarith only [Complex.sq_norm_sub_sq_im (H j), sq_nonneg (H j).re]
  have ht : (b 1)^2 + (b 2)^2 < (a 0)^2 := by
    change (H 1).im ^ 2 + (H 2).im ^ 2 < (H 0).re ^ 2
    calc
      _ ≤ ‖H 1‖^2+‖H 2‖^2 := add_le_add (bound 1) (bound 2)
      _ ≤ (‖H 1‖+‖H 2‖)^2 := by nlinarith [mul_nonneg (norm_nonneg (H 1)) (norm_nonneg (H 2))]
      _ < _ := (sq_lt_sq₀ nn (le_trans nn h.le)).mpr h
  have representation (s : Spin 3) :
      vectorField a b Complex.I s = ∑ j, H j * (s.val j : ℂ) := by
    apply Complex.ext <;>
      simp [vectorField,a,b,Fin.sum_univ_three,PiLp.inner_apply,Complex.mul_re,Complex.mul_im] <;> ring
  simpa only [representation] using vector_partition_ne_zero a b ht

/-- Arbitrary spatially inhomogeneous vector fields on an uncoupled finite
Heisenberg graph. -/
theorem decoupled_vector_cone {V : Type*} [Fintype V] (H : V → Fin 3 → ℂ)
    (h : ∀ x, ‖H x 1‖ + ‖H x 2‖ < (H x 0).re) :
    (∫ s : V → Spin 3, Complex.exp (∑ x, ∑ j, H x j * ((s x).val j : ℂ))
      ∂Measure.pi (fun _ => θ)) ≠ 0 := by
  classical
  have e (s : V → Spin 3) : Complex.exp (∑ x, ∑ j, H x j * ((s x).val j : ℂ)) =
      ∏ x, Complex.exp (∑ j, H x j * ((s x).val j : ℂ)) := Complex.exp_sum _ _
  simp_rw [e]
  rw [integral_fintype_prod_eq_prod (fun x (s : Spin 3) => Complex.exp (∑ j, H x j * (s.val j : ℂ)))]
  exact Finset.prod_ne_zero_iff.mpr fun x _ => single_site_cone (H x) (h x)

/-- Zero coupling in the finite-volume interacting partition convention,
with spatially inhomogeneous complex vector fields in the physical cone. -/
theorem physical_partition_zero_coupling {V : Type*} [Fintype V]
    (H : ComplexPartition.Field V) (h : ∀ x, ‖H x 1‖ + ‖H x 2‖ < (H x 0).re) :
    ComplexPartition.partition (fun _ _ => 0) H ≠ 0 := by
  simpa [ComplexPartition.partition, ComplexPartition.weight, PressureSelection.energy,
    ComplexPartition.surfaceProduct] using decoupled_vector_cone H h

/-- The up-spin population (1+S₀)/2 under the physical surface measure has
Lebesgue law on the unit interval. -/
theorem up_coordinate_law :
    θ.map (fun s : Spin 3 => (1+s.val 0)/2) =
      (volume : Measure ℝ).restrict (Set.Ioc 0 1) := by
  let readout (s : Spin 3) : ℝ := (1+s.val 0)/2
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  have hX : Continuous readout := by unfold readout; fun_prop
  have h : ProbabilityTheory.complexMGF readout θ = ProbabilityTheory.complexMGF id μ := by
    funext z
    by_cases hz : z = 0
    · subst z
      simp [ProbabilityTheory.complexMGF, μ, measureReal_def, Real.volume_Ioc]
    have half : z/2 ≠ 0 := by exact div_ne_zero hz (by norm_num)
    have e (s : Spin 3) : Complex.exp (z*(readout s : ℂ)) =
        Complex.exp (z/2)*Complex.exp ((z/2)*(s.val 0 : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      simp [readout]
      ring
    have mul : Complex.exp (z/2)*Complex.exp (z/2) = Complex.exp z := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have inv : Complex.exp (z/2)*Complex.exp (-(z/2)) = 1 := by rw [← Complex.exp_add]; simp
    change (∫ s, Complex.exp (z*(readout s : ℂ)) ∂θ) =
      ∫ u in Set.Ioc (0:ℝ) 1, Complex.exp (z*(u : ℂ))
    simp_rw [e]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_exp_mul_complex hz]
    change Complex.exp (z/2)*axialPartition (z/2) = _
    rw [axialPartition_eq half, Complex.sinh]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    calc
      _ = (Complex.exp (z/2) * (Complex.exp (z/2) - Complex.exp (-(z/2)))) / z := by
        field_simp
      _ = _ := by rw [mul_sub, mul, inv]
  simpa only [Measure.map_id] using
    (Measure.ext_of_complexMGF_eq hX.measurable.aemeasurable aemeasurable_id h)

/-- Physical axial Bernstein moment of the spin-up population. -/
theorem bernoulli_axis_moment (m : ℕ) :
    (∫ s : Spin 3, ((1+s.val 0)/2)^m ∂θ) = 1/((m:ℝ)+1) := by
  let readout (s : Spin 3) : ℝ := (1+s.val 0)/2
  have hX : Continuous readout := by unfold readout; fun_prop
  have h : (∫ u : ℝ, u^m ∂(θ.map readout)) = ∫ s, (readout s)^m ∂θ :=
    integral_map hX.measurable.aemeasurable (by fun_prop)
  rw [show θ.map readout = volume.restrict (Set.Ioc 0 1) from up_coordinate_law,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow] at h
  simpa [readout] using h.symm

/-- Every physical diagonal Bloch monomial has its exact beta weight.
The recursion comes from down = 1-up and uses no independent angular input. -/
theorem bernoulli_axis_mixed (k l : ℕ) :
    (∫ s : Spin 3, ((1-s.val 0)/2)^k * ((1+s.val 0)/2)^l ∂θ) =
      (k.factorial : ℝ) * (l.factorial : ℝ) / ((k+l+1).factorial : ℝ) := by
  let U (s : Spin 3) : ℝ := (1+s.val 0)/2
  let D (s : Spin 3) : ℝ := (1-s.val 0)/2
  let F (i j : ℕ) (s : Spin 3) := (D s)^i * (U s)^j
  have hF (i j : ℕ) : Integrable (F i j) θ := ci (by unfold F U D; fun_prop)
  have step (i j : ℕ) : (∫ s, F (i+1) j s ∂θ) =
      (∫ s, F i j s ∂θ) - (∫ s, F i (j+1) s ∂θ) := by
    rw [← integral_sub (hF i j) (hF i (j+1))]
    apply integral_congr_ae
    filter_upwards with s
    dsimp [F]
    have rel : D s = 1-U s := by dsimp [D,U]; ring
    rw [rel,pow_succ,pow_succ]
    ring
  change (∫ s, F k l s ∂θ) = _
  induction k generalizing l with
  | zero =>
    simp only [F, D, U, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, Nat.zero_add]
    rw [bernoulli_axis_moment, Nat.factorial_succ]
    push_cast
    field_simp
  | succ k ih =>
    rw [step, ih, ih]
    rw [show k + 1 + l + 1 = k+l+1+1 by omega,
      show k + (l+1) + 1 = k+l+1+1 by omega,
      Nat.factorial_succ (k+l+1), Nat.factorial_succ k, Nat.factorial_succ l]
    push_cast
    field_simp
    ring

#print axioms up_coordinate_law
#print axioms bernoulli_axis_moment
#print axioms bernoulli_axis_mixed
#print axioms axial_moment_eq
#print axioms axialPartition_analytic
#print axioms mul_axialPartition
#print axioms axialPartition_ne_zero
#print axioms decoupled_partition_ne_zero
#print axioms vector_even_moment
#print axioms vector_partition_eq_axial
#print axioms single_site_cone
#print axioms decoupled_vector_cone
#print axioms physical_partition_zero_coupling
end IsingScaling.Rotor.HeisenbergField.SingleSiteLeeYang
