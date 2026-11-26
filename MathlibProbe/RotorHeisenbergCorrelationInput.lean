import MathlibProbe.RotorHeisenbergVanishingField
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.MvPolynomial.Eval

/-! # The positive-field Heisenberg input in terms of scalar correlations

A multi-index records the sites, components and multiplicities in a finite
spin correlation. Coordinate polynomials separate full spin configurations.
Stone–Weierstrass therefore shows that all finite correlations determine a
probability law. Compactness then converts convergence of these correlations
in free cubes into convergence of the entire free-cube sequence. Translation
independence and the one comparison of free shapes needed for the bond
reflection can likewise be expressed as limits of finite-volume numbers.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace IsingScaling.Rotor.HeisenbergField
open PressureSelection

/-- Exponents of finitely many spin components at finitely many lattice sites. -/
abbrev MomentDegree := (Site × Fin 3) →₀ ℕ

private def component (i : Site × Fin 3) : C(SpinField 3, ℝ) where
  toFun s := (s i.1).val i.2
  continuous_toFun := by fun_prop

/-- The product of spin components with the indicated exponents. -/
def spinMoment (d : MomentDegree) : C(SpinField 3, ℝ) :=
  d.prod fun i k => component i ^ k

theorem spinMoment_apply (d : MomentDegree) (s : SpinField 3) :
    spinMoment d s = ∏ i ∈ d.support, ((s i.1).val i.2) ^ (d i) := by
  simp [spinMoment, Finsupp.prod, component]

private abbrev Poly := MvPolynomial (Site × Fin 3) ℝ
private def polynomialTest : Poly →ₐ[ℝ] C(SpinField 3, ℝ) := MvPolynomial.aeval component

private theorem polynomialTest_separates : polynomialTest.range.SeparatesPoints := by
  intro s t hst
  have h : ∃ i : Site × Fin 3, component i s ≠ component i t := by
    by_contra! he
    apply hst
    funext x
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    funext k
    exact he (x,k)
  obtain ⟨i,hi⟩ := h
  refine ⟨(component i : SpinField 3 → ℝ), ⟨component i, ⟨MvPolynomial.X i,?_⟩,rfl⟩,hi⟩
  exact MvPolynomial.aeval_X _ _

private def mean (P : ProbabilityMeasure (SpinField 3)) (F : C(SpinField 3, ℝ)) : ℝ :=
  ∫ s, F s ∂(P : Measure _)

private theorem testIntegrable (P : ProbabilityMeasure (SpinField 3)) (F : C(SpinField 3, ℝ)) :
    Integrable F (P : Measure _) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem mean_continuous (P : ProbabilityMeasure (SpinField 3)) : Continuous (mean P) := by
  apply LipschitzWith.continuous (K := 1)
  rw [lipschitzWith_iff_dist_le_mul]
  intro F G
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, mean]
  rw [← integral_sub (testIntegrable P F) (testIntegrable P G)]
  exact (BoundedContinuousFunction.mkOfCompact (F-G)).norm_integral_le_norm (P : Measure _)

/-- All coordinate moments determine the entire spin-field law. -/
theorem eq_of_spinMoments {P Q : ProbabilityMeasure (SpinField 3)}
    (hm : ∀ d, (∫ s, spinMoment d s ∂(P : Measure _)) = ∫ s, spinMoment d s ∂(Q : Measure _)) :
    P = Q := by
  have hp : Set.EqOn (mean P) (mean Q) (polynomialTest.range : Set C(SpinField 3, ℝ)) := by
    rintro _ ⟨p,rfl⟩
    induction p using MvPolynomial.induction_on' with
    | monomial d a =>
      change (∫ s, (MvPolynomial.aeval component (MvPolynomial.monomial d a)) s ∂(P : Measure _)) =
        ∫ s, (MvPolynomial.aeval component (MvPolynomial.monomial d a)) s ∂(Q : Measure _)
      simp only [MvPolynomial.aeval_monomial, ContinuousMap.mul_apply, algebraMap_apply,
        smul_eq_mul, mul_one, integral_const_mul]
      exact congrArg (a * ·) (hm d)
    | add p q hp hq =>
      simp only [mean, map_add, ContinuousMap.add_apply,
        integral_add (testIntegrable _ _) (testIntegrable _ _)] at hp hq ⊢
      rw [hp,hq]
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  exact hp.closure (mean_continuous P) (mean_continuous Q)
    (ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints
      _ polynomialTest_separates F.toContinuousMap)

/-- The three correlation statements used from the positive-field
thermodynamic theorem. Each integral is taken under a specified finite law.
The second and third clauses compare two finite-volume measurements. -/
structure ScalarThermodynamicLimit (β h : ℝ) : Prop where
  moments : ∀ d : MomentDegree, ∃ a : ℝ,
    Tendsto (fun L => ∫ s, spinMoment d s ∂(cubeLaw β h L : Measure _)) atTop (𝓝 a)
  translates : ∀ (u : Site) (d : MomentDegree),
    Tendsto (fun L => (∫ s, spinMoment d (shiftField u s) ∂(cubeLaw β h L : Measure _)) -
      ∫ s, spinMoment d s ∂(cubeLaw β h L : Measure _)) atTop (𝓝 0)
  rectangles : ∀ x y : Site, 0 < x 0 → 0 < y 0 →
    Tendsto (fun L => BondRectangle.crossPair (fieldPrior h) β
      (BondMirror.port L x) (BondMirror.port L y) -
      ∫ s, fieldDot 3 x (BondMirror.reflected y) s ∂(cubeLaw β h L : Measure _)) atTop (𝓝 0)

/-- Compactness and scalar positive-field correlations give the same full
free law for the centered cube measurements and the bond-rectangle pairs. -/
theorem ScalarThermodynamicLimit.exists_commonFreeLimit {β h : ℝ}
    (H : ScalarThermodynamicLimit β h) :
    ∃ P : ProbabilityMeasure (SpinField 3), CommonFreeLimit β h P := by
  obtain ⟨P,k,hk,_,hPk⟩ := spinField_subsequence 3 (cubeLaw β h)
  have hP : Tendsto (cubeLaw β h) atTop (𝓝 P) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro n hn
    obtain ⟨Q,j,hj,hQ,hQj⟩ := spinField_subsequence 3 (cubeLaw β h ∘ n)
    have hQP : Q = P := by
      apply eq_of_spinMoments
      intro d
      obtain ⟨a,ha⟩ := H.moments d
      exact (tendsto_nhds_unique (hQj (spinMoment d)) (ha.comp (hn.comp hj.tendsto_atTop))).trans
        (tendsto_nhds_unique (ha.comp hk.tendsto_atTop) (hPk (spinMoment d)))
    exact ⟨j,hQP ▸ hQ⟩
  have test (F : C(SpinField 3, ℝ)) :
      Tendsto (fun L => ∫ s, F s ∂(cubeLaw β h L : Measure _)) atTop
        (𝓝 (∫ s, F s ∂(P : Measure _))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP
  have hstat : ShiftInvariant P := by
    intro u
    let pu := P.map (shiftField u).continuous.measurable.aemeasurable
    have e : pu = P := by
      apply eq_of_spinMoments
      intro d
      change (∫ s, spinMoment d s ∂(P : Measure _).map (shiftField u)) = _
      rw [integral_map (shiftField u).continuous.measurable.aemeasurable
        (spinMoment d).continuous.aestronglyMeasurable]
      exact sub_eq_zero.mp (tendsto_nhds_unique
        ((test ((spinMoment d).comp (shiftField u))).sub (test (spinMoment d))) (H.translates u d))
    exact ⟨(shiftField u).continuous.measurable, congrArg ProbabilityMeasure.toMeasure e⟩
  refine ⟨P,hP,hstat,?_⟩
  intro x y hx hy
  have pair := test (fieldDot 3 x (BondMirror.reflected y))
  rw [stationary_dot_integral hstat] at pair
  have lim := (H.rectangles x y hx hy).add pair
  simpa only [sub_add_cancel, zero_add] using lim

theorem CommonFreeLimit.scalarThermodynamicLimit {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)}
    (H : CommonFreeLimit β h P) : ScalarThermodynamicLimit β h := by
  have test (F : C(SpinField 3, ℝ)) :
      Tendsto (fun L => ∫ s, F s ∂(cubeLaw β h L : Measure _)) atTop
        (𝓝 (∫ s, F s ∂(P : Measure _))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp H.centered
  refine ⟨fun d => ⟨_,test (spinMoment d)⟩,?_,?_⟩
  · intro u d
    have eq : (∫ s, spinMoment d (shiftField u s) ∂(P : Measure _)) =
        ∫ s, spinMoment d s ∂(P : Measure _) := by
      rw [← integral_map (shiftField u).continuous.measurable.aemeasurable
        (spinMoment d).continuous.aestronglyMeasurable, (H.stationary u).map_eq]
    simpa only [ContinuousMap.comp_apply, eq, sub_self] using
      ((test ((spinMoment d).comp (shiftField u))).sub (test (spinMoment d)))
  · intro x y hx hy
    have pair := test (fieldDot 3 x (BondMirror.reflected y))
    rw [stationary_dot_integral H.stationary] at pair
    simpa only [sub_self] using (H.rectangle x y hx hy).sub pair

/-- The remaining input for all positive fields can be stated using only
finite-volume scalar correlations. -/
theorem positiveFieldInput_iff_scalar (β : ℝ) :
    PositiveFieldThermodynamicInput β ↔ ∀ h : ℝ, 0 < h → ScalarThermodynamicLimit β h := by
  constructor
  · intro H h hh
    obtain ⟨P,hP⟩ := H h hh
    exact hP.scalarThermodynamicLimit
  · exact fun H h hh => (H h hh).exists_commonFreeLimit

#print axioms eq_of_spinMoments
#print axioms ScalarThermodynamicLimit.exists_commonFreeLimit
#print axioms positiveFieldInput_iff_scalar

end IsingScaling.Rotor.HeisenbergField
