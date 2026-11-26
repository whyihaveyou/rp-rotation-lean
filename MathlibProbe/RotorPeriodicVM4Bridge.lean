import MathlibProbe.RotorPeriodicCharacterPolynomial
import MathlibProbe.RotorResolventTestApproximation

/-!
# The VM-4 approximation on the physical momentum torus

The resolvent approximation is stated on the compact cube of cosine
coordinates. This file supplies the exact map from the actual momentum
torus and the packet polynomial produced by the finite Gibbs character.
-/

noncomputable section
open MeasureTheory
open scoped Topology
namespace IsingScaling.Rotor.PressureSelection
open MathlibProbe.RotorObliqueTestPolynomials
open MathlibProbe.RotorResolventTestApproximation

def momentumCosine (k : Momentum) : CosineCube :=
  fun i => ⟨(k i : ℂ).re, abs_le.mp ((Complex.abs_re_le_norm (k i : ℂ)).trans_eq (Circle.norm_coe _))⟩

def momentumCosineMap : C(Momentum, CosineCube) where
  toFun := momentumCosine
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_apply i))

theorem horizontalMean_approx_variation {ι : Type*} [Fintype ι]
    (r : Site → Site) (x : ι → Site) (c : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F ∈ Submodule.span ℝ variations, ∀ k : Momentum,
      |horizontalMean (reflectedTest r x c) k - F (momentumCosine k)| < ε := by
  obtain ⟨A,B,C,hABC⟩ := horizontalMean_reflectedTest_elementary r x c
  obtain ⟨F,hF,hclose⟩ := approximate_three_polynomials A B C hε
  refine ⟨F,hF,fun k => ?_⟩
  rw [hABC k]
  exact hclose (momentumCosine k)

/-- VM-4 and VM-6 combined. Each comparison law is allowed to depend on
the physical variation in the specified real span. -/
theorem reflected_pair_of_resolvent_comparisons (μ : Measure Momentum) [IsProbabilityMeasure μ]
    (hμ : HorizontallyInvariant μ) {ι : Type*} [Fintype ι]
    (r : Site → Site) (x : ι → Site) (c : ι → ℝ)
    (hcompare : ∀ F ∈ Submodule.span ℝ variations, ∃ ν : ProbabilityMeasure Momentum,
      HorizontallyInvariant (ν : Measure Momentum) ∧
      (∫ k, F (momentumCosine k) ∂μ) ≤ (∫ k, F (momentumCosine k) ∂(ν : Measure Momentum)) ∧
      0 ≤ ∑ i, ∑ j, (c i*c j) * spectralPair (ν : Measure Momentum) (x i-r (x j))) :
    0 ≤ ∑ i, ∑ j, (c i*c j) * spectralPair μ (x i-r (x j)) := by
  let dirs : Set C(Momentum, ℝ) := {H | ∃ F ∈ Submodule.span ℝ variations, H = F.comp momentumCosineMap}
  apply reflected_pair_of_admissible_variations μ hμ r x c dirs
  · intro ε hε
    obtain ⟨F,hF,hclose⟩ := horizontalMean_approx_variation r x c hε
    refine ⟨(-F).comp momentumCosineMap, ⟨-F,(Submodule.span ℝ variations).neg_mem hF,rfl⟩,?_⟩
    intro k
    change |-F (momentumCosine k) + horizontalMean (reflectedTest r x c) k| ≤ ε
    rw [neg_add_eq_sub]
    exact (hclose k).le
  · rintro H ⟨F,hF,rfl⟩
    exact hcompare F hF

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.horizontalMean_approx_variation
#print axioms IsingScaling.Rotor.PressureSelection.reflected_pair_of_resolvent_comparisons
