import MathlibProbe.RotorPeriodicPressureTransfer
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Transferring an oblique two-point mirror test

The Fourier test is the real character polynomial of the actual signed
packet. Its group average keeps the third coordinate distinguished.
Every comparison law may depend on the chosen interaction variation.
Only the original law is held fixed while the approximation error tends
to zero.
-/

noncomputable section
open MeasureTheory Finset Filter
open scoped Topology
namespace IsingScaling.Rotor.PressureSelection

abbrev Momentum := Fin 3 → Circle
abbrev HorizontalSymmetry := (Fin 3 → Bool) × Bool

instance momentumMeasurableSpace : MeasurableSpace Momentum := borel _
instance momentumBorelSpace : BorelSpace Momentum := ⟨rfl⟩

/-- The real part of the lattice character at a torus momentum. -/
def realCharacter (z : Site) : C(Momentum, ℝ) where
  toFun k := ((∏ i, (k i) ^ (z i) : Circle) : ℂ).re
  continuous_toFun := by
    have hc : Continuous (fun k : Momentum => ∏ i, (k i) ^ (z i) : Momentum → Circle) := by
      apply continuous_finsetProd
      intro i _
      have he : Continuous (fun k : Momentum => k i) := continuous_apply i
      exact he.zpow (z i)
    exact Complex.continuous_re.comp (continuous_subtype_val.comp hc)

def spectralPair (μ : Measure Momentum) (z : Site) := ∫ k, realCharacter z k ∂μ

def horizontalAction (a : HorizontalSymmetry) (k : Momentum) : Momentum :=
  let p : Equiv.Perm (Fin 3) := if a.2 then Equiv.swap 0 1 else Equiv.refl _
  fun i => if a.1 i then (k (p i))⁻¹ else k (p i)

private lemma continuous_horizontalAction (a : HorizontalSymmetry) : Continuous (horizontalAction a) := by
  apply continuous_pi
  intro i
  unfold horizontalAction
  by_cases h : a.1 i <;> simp [h] <;> fun_prop

def HorizontallyInvariant (μ : Measure Momentum) : Prop :=
  ∀ a : HorizontalSymmetry, MeasurePreserving (horizontalAction a) μ μ

def horizontalMean (T : C(Momentum, ℝ)) : C(Momentum, ℝ) where
  toFun k := (∑ a : HorizontalSymmetry, T (horizontalAction a k)) / Fintype.card HorizontalSymmetry
  continuous_toFun := (continuous_finsetSum _ (fun a _ =>
    T.continuous.comp (continuous_horizontalAction a))).div_const _

private theorem integral_horizontalMean (μ : Measure Momentum) [IsProbabilityMeasure μ]
    (hμ : HorizontallyInvariant μ) (T : C(Momentum, ℝ)) :
    (∫ k, horizontalMean T k ∂μ) = ∫ k, T k ∂μ := by
  have hc (a : HorizontalSymmetry) : Integrable (fun k => T (horizontalAction a k)) μ :=
    (T.continuous.comp (continuous_horizontalAction a)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs (a : HorizontalSymmetry) :
      (∫ k, T (horizontalAction a k) ∂μ) = ∫ k, T k ∂μ :=
    (hμ a).hasLaw.integral_comp T.continuous.aestronglyMeasurable
  change (∫ k, (∑ a : HorizontalSymmetry, T (horizontalAction a k)) / Fintype.card HorizontalSymmetry ∂μ) = _
  rw [integral_div, integral_finsetSum _ (fun a _ => hc a)]
  simp only [hs, sum_const, card_univ, nsmul_eq_mul]
  field_simp

def reflectedTest {ι : Type*} [Fintype ι] (r : Site → Site) (x : ι → Site) (c : ι → ℝ) :
    C(Momentum, ℝ) where
  toFun k := ∑ i, ∑ j, (c i * c j) * realCharacter (x i - r (x j)) k
  continuous_toFun := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (realCharacter _).continuous

theorem integral_reflectedTest (μ : Measure Momentum) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (r : Site → Site) (x : ι → Site) (c : ι → ℝ) :
    (∫ k, reflectedTest r x c k ∂μ) = ∑ i, ∑ j, (c i*c j) * spectralPair μ (x i-r (x j)) := by
  let F (i j : ι) (k : Momentum) := (c i*c j) * realCharacter (x i - r (x j)) k
  have hc (i j : ι) : Continuous (F i j) := continuous_const.mul (realCharacter _).continuous
  change (∫ k, ∑ i, ∑ j, F i j k ∂μ) = _
  rw [integral_finsetSum _ (fun i _ => (continuous_finsetSum _ (fun j _ => hc i j)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hc _ j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  simp only [F, integral_const_mul, spectralPair]

private theorem bounded_error (μ : Measure Momentum) [IsProbabilityMeasure μ]
    (hμ : HorizontallyInvariant μ) (T H : C(Momentum, ℝ)) {ε : ℝ}
    (happ : ∀ k, |H k + horizontalMean T k| ≤ ε) :
    |(∫ k, H k ∂μ) + (∫ k, T k ∂μ)| ≤ ε := by
  have hi := norm_integral_le_of_norm_le_const (μ := μ) (f := fun k => H k + horizontalMean T k)
    (C := ε) (Eventually.of_forall (fun k => by simpa [Real.norm_eq_abs] using happ k))
  rw [integral_add
    (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((horizontalMean T).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_horizontalMean μ hμ T] at hi
  simpa [Real.norm_eq_abs] using hi

/-- VM-6 on the actual three-dimensional Fourier torus. The family of
directions is fixed. One needs approximation of the stabilizer average,
and pressure comparison only in the chosen direction. -/
theorem reflected_pair_of_admissible_variations (μ : Measure Momentum) [IsProbabilityMeasure μ]
    (hμ : HorizontallyInvariant μ) {ι : Type*} [Fintype ι]
    (r : Site → Site) (x : ι → Site) (c : ι → ℝ) (directions : Set C(Momentum, ℝ))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ H ∈ directions, ∀ k,
      |H k + horizontalMean (reflectedTest r x c) k| ≤ ε)
    (hcompare : ∀ H ∈ directions, ∃ ν : ProbabilityMeasure Momentum,
      HorizontallyInvariant (ν : Measure Momentum) ∧
      (∫ k, H k ∂μ) ≤ (∫ k, H k ∂(ν : Measure Momentum)) ∧
      0 ≤ ∑ i, ∑ j, (c i*c j) * spectralPair (ν : Measure Momentum) (x i-r (x j))) :
    0 ≤ ∑ i, ∑ j, (c i*c j) * spectralPair μ (x i-r (x j)) := by
  let T := reflectedTest r x c
  rw [← integral_reflectedTest]
  change 0 ≤ ∫ k, T k ∂μ
  by_contra! hneg
  let ε := -(∫ k, T k ∂μ) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨H, hin, hfit⟩ := happrox ε hε
  obtain ⟨ν, hν, hresp, href⟩ := hcompare H hin
  rw [← integral_reflectedTest] at href
  change 0 ≤ ∫ k, T k ∂(ν : Measure Momentum) at href
  have h1 := (abs_le.mp (bounded_error μ hμ T H hfit)).1
  have h2 := (abs_le.mp (bounded_error (ν : Measure Momentum) hν T H hfit)).2
  dsimp only [ε] at h1 h2
  linarith

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.reflected_pair_of_admissible_variations
