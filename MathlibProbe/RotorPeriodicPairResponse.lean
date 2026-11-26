import MathlibProbe.RotorPeriodicSeam
import MathlibProbe.RotorPeriodicSpectralTest
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The displacement observable in the two-shape pressure comparison

Average the actual Gibbs dot pair over the starting vertex of every
periodized displacement. Absolute summability of the full interaction
and unit spin length permit every winding and every fixed-pair limit
to be retained when opening the finite pressure responses.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology
namespace IsingScaling.Rotor.PressureSelection

def averagedDot (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (D : Site → V → V) (H : V → V → ℝ) (z : Site) : ℝ :=
  (∑ v, dotPair N H v (D z v)) / Fintype.card V

theorem abs_averagedDot_le_one (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (H : V → V → ℝ) (z : Site) : |averagedDot N D H z| ≤ 1 := by
  have hc : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [averagedDot, abs_div, abs_of_pos hc, div_le_one hc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact (Finset.sum_le_sum (fun v _ => abs_dotPair_le_one N H v (D z v))).trans_eq (by simp)

private lemma summable_diff {J K : Site → ℝ} (hJ : Summable (fun z => |J z|))
    (hK : Summable (fun z => |K z|)) : Summable (fun z => |K z-J z|) := by
  apply (hK.add hJ).of_norm_bounded
  intro z
  simpa [Real.norm_eq_abs] using abs_sub (K z) (J z)

/-- This identity permits negative couplings, repeated destinations and
a nonuniform choice of the starting-site pairs. -/
theorem response_periodize_eq (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [DecidableEq V]
    (D : Site → V → V) (H : V → V → ℝ) (J K : Site → ℝ)
    (hJ : Summable (fun z => |J z|)) (hK : Summable (fun z => |K z|)) :
    response N H (Seam.periodizeSeries D J) (Seam.periodizeSeries D K) =
      (∑' z, (K z-J z) * averagedDot N D H z) / 2 := by
  classical
  let F (z : Site) (v w : V) : ℝ := if D z v = w then (K z-J z) * dotPair N H v w else 0
  have hcell (J : Site → ℝ) (hJ : Summable (fun z => |J z|)) (v w : V) :
      HasSum (fun z => if D z v = w then J z else 0) (Seam.periodizeSeries D J v w) := by
    apply Summable.hasSum
    exact hJ.of_norm_bounded fun z => by by_cases h : D z v = w <;> simp [h, Real.norm_eq_abs]
  have hF (v w : V) : HasSum (fun z => F z v w)
      ((Seam.periodizeSeries D K v w-Seam.periodizeSeries D J v w) * dotPair N H v w) := by
    apply (((hcell K hK v w).sub (hcell J hJ v w)).mul_right _).congr_fun
    intro z
    by_cases h : D z v = w <;> simp [F,h]
  have hall : HasSum (fun z => ∑ v, ∑ w, F z v w)
      (∑ v, ∑ w, (Seam.periodizeSeries D K v w-Seam.periodizeSeries D J v w) * dotPair N H v w) :=
    hasSum_sum fun v _ => hasSum_sum fun w _ => hF v w
  have hrow (z : Site) : ∑ v, ∑ w, F z v w = (K z-J z) * ∑ v, dotPair N H v (D z v) := by
    simp [F, Finset.mul_sum]
  rw [response_eq_dotPair, ← hall.tsum_eq]
  simp_rw [hrow, averagedDot, ← mul_div_assoc]
  rw [tsum_div_const]
  ring

private theorem tendsto_pairing {J : Site → ℝ} (hJ : Summable (fun z => |J z|))
    (g : ℕ → Site → ℝ) (f : Site → ℝ) (hg : ∀ n z, |g n z| ≤ 1)
    (hf : ∀ z, Tendsto (fun n => g n z) atTop (𝓝 (f z))) :
    Tendsto (fun n => ∑' z, J z * g n z) atTop (𝓝 (∑' z, J z * f z)) := by
  apply tendsto_tsum_of_dominated_convergence hJ (fun z => (hf z).const_mul (J z))
  refine Eventually.of_forall fun n z => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hg n z)

def cubicPair (N L : ℕ) [NeZero N] [NeZero L] (J : Site → ℝ) : Site → ℝ :=
  averagedDot N Seam.baseMove (Seam.ordinarySeries L J)

def diagonalPair (N L : ℕ) [NeZero N] [NeZero L] (J : Site → ℝ) : Site → ℝ :=
  averagedDot N Seam.adaptedDestination (Seam.adaptedSeries L J)

/-- The two profiles are limits of concrete Gibbs two-point observables on
the same side lengths. No pressure, energy-observable or functional
inequality is included as a premise. -/
theorem compare_periodic_pairings (N : ℕ) [NeZero N] (J K : Site → ℝ)
    (hJ : Summable (fun z => |J z|)) (hK : Summable (fun z => |K z|))
    (sides : ℕ → ℕ) [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop)
    {g h : Site → ℝ}
    (hg : ∀ z, Tendsto (fun n => cubicPair N (sides n) J z) atTop (𝓝 (g z)))
    (hh : ∀ z, Tendsto (fun n => diagonalPair N (sides n) K z) atTop (𝓝 (h z))) :
    (∑' z, (K z-J z)*g z) ≤ (∑' z, (K z-J z)*h z) := by
  have hδ := summable_diff hJ hK
  have hcg := (tendsto_pairing hδ _ g (fun n z => abs_averagedDot_le_one N _ _ z) hg).div_const 2
  have hag := (tendsto_pairing hδ _ h (fun n z => abs_averagedDot_le_one N _ _ z) hh).div_const 2
  have hle := Seam.compare_periodic_pair_responses N J K hJ hK sides hsides _ _
    (by simpa only [Seam.ordinarySeries, response_periodize_eq N _ _ J K hJ hK, cubicPair] using hcg)
    (by simpa only [Seam.adaptedSeries, response_periodize_eq N _ _ J K hJ hK, diagonalPair] using hag)
  linarith

theorem abs_realCharacter_le_one (z : Site) (k : Momentum) : |realCharacter z k| ≤ 1 := by
  let w : Circle := ∏ i, k i ^ z i
  exact (Complex.abs_re_le_norm (w : ℂ)).trans_eq (Circle.norm_coe w)

/-- Uniformly convergent Fourier series of a real summable pair variation
on the actual three-dimensional momentum torus. -/
def interactionMultiplier (J : Site → ℝ) (hJ : Summable (fun z => |J z|)) : C(Momentum, ℝ) where
  toFun k := ∑' z, J z * realCharacter z k
  continuous_toFun := continuous_tsum (fun z => continuous_const.mul (realCharacter z).continuous)
    hJ (fun z k => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_realCharacter_le_one z k))

theorem integral_interactionMultiplier (J : Site → ℝ) (hJ : Summable (fun z => |J z|))
    (μ : Measure Momentum) [IsProbabilityMeasure μ] :
    (∫ k, interactionMultiplier J hJ k ∂μ) = ∑' z, J z * spectralPair μ z := by
  let F (z : Site) (k : Momentum) := J z * realCharacter z k
  have hi (z : Site) : Integrable (F z) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul (realCharacter z).continuous
  have hb (z : Site) (k : Momentum) : ‖F z k‖ ≤ |J z| := by
    change ‖J z * realCharacter z k‖ ≤ |J z|
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_realCharacter_le_one z k)
  have hs : Summable (fun z => ∫ k, ‖F z k‖ ∂μ) := by
    apply hJ.of_norm_bounded
    intro z
    have hz := integral_mono (hi z).norm (integrable_const (|J z|)) (hb z)
    rw [Real.norm_of_nonneg (integral_nonneg fun k => norm_nonneg (F z k))]
    simpa using hz
  have he := (integral_tsum_of_summable_integral_norm hi hs).symm
  simpa only [interactionMultiplier, ContinuousMap.coe_mk, F, integral_const_mul, spectralPair] using he

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.compare_periodic_pairings
#print axioms IsingScaling.Rotor.PressureSelection.integral_interactionMultiplier
