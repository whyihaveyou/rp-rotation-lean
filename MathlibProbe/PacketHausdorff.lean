import MathlibProbe.IsingSiteReflection
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp

/-! The Hausdorff moment construction for even-time reflection-positive packets.
Bernstein weights realize positive measures on the uniform grid. Removing one
size-biased success identifies every limiting power moment with the prescribed
sequence. -/
noncomputable section
open Finset Filter Set MeasureTheory
open scoped Topology ENNReal
namespace IsingScaling.Packet

private def shift (a : ℕ → ℝ) (j : ℕ) := a (j+1)

private lemma diff_shift (a : ℕ → ℝ) (k j : ℕ) :
    (diff^[k]) (shift a) j = (diff^[k]) a (j+1) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', diff, ih]

private def weight (a : ℕ → ℝ) (n j : ℕ) : ℝ :=
  (n.choose j : ℝ) * (diff^[n-j]) a j

private lemma weight_split (a : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    weight a (n+1) (j+1) =
      weight (diff a) n (j+1) + weight (shift a) n j := by
  by_cases he : j = n
  · subst j
    simp [weight, shift]
  · have h : (n-(j+1)).succ = n-j := by omega
    simp only [weight, Nat.add_sub_add_right, diff_shift, ← Function.iterate_succ_apply,
      h, Nat.choose_succ_succ, Nat.cast_add]
    ring

private lemma sum_weight (a : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n+1), weight a n j = a 0 := by
  induction n generalizing a with
  | zero => simp [weight]
  | succ n ih =>
    rw [sum_range_succ']
    have hs : ∑ j ∈ range (n+1), weight a (n+1) (j+1) =
        (∑ j ∈ range (n+1), weight (diff a) n (j+1)) + shift a 0 := by
      rw [← ih (shift a), ← sum_add_distrib]
      exact sum_congr rfl fun j hj => weight_split a n j (by simpa using hj)
    rw [hs, show weight a (n+1) 0 = weight (diff a) n 0 by
      simp [weight, Function.iterate_succ_apply]]
    have hz : weight (diff a) n (n+1) = 0 := by
      simp [weight]
    have htotal := sum_range_succ' (fun j => weight (diff a) n j) (n+1)
    rw [sum_range_succ, hz, add_zero, ih] at htotal
    unfold diff shift at *
    linarith

private lemma weight_bias (a : ℕ → ℝ) (n j : ℕ) :
    weight a (n+1) (j+1) * (j+1:ℕ) = (n+1:ℕ) * weight (shift a) n j := by
  simp only [weight, Nat.add_sub_add_right, diff_shift]
  have h : ((n+1:ℕ):ℝ) * (n.choose j : ℝ) =
      ((n+1).choose (j+1):ℝ) * ((j+1:ℕ):ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  linear_combination -((diff^[n-j]) a (j+1)) * h

private def gridMoment (a : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ j ∈ range (n+1), weight a n j * ((j:ℝ)/n)^k

private lemma gridMoment_succ (a : ℕ → ℝ) (n k : ℕ) :
    gridMoment a (n+1) (k+1) =
      ∑ j ∈ range (n+1), weight (shift a) n j * (((j+1:ℕ):ℝ)/(n+1:ℕ))^k := by
  unfold gridMoment
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_div, zero_pow (Nat.succ_ne_zero k), mul_zero, add_zero]
  apply sum_congr rfl
  intro j _
  rw [pow_succ, ← mul_assoc, mul_right_comm, ← mul_div_assoc, weight_bias]
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hn, mul_comm]

private lemma grid_step_bounds {j n k : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    ((j:ℝ)/n)^k ≤ (((j+1:ℕ):ℝ)/(n+1:ℕ))^k ∧
    (((j+1:ℕ):ℝ)/(n+1:ℕ))^k ≤ ((j:ℝ)/n)^k + (1 / ((n:ℝ)+1)) * k := by
  let x : ℝ := (j:ℝ)/n
  let y : ℝ := ((j+1:ℕ):ℝ)/(n+1:ℕ)
  have hr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hrj : (j:ℝ) ≤ n := by exact_mod_cast hj
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : y ≤ 1 := by dsimp [y]; push_cast; rw [div_le_one (by positivity)]; linarith
  have hxy : x ≤ y := by
    dsimp [x,y]; push_cast; rw [div_le_div_iff₀ hr (by positivity)]; nlinarith
  have hd : y - x ≤ 1 / ((n:ℝ)+1) := by
    dsimp [x,y]; push_cast
    apply (le_div_iff₀ (by positivity : (0:ℝ) < n+1)).2
    field_simp
    nlinarith
  have hp := abs_pow_sub_pow_le y x k
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hx hxy _)),
    abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg (hx.trans hxy), abs_of_nonneg hx,
    max_eq_left hxy] at hp
  have hpow : y^(k-1) ≤ 1 := pow_le_one₀ (hx.trans hxy) hy
  refine ⟨pow_le_pow_left₀ hx hxy _, ?_⟩
  change y^k ≤ x^k + _
  nlinarith [mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (sub_nonneg.mpr hxy) (Nat.cast_nonneg k)),
    mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg k)]

private lemma gridMoment_tendsto (a : ℕ → ℝ) (ha : ∀ k j, 0 ≤ (diff^[k]) a j)
    (k : ℕ) : Tendsto (fun n => gridMoment a n k) atTop (𝓝 (a k)) := by
  induction k generalizing a with
  | zero =>
    simpa only [gridMoment, pow_zero, mul_one, sum_weight] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a 0) atTop (𝓝 (a 0)))
  | succ k ih =>
    have hs : ∀ d j, 0 ≤ (diff^[d]) (shift a) j := fun d j => by
      rw [diff_shift]; exact ha _ _
    have hw (n j) : 0 ≤ weight (shift a) n j :=
      mul_nonneg (Nat.cast_nonneg _) (hs _ _)
    have ht := ih (shift a) hs
    have hzero : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))*k*shift a 0) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (k:ℝ) |>.mul_const (shift a 0)
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ht
      (show Tendsto (fun n => gridMoment (shift a) n k + (1/((n:ℝ)+1))*k*shift a 0)
        atTop (𝓝 (shift a k)) from by simpa using ht.add hzero)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [gridMoment_succ]
      exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
        (grid_step_bounds (k:=k) hn (by simpa using hj)).1 (hw _ _)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [gridMoment_succ]
      calc
        _ ≤ ∑ j ∈ range (n+1), weight (shift a) n j *
           (((j:ℝ)/n)^k + (1/((n:ℝ)+1)) * k) := by
             exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
               (grid_step_bounds hn (by simpa using hj)).2 (hw _ _)
        _ = _ := by
          simp_rw [mul_add, sum_add_distrib, ← sum_mul, sum_weight, gridMoment]
          ring

abbrev UnitInterval := Set.Icc (0:ℝ) 1

private def gridPoint (n j : ℕ) : UnitInterval :=
  ⟨min ((j:ℝ)/n) 1, le_min (by positivity) zero_le_one, min_le_right ..⟩

private def empirical (a : ℕ → ℝ) (n : ℕ) : FiniteMeasure UnitInterval :=
  ⟨∑ j ∈ range (n+1), (weight a n j).toNNReal • Measure.dirac (gridPoint n j),
   by infer_instance⟩

private def powerTest (k : ℕ) : C(UnitInterval, ℝ) :=
  ⟨fun x => (x:ℝ)^k, by fun_prop⟩

def powerMoment (μ : FiniteMeasure UnitInterval) (k : ℕ) : ℝ :=
  ∫ x, powerTest k x ∂(μ : Measure UnitInterval)

private lemma empirical_moment (a : ℕ → ℝ) (ha : ∀ k j, 0 ≤ (diff^[k]) a j)
    (n k : ℕ) : powerMoment (empirical a n) k = gridMoment a n k := by
  unfold powerMoment
  change (∫ x, powerTest k x ∂∑ j ∈ range (n+1), (weight a n j).toNNReal •
    Measure.dirac (gridPoint n j)) = _
  rw [integral_finsetSum_measure]
  · apply sum_congr rfl
    intro j hj
    have hw : 0 ≤ weight a n j := mul_nonneg (Nat.cast_nonneg _) (ha _ _)
    have hgrid : (j:ℝ)/n ≤ 1 := by
      by_cases hn : n=0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast (show j ≤ n by simpa using hj)
    simp [powerTest, gridPoint, hw, min_eq_left hgrid, NNReal.smul_def]
  · intro j _
    exact (powerTest k).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem hausdorff_moments (a : ℕ → ℝ) (ha : ∀ k j, 0 ≤ (diff^[k]) a j) :
    ∃ μ : FiniteMeasure UnitInterval, ∀ k, (∫ t, (t:ℝ)^k ∂(μ : Measure UnitInterval)) = a k := by
  have hc : Continuous powerMoment := continuous_pi fun k =>
    FiniteMeasure.continuous_integral_continuousMap (powerTest k)
  have hm (μ : FiniteMeasure UnitInterval) : powerMoment μ 0 = (μ.mass:ℝ) := by
    unfold powerMoment
    simp only [powerTest, ContinuousMap.coe_mk, pow_zero, integral_const, smul_eq_mul, mul_one]
    rfl
  have hf (n : ℕ) : (empirical a n).mass ≤ (a 0).toNNReal := by
    change ((empirical a n).mass:ℝ) ≤ ((a 0).toNNReal:ℝ)
    rw [← hm, empirical_moment _ ha, Real.coe_toNNReal _ (show 0 ≤ a 0 from ha 0 0)]
    simp [gridMoment, sum_weight]
  have hclosed := ((isCompact_setOfPred_finiteMeasure_le_of_compactSpace
    UnitInterval (a 0).toNNReal).image hc).isClosed
  have hlim : Tendsto (fun n => powerMoment (empirical a n)) atTop (𝓝 a) :=
    tendsto_pi_nhds.mpr fun k => by
      simpa only [empirical_moment _ ha] using gridMoment_tendsto a ha k
  obtain ⟨μ, _, hμ⟩ := hclosed.mem_of_tendsto hlim
    (Eventually.of_forall fun n => ⟨empirical a n, hf n, rfl⟩)
  exact ⟨μ, congrFun hμ⟩

#print axioms hausdorff_moments

/-- Actual stationary free-cube two-site limits have positive finite time
spectra on the even axial mesh. -/
theorem axis_evenPacket_spectrum {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x-y))) {ι : Type} [Fintype ι]
    (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure UnitInterval, ∀ n, (∫ t, (t:ℝ)^n ∂(μ : Measure UnitInterval)) =
      evenPacket c (fun m i j => g ![(m:ℤ), x i-x j, y i-y j]) n :=
  hausdorff_moments _ (axis_evenPacket_completeMonotone hg c x y)

/-- The same positive spectral representation holds along a face diagonal,
with spatial displacement (2n,-2n,0). -/
theorem diagonal_evenPacket_spectrum {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x-y))) {ι : Type} [Fintype ι]
    (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure UnitInterval, ∀ n, (∫ t, (t:ℝ)^n ∂(μ : Measure UnitInterval)) =
      evenPacket c (fun m i j => g ![x i-x j+(m:ℤ), x i-x j-(m:ℤ), y i-y j]) n :=
  hausdorff_moments _ (diagonal_evenPacket_completeMonotone hg c x y)

#print axioms diagonal_evenPacket_spectrum

end IsingScaling.Packet
