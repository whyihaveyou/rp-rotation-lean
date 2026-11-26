import MathlibProbe.RotorHeisenbergFieldFinite
import Mathlib.MeasureTheory.Integral.PeakFunction

/-! # Concentration of the physical Heisenberg single-site law at high field

The reference probability is the normalized area measure on the unit
two-sphere. The pinning direction is the one used in the finite Heisenberg
cube. All fields below are dimensionless.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace IsingScaling.Rotor.HeisenbergField

private abbrev spherePrior := SiteReflection.surfacePrior 3

private def radialDistance (s : Spin 3) : ℝ := ‖s.val - firstSpin.val‖

private theorem continuous_distance : Continuous radialDistance := by
  unfold radialDistance
  fun_prop

private theorem contInt {μ : Measure (Spin 3)} [IsFiniteMeasure μ]
    {f : Spin 3 → ℝ} (hc : Continuous f) : Integrable f μ :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem coord_lt {s : Spin 3} (hs : s ≠ firstSpin) :
    s.val 0 < firstSpin.val 0 := by
  have hn : firstSpin.val - s.val ≠ 0 := by
    intro h
    exact hs (Subtype.ext (sub_eq_zero.mp h).symm)
  have H := sq_pos_of_pos (norm_pos_iff.mpr hn)
  rw [norm_sub_sq_real, mem_sphere_zero_iff_norm.mp firstSpin.property,
    mem_sphere_zero_iff_norm.mp s.property] at H
  simpa [firstSpin, EuclideanSpace.inner_single_left] using
    (show ⟪firstSpin.val, s.val⟫_ℝ < 1 by linarith)

private theorem field_integral_eq (h : ℝ) (f : Spin 3 → ℝ) :
    (∫ s, f s ∂fieldPrior h) =
    (∫ s, Real.exp (siteField h s) ∂spherePrior)⁻¹ *
      ∫ s, Real.exp (siteField h s) * f s ∂spherePrior := by
  rw [fieldPrior, integral_tilted, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [smul_eq_mul, div_eq_mul_inv]
  ring

/-- Physical single-spin concentration at integer pinning fields. -/
theorem fieldPrior_distance_nat :
    Tendsto (fun n : ℕ => ∫ s : Spin 3, ‖s.val - firstSpin.val‖ ∂fieldPrior n)
      atTop (𝓝 0) := by
  let m := (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere
  let _ : spherePrior.IsOpenPosMeasure :=
    Measure.isOpenPosMeasure_smul m (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  let c (s : Spin 3) := Real.exp (s.val 0)
  have hc : Continuous c := by unfold c; fun_prop
  have hp := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := spherePrior) (g := radialDistance) (x₀ := firstSpin) isCompact_univ
    hc.continuousOn (fun s _ hs => Real.exp_lt_exp.mpr (coord_lt hs))
    (fun s _ => (Real.exp_pos _).le) (Real.exp_pos _)
    (by simp) continuous_distance.continuousOn
  have eq (n : ℕ) (s : Spin 3) : c s ^ n = Real.exp (siteField n s) := by
    simpa [c, siteField] using (Real.exp_nat_mul (s.val 0) n).symm
  simpa only [Measure.restrict_univ, eq, smul_eq_mul, radialDistance, sub_self, norm_zero,
    field_integral_eq] using hp

private theorem partition_floor (μ : Measure (Spin 3)) [IsProbabilityMeasure μ]
    {a : Spin 3 → ℝ} (ha : Continuous a) {B : ℝ} (hB : ∀ s, |a s| ≤ B) :
    Real.exp (-B) ≤ ∫ s, Real.exp (a s) ∂μ := by
  have h := integral_mono (μ := μ) (integrable_const (Real.exp (-B))) (contInt ha.rexp)
    (fun s => Real.exp_le_exp.mpr ((abs_le.mp (hB s)).1))
  simpa using h

private theorem tilted_distance_le (μ : Measure (Spin 3)) [IsProbabilityMeasure μ]
    {a : Spin 3 → ℝ} (ha : Continuous a) {B : ℝ} (hB : ∀ s, |a s| ≤ B) :
    (∫ s, radialDistance s ∂μ.tilted a) ≤
      Real.exp (2*B) * ∫ s, radialDistance s ∂μ := by
  let Z := ∫ s, Real.exp (a s) ∂μ
  have hz : Real.exp (-B) ≤ Z := partition_floor μ ha hB
  have hzpos : 0 < Z := (Real.exp_pos _).trans_le hz
  have hratio (s) : Real.exp (a s)/Z ≤ Real.exp (2*B) := by
    rw [div_le_iff₀ hzpos]
    calc
      _ ≤ Real.exp B := Real.exp_le_exp.mpr ((abs_le.mp (hB s)).2)
      _ = Real.exp (2*B) * Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
  rw [integral_tilted, ← integral_const_mul]
  change (∫ s, (Real.exp (a s) / Z) * radialDistance s ∂μ) ≤ _
  exact integral_mono (contInt ((ha.rexp.div_const _).mul continuous_distance))
    (contInt (continuous_const.mul continuous_distance))
    (fun s => mul_le_mul_of_nonneg_right (hratio s) (norm_nonneg _))

/-- Concentration holds along all positive real fields, including nonintegral ones. -/
theorem fieldPrior_distance :
    Tendsto (fun h : ℝ => ∫ s : Spin 3, ‖s.val - firstSpin.val‖ ∂fieldPrior h)
      atTop (𝓝 0) := by
  have natLim := fieldPrior_distance_nat.comp (tendsto_nat_floor_atTop (α := ℝ))
  have scaled := natLim.const_mul (Real.exp 2)
  simp only [mul_zero, Function.comp_apply] at scaled
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => norm_nonneg _)))
    _ scaled
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
  let n := ⌊h⌋₊
  let δ := h - n
  have hδ : |δ| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hh))]
    linarith [Nat.lt_floor_add_one h]
  have add : fieldPrior h = (fieldPrior n).tilted (siteField δ) := by
    unfold fieldPrior
    rw [tilted_tilted (contInt (μ := spherePrior)
      (f := fun s => Real.exp (siteField n s)) (by unfold siteField; fun_prop))]
    congr 1
    funext s
    simp [siteField, δ]
    ring
  rw [add]
  simpa [radialDistance] using tilted_distance_le (fieldPrior n) (a := siteField δ)
    (by unfold siteField; fun_prop) (B := 1) (fun s => (abs_siteField_le δ s).trans hδ)

private theorem exp_diff_bound {x y B : ℝ} (hx : x ≤ B) (hy : y ≤ B) :
    |Real.exp x - Real.exp y| ≤ Real.exp B * |x-y| := by
  have aux {u v : ℝ} (hu : u ≤ B) (hv : v ≤ u) :
      Real.exp u - Real.exp v ≤ Real.exp B * (u-v) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v-u)) (Real.exp_pos u).le
    rw [← Real.exp_add, show u+(v-u)=v by ring] at h
    nlinarith [mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu) (sub_nonneg.mpr hv)]
  rcases le_total y x with H | H
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr H)),
      abs_of_nonneg (sub_nonneg.mpr H)]
    exact aux hx H
  · rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr H)),
      abs_of_nonneg (sub_nonneg.mpr H)]
    exact aux hy H

private def localEnergy (b : EuclideanSpace ℝ (Fin 3)) (s : Spin 3) : ℝ := ⟪b,s.val⟫_ℝ

/-- The one-site conditional with dimensionless neighbouring field vector b. -/
def singleSiteConditional (h : ℝ) (b : EuclideanSpace ℝ (Fin 3)) : Measure (Spin 3) :=
  (fieldPrior h).tilted (localEnergy b)

instance (h : ℝ) (b : EuclideanSpace ℝ (Fin 3)) :
    IsProbabilityMeasure (singleSiteConditional h b) :=
  isProbabilityMeasure_tilted (contInt (μ := fieldPrior h)
    (f := fun s => Real.exp (localEnergy b s)) (by unfold localEnergy; fun_prop))

private theorem energy_bound (b : EuclideanSpace ℝ (Fin 3)) (s : Spin 3) :
    |localEnergy b s| ≤ ‖b‖ := by
  simpa [localEnergy, mem_sphere_zero_iff_norm.mp s.property] using abs_real_inner_le_norm b s.val

/-- Uniform error for all measurable tests bounded in absolute value by one.
The unperturbed measure is the physical sphere prior tilted by h*S₀. -/
theorem conditional_readout_bound (h : ℝ) {B : ℝ} (b : EuclideanSpace ℝ (Fin 3))
    (hb : ‖b‖ ≤ B) (F : Spin 3 → ℝ) (hm : Measurable F) (hf : ∀ s, |F s| ≤ 1) :
    |(∫ s, F s ∂singleSiteConditional h b) - ∫ s, F s ∂fieldPrior h| ≤
      (2 * Real.exp (2*B) * B) * ∫ s : Spin 3, ‖s.val - firstSpin.val‖ ∂fieldPrior h := by
  let μ := fieldPrior h
  let u (s : Spin 3) := Real.exp (localEnergy b s)
  let c := u firstSpin
  let Z := ∫ s, u s ∂μ
  have he : Continuous (localEnergy b) := by unfold localEnergy; fun_prop
  have hu : Continuous u := he.rexp
  have ha s := (energy_bound b s).trans hb
  have hz : Real.exp (-B) ≤ Z := partition_floor μ he ha
  have hp : 0 < Z := (Real.exp_pos _).trans_le hz
  have hdist (s : Spin 3) : |u s - c| ≤ (Real.exp B * B) * radialDistance s := by
    have h := exp_diff_bound ((abs_le.mp (ha s)).2) ((abs_le.mp (ha firstSpin)).2)
    have hd : |localEnergy b s - localEnergy b firstSpin| ≤ B * radialDistance s := by
      unfold localEnergy radialDistance
      rw [← inner_sub_right]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    simpa only [mul_assoc] using h.trans (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
  have hcu : Continuous (fun s => u s - c) := hu.sub continuous_const
  have hfirst : (∫ s, |u s-c| ∂μ) ≤ (Real.exp B * B) * ∫ s, radialDistance s ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (contInt hcu.abs) (contInt (continuous_const.mul continuous_distance)) hdist
  have hcenter : |Z-c| ≤ ∫ s, |u s-c| ∂μ := by
    have h := abs_integral_le_integral_abs (μ := μ) (f := fun s => u s-c)
    simpa [integral_sub (contInt (μ := μ) hu) (integrable_const c), Z] using h
  have hmass : (∫ s, |u s - Z| ∂μ) ≤ 2 * ((Real.exp B * B) * ∫ s, radialDistance s ∂μ) := by
    have h := integral_mono (μ := μ) (contInt (hu.sub continuous_const).abs)
      (contInt (hcu.abs.add (continuous_const (y := |c-Z|))))
      (fun s => show |u s-Z| ≤ |u s-c|+|c-Z| from abs_sub_le _ _ _)
    change (∫ s, |u s-Z| ∂μ) ≤ ∫ s, |u s-c|+|c-Z| ∂μ at h
    rw [integral_add (contInt (μ := μ) hcu.abs) (integrable_const _),
      integral_const, probReal_univ, one_smul, abs_sub_comm c Z] at h
    linarith
  have hint : Integrable F μ := (integrable_const (μ := μ) (1 : ℝ)).mono'
    hm.aestronglyMeasurable (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hf s)
  have hmul : Integrable (fun s => (u s-Z)*F s) μ :=
    (contInt (μ := μ) (hu.sub continuous_const)).mul_bdd (c := 1) hm.aestronglyMeasurable
      (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hf s)
  have huF : Integrable (fun s => u s * F s) μ :=
    (contInt (μ := μ) hu).mul_bdd (c := 1) hm.aestronglyMeasurable
      (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hf s)
  change |(∫ s, F s ∂μ.tilted (localEnergy b)) - ∫ s, F s ∂μ| ≤ _
  rw [integral_tilted]
  change |(∫ s, u s / Z * F s ∂μ) - ∫ s, F s ∂μ| ≤ _
  have rewrite_num :
      (∫ s, u s / Z * F s ∂μ) - ∫ s, F s ∂μ =
        (∫ s, (u s-Z)*F s ∂μ) / Z := by
    have point (s) : u s / Z * F s = (u s * F s) / Z := by ring
    simp_rw [point, sub_mul]
    rw [integral_div, integral_sub huF (hint.const_mul Z), integral_const_mul]
    field_simp [hp.ne']
  rw [rewrite_num, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have hh : |∫ s, (u s-Z)*F s ∂μ| ≤ ∫ s, |u s-Z| ∂μ := by
    apply abs_integral_le_integral_abs.trans
    apply integral_mono hmul.abs (contInt (hu.sub continuous_const).abs)
    intro s
    change |(u s-Z)*F s| ≤ |u s-Z|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf s)
  refine hh.trans (hmass.trans ?_)
  have h := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ 2 * Real.exp (2*B) * B * ∫ s, radialDistance s ∂μ by
      have : 0 ≤ B := (norm_nonneg b).trans hb
      exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _))
  change _ ≤ (2 * Real.exp (2*B) * B * ∫ s, radialDistance s ∂μ) * Z
  refine le_trans (le_of_eq ?_) h
  rw [show Real.exp B = Real.exp (2*B) * Real.exp (-B) by rw [← Real.exp_add]; ring_nf]
  ring

/-- Every fixed bounded range of local fields satisfies one common estimate
as h grows, simultaneously for all bounded measurable spin probes. -/
theorem conditional_readout_uniform (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in atTop, ∀ (b : EuclideanSpace ℝ (Fin 3)), ‖b‖ ≤ B →
      ∀ (F : Spin 3 → ℝ), Measurable F → (∀ s, |F s| ≤ 1) →
        |(∫ s, F s ∂singleSiteConditional h b) - ∫ s, F s ∂fieldPrior h| < ε := by
  have T := fieldPrior_distance.const_mul (2 * Real.exp (2*B) * B)
  simp only [mul_zero] at T
  filter_upwards [T.eventually_lt_const hε] with h hh
  intro b hb F hm hf
  exact (conditional_readout_bound h b hb F hm hf).trans_lt hh

/-- The physical vector field contributed by the spins adjacent to one site. -/
def neighbourField {k : ℕ} (β : ℝ) (neighbours : Fin k → Spin 3) :
    EuclideanSpace ℝ (Fin 3) := β • ∑ j, (neighbours j).val

theorem neighbourField_bound {k : ℕ} (hk : k ≤ 6) {β : ℝ} (hβ : 0 ≤ β)
    (neighbours : Fin k → Spin 3) : ‖neighbourField β neighbours‖ ≤ 6*β := by
  rw [neighbourField, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
  have H := norm_sum_le Finset.univ (fun j => (neighbours j).val)
  simp only [fun j => mem_sphere_zero_iff_norm.mp (neighbours j).property, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at H
  have H' : (k : ℝ) ≤ 6 := by exact_mod_cast hk
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (H.trans H') hβ

/-- With k incident neighbours, this is exactly the original sphere law with
the dimensionless field plus all k nearest-neighbour bond energies. -/
theorem neighbour_conditional_eq {k : ℕ} (h β : ℝ) (a : Fin k → Spin 3) :
    singleSiteConditional h (neighbourField β a) =
      spherePrior.tilted (fun s => h * s.val 0 + ∑ j, β * ⟪(a j).val, s.val⟫_ℝ) := by
  unfold singleSiteConditional fieldPrior
  rw [tilted_tilted (contInt (μ := spherePrior)
    (f := fun s => Real.exp (siteField h s)) (by unfold siteField; fun_prop))]
  congr 1
  funext s
  simp [siteField, localEnergy, neighbourField, real_inner_smul_left, sum_inner, Finset.mul_sum]

/-- Any two environments of degree at most six have indistinguishable
single-site conditionals at high field, uniformly in the measurable probe.
Taking ε < 1/6 in particular gives a strict six-neighbour influence bound. -/
theorem six_neighbour_readouts_eventually_close {β : ℝ} (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in atTop, ∀ (k l : ℕ), k ≤ 6 → l ≤ 6 →
      ∀ (a : Fin k → Spin 3) (b : Fin l → Spin 3) (F : Spin 3 → ℝ),
        Measurable F → (∀ s, |F s| ≤ 1) →
        |(∫ s, F s ∂singleSiteConditional h (neighbourField β a)) -
          ∫ s, F s ∂singleSiteConditional h (neighbourField β b)| < ε := by
  filter_upwards [conditional_readout_uniform (6*β) (ε/2) (by positivity)] with h H
  intro k l hk hl a b F hm hf
  have ha := H _ (neighbourField_bound hk hβ a) F hm hf
  have hb := H _ (neighbourField_bound hl hβ b) F hm hf
  rw [abs_sub_comm] at hb
  exact (abs_sub_le _ (∫ s, F s ∂fieldPrior h) _).trans_lt (by linarith [add_lt_add ha hb])

#print axioms fieldPrior_distance
#print axioms neighbour_conditional_eq
#print axioms six_neighbour_readouts_eventually_close

end IsingScaling.Rotor.HeisenbergField
