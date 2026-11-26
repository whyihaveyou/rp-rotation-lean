import MathlibProbe.FourierShellDensity

/-! Fourier summation of three-dimensional annuli with bounded amplitude.
At the frequency origin a vanishing Schwartz test provides the missing
power of the radius. -/
noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology FourierTransform SchwartzMap NNReal
namespace IsingRotation.FourierShell

private lemma half_geom : Summable (fun j : ℕ => (1/2:ℝ)^j) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

private lemma prefix_eight (k : ℕ) : ∑ j ∈ Finset.range k, (8:ℝ)^j ≤ 8^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith [show (0:ℝ) ≤ 8^k by positivity]

/-- Low frequency costs the volume of the annulus. Fourth differences
give one summable power of the reciprocal annular radius. -/
theorem dyadic_volume_bound (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) {A u : ℝ}
    (hA : 0 ≤ A) (hu : 0 < u) (low : ∀ j, a j ≤ A*8^j)
    (high : ∀ j, a j ≤ A*u^4*(1/2:ℝ)^j) :
    ∑' j, a j ≤ 10*A*u^3 := by
  obtain ⟨k,huk,hku⟩ : ∃ k : ℕ, u ≤ (2:ℝ)^k ∧ (k=0 ∨ (2:ℝ)^k ≤ 2*u) := by
    by_cases h : 1 ≤ u
    · obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near h (show (1:ℝ) < 2 by norm_num)
      exact ⟨k+1,hk'.le,Or.inr (by rw [pow_succ]; linarith)⟩
    · exact ⟨0,by simpa using le_of_not_ge h, Or.inl rfl⟩
  have hs := Summable.of_nonneg_of_le ha high (half_geom.mul_left (A*u^4))
  have hp : ∑ j ∈ Finset.range k, a j ≤ 8*A*u^3 := by
    rcases hku with rfl|hk
    · simp [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hA) (pow_nonneg hu.le 3)]
    · calc
        _ ≤ ∑ j ∈ Finset.range k, A*8^j := Finset.sum_le_sum fun j _ => low j
        _ ≤ A*8^k := by rw [← Finset.mul_sum]; gcongr; exact prefix_eight k
        _ = A*((2:ℝ)^k)^3 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
        _ ≤ A*(2*u)^3 := by gcongr
        _ = _ := by ring
  have hh (j : ℕ) : a (j+k) ≤ (A*u^3)*(1/2:ℝ)^j := by
    have hsmall : u*(1/2:ℝ)^k ≤ 1 := by
      rw [one_div,inv_pow,← div_eq_mul_inv,div_le_one (by positivity)]; exact huk
    calc
      _ ≤ A*u^4*((1/2:ℝ)^j*(1/2:ℝ)^k) := by simpa only [pow_add] using high (j+k)
      _ = (A*u^3*(1/2:ℝ)^j)*(u*(1/2:ℝ)^k) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hsmall
  have ht : ∑' j, a (j+k) ≤ A*u^3*2 := by
    calc
      _ ≤ ∑' j : ℕ, (A*u^3)*(1/2:ℝ)^j :=
        ((summable_nat_add_iff k).mpr hs).tsum_le_tsum hh (half_geom.mul_left _)
      _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
                    (by norm_num)]; norm_num
  rw [← hs.sum_add_tsum_nat_add k]
  linarith

/-- A first-order zero of the test absorbs one of the three singular
powers, so this multiplier can be integrated absolutely. -/
theorem inverse_cube_test_integrable (A : ℝ) (hA : 0 ≤ A) (φ : 𝓢(V,ℂ)) (hφ : φ 0 = 0) :
    Integrable (fun p : V => (A/‖p‖^3)*‖φ p‖) := by
  let D := SchwartzMap.seminorm ℝ 0 1 φ
  have hD : 0 ≤ D := apply_nonneg _ _
  have hlip : LipschitzWith (⟨D,hD⟩ : ℝ≥0) (φ : V → ℂ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (φ.smooth 1).differentiable_one
    intro x
    change ‖fderiv ℝ (φ : V → ℂ) x‖ ≤ D
    simpa only [norm_iteratedFDeriv_one] using φ.norm_iteratedFDeriv_le_seminorm ℝ 1 x
  have hsmall (p : V) : ‖φ p‖ ≤ D*‖p‖ := by
    have h := hlip.dist_le_mul p 0
    change dist (φ p) (φ 0) ≤ D*dist p 0 at h
    simpa only [hφ, dist_zero_right] using h
  let B := Metric.ball (0:V) 1
  let b (p : V) := (A/‖p‖^3)*‖φ p‖
  have hm : Measurable b := by dsimp [b]; fun_prop
  have hpos (p : V) : 0 ≤ b p := by dsimp [b]; positivity
  have hnear : IntegrableOn b B := by
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow (C:=A*D)
      (α:=2) (by norm_num [V,Space3]) (by norm_num [V,Space3]) _ hm.aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:V))] with p hp
    rw [Real.norm_of_nonneg (hpos p),Real.rpow_neg (norm_nonneg p),Real.rpow_two]
    calc b p ≤ (A/‖p‖^3)*(D*‖p‖) := mul_le_mul_of_nonneg_left (hsmall p) (by positivity)
         _ = _ := by field_simp [norm_ne_zero_iff.mpr hp]
  have hfar : IntegrableOn b Bᶜ := by
    apply ((φ.integrable.norm.const_mul A).integrableOn (s:=Bᶜ)).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with p hp
    have hv : 1 ≤ ‖p‖ := by simpa [B,Metric.mem_ball,dist_zero_right] using hp
    rw [Real.norm_of_nonneg (hpos p)]
    exact mul_le_mul_of_nonneg_right (div_le_self hA (one_le_pow₀ hv)) (norm_nonneg _)
  simpa only [B, Set.union_compl_self, integrableOn_univ] using hnear.union hfar

/-- Fourier estimates for bounded-amplitude pieces at scale 2^j.
The high-frequency inequality may use a different normal on each
piece of a spatial partition. -/
structure VolumeShellBounds (f : ℕ → V → ℂ) (A : ℝ) : Prop where
  nonneg : 0 ≤ A
  integrable (j : ℕ) : Integrable (f j)
  low (j : ℕ) (p : V) : ‖𝓕 (f j) p‖ ≤ A*(8:ℝ)^j
  high (j : ℕ) {p : V} (hp : p ≠ 0) : ‖𝓕 (f j) p‖ ≤ (A/‖p‖^4)*(1/2:ℝ)^j

namespace VolumeShellBounds
variable {f : ℕ → V → ℂ} {A : ℝ} (h : VolumeShellBounds f A)
include h

theorem summable_norm {p : V} (hp : p ≠ 0) : Summable (fun j => ‖𝓕 (f j) p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => h.high j hp) (half_geom.mul_left _)

theorem absolute_bound {p : V} (hp : p ≠ 0) : ∑' j, ‖𝓕 (f j) p‖ ≤ 10*A/‖p‖^3 := by
  simpa only [inv_pow, ← div_eq_mul_inv] using dyadic_volume_bound (fun j => ‖𝓕 (f j) p‖)
    (fun _ => norm_nonneg _) h.nonneg (inv_pos.mpr (norm_pos_iff.mpr hp)) (fun j => h.low j p)
    (fun j => by simpa only [inv_pow, ← div_eq_mul_inv] using h.high j hp)

theorem continuousOn {U : Set V} {r : ℝ} (hr : 0 < r) (hU : ∀ p ∈ U, r ≤ ‖p‖) :
    ContinuousOn (shellDensity f) U := by
  refine continuousOn_tsum ?_ (half_geom.mul_left (A/r^4)) ?_
  · intro j
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ (E:=V)).continuous₂ (h.integrable j)).continuousOn
  · intro j p hp
    exact (h.high j (norm_pos_iff.mp (hr.trans_le (hU _ hp)))).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left h.nonneg (by positivity)
        (pow_le_pow_left₀ hr.le (hU _ hp) 4)) (by positivity))

theorem continuousOff : ContinuousOn (shellDensity f) {0}ᶜ := by
  intro p hp
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hop : IsOpen {x : V | ‖p‖/2 < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hmem : p ∈ {x : V | ‖p‖/2 < ‖x‖} := half_lt_self hn
  exact ((h.continuousOn (by positivity) (fun _ hx => le_of_lt hx)).continuousAt
    (hop.mem_nhds hmem)).continuousWithinAt

theorem tested {φ : 𝓢(V,ℂ)} (hφ : φ 0 = 0) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, ∫ x, (f j x)*(𝓕 φ) x) atTop
        (𝓝 (∫ p, shellDensity f p * φ p)) := by
  have hcont (j : ℕ) : Continuous (𝓕 (f j)) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ (E:=V)).continuous₂ (h.integrable j)
  let S (N : ℕ) (p : V) := ∑ j ∈ Finset.range N, 𝓕 (f j) p * φ p
  have hS (N : ℕ) : Continuous (S N) :=
    continuous_finsetSum _ fun j _ => (hcont j).mul φ.continuous
  have hconv : Tendsto (fun N => ∫ p, S N p) atTop (𝓝 (∫ p, shellDensity f p * φ p)) := by
    apply tendsto_integral_of_dominated_convergence (fun p : V => (10*A/‖p‖^3)*‖φ p‖)
      (fun N => (hS N).aestronglyMeasurable)
      (inverse_cube_test_integrable _ (mul_nonneg (by norm_num) h.nonneg) φ hφ)
    · intro N
      filter_upwards [volume.ae_ne (0:V)] with p hp
      calc ‖S N p‖ ≤ ∑ j ∈ Finset.range N, ‖𝓕 (f j) p*φ p‖ := norm_sum_le _ _
           _ = (∑ j ∈ Finset.range N, ‖𝓕 (f j) p‖)*‖φ p‖ := by simp [Finset.sum_mul]
           _ ≤ _ := mul_le_mul_of_nonneg_right (((h.summable_norm hp).sum_le_tsum _
             (fun _ _ => norm_nonneg _)).trans (h.absolute_bound hp)) (norm_nonneg _)
    · filter_upwards [volume.ae_ne (0:V)] with p hp
      exact (((h.summable_norm hp).of_norm.hasSum).mul_right (φ p)).tendsto_sum_nat
  convert hconv using 1
  funext N
  rw [show (∫ p, S N p) = ∑ j ∈ Finset.range N, ∫ p, 𝓕 (f j) p*φ p from
    integral_finsetSum _ (fun j _ => φ.integrable.bdd_mul (hcont j).aestronglyMeasurable
      (.of_forall (fun p => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)))]
  apply Finset.sum_congr rfl
  intro j _
  symm
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ V)
    Real.continuous_fourierChar continuous_inner (h.integrable j) φ.integrable)

end VolumeShellBounds
end IsingRotation.FourierShell
