import MathlibProbe.IsingTangentCells

/-! Compact off-origin bounds and exact testing of lattice cell densities. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported
namespace IsingScaling.Packet

/-- The sequential spatial convergence hypothesis also applies on every
strictly increasing subsequence, filling skipped indices with genuine
rounded sites converging to the *same* test point. -/
theorem OffOriginLimit.subseq {g : Site → ℝ} {R : ℕ → ℕ} {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (hR : Tendsto R atTop atTop)
    {u : ℕ → ℕ} (hu : StrictMono u) : OffOriginLimit g (R ∘ u) f := by
  classical
  intro v hv q hq
  let Q (j : ℕ) := if j ∈ range u then q (Function.invFun u j) else gridIndex (R j) v
  have hQ (n : ℕ) : Q (u n) = q n := by
    simp [Q,Function.leftInverse_invFun hu.injective n]
  have hr := gridIndex_scaled_tendsto (v := fun _ => v) hR tendsto_const_nhds
  have hfull : Tendsto (fun j => scaledSite (R j) (Q j)) atTop (𝓝 v) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₁,hn₁⟩ := Metric.tendsto_atTop.1 hq ε hε
    obtain ⟨n₂,hn₂⟩ := Metric.tendsto_atTop.1 hr ε hε
    refine ⟨max (u n₁) n₂,fun j hj => ?_⟩
    by_cases hm : j ∈ range u
    · obtain ⟨m,rfl⟩ := hm
      rw [hQ]
      exact hn₁ m (hu.le_iff_le.mp (le_of_max_le_left hj))
    · rw [show Q j = gridIndex (R j) v by simp only [Q,ite_eq_right hm]]
      exact hn₂ j (le_of_max_le_right hj)
  have hh := (hsp v hv Q hfull).comp hu.tendsto_atTop
  simpa only [Function.comp_def,hQ] using hh

/-- On every compact set disjoint from the contact point the normalized
lattice correlations have an eventual uniform bound. -/
theorem OffOriginLimit.eventually_bounded {g : Site → ℝ} {R : ℕ → ℕ} {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (hR : Tendsto R atTop atTop)
    (hf : ContinuousOn f {0}ᶜ) {K : Set Space} (hK : IsCompact K) (h0 : 0 ∉ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ k : Site, scaledSite (R n) k ∈ K →
      ‖normalization g (R n)*g k‖ ≤ B := by
  have hsub : K ⊆ {0}ᶜ := fun _ hv h => h0 (Set.mem_singleton_iff.mp h ▸ hv)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨max C 0+1,by positivity,?_⟩
  by_contra hn
  have hh : ∃ᶠ n in atTop, ∃ k, scaledSite (R n) k ∈ K ∧ max C 0+1 < ‖normalization g (R n)*g k‖ := by
    simpa only [Filter.Frequently,not_exists,not_and,not_lt] using hn
  obtain ⟨u,hu,hh⟩ := extraction_of_frequently_atTop hh
  choose q hq hbig using hh
  obtain ⟨a,ha,v,hv,hlim⟩ := hK.tendsto_subseq hq
  have hne : a≠0 := fun h => h0 (h ▸ ha)
  have hphys := (hsp.subseq hR (hu.comp hv)) a hne (q ∘ v) hlim
  have hlimbound : ‖f a‖ ≤ C := hC a ha
  obtain ⟨n,hn⟩ := (hphys.norm.eventually_lt_const
    (show ‖f a‖ < max C 0+1 by linarith [le_max_left C 0])).exists
  exact (not_lt_of_ge (hbig (v n)).le) hn

/-- Smearing each point mass uniformly over its half-open cell and
returning that cell to its lattice corner recovers the original measure
exactly, at each positive grid scale. -/
theorem map_stepDensity (g : Site → ℝ) {r : ℕ} (hr : 0<r) :
    (volume.withDensity (fun v => ENNReal.ofReal (normalization g r*g (gridIndex r v)))).map
      (fun v => scaledSite r (gridIndex r v)) = twoPointMeasure g r := by
  ext s hs
  have hm : Measurable (fun v => scaledSite r (gridIndex r v)) :=
    (measurable_of_countable (f := scaledSite r)).comp (measurable_gridIndex r)
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs),
    ←lintegral_indicator (hm hs)]
  let A := (scaledSite r ⁻¹' s).indicator (fun k => ENNReal.ofReal (normalization g r*g k))
  change (∫⁻ v, A (gridIndex r v)) = _
  rw [(gridIndex_volume r hr).lintegral_comp (measurable_of_countable (f := A)),
    lintegral_smul_measure, smul_eq_mul, lintegral_count, ← ENNReal.tsum_mul_left,
    twoPointMeasure, Measure.sum_apply _ hs]
  apply tsum_congr
  intro k
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs,smul_eq_mul]
  by_cases h : scaledSite r k ∈ s
  · have hm : k ∈ scaledSite r ⁻¹' s := h
    simp only [A,indicator_of_mem hm,indicator_of_mem h,Pi.one_apply,mul_one]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold normalization
    field_simp [show (r:ℝ)≠0 by positivity]
  · have hm : k ∉ scaledSite r ⁻¹' s := h
    simp [A,hm,h]

/-- Exact Bochner test formula. It preserves the complete grid weights
before taking the continuum limit. -/
theorem twoPointMeasure_test_step {g : Site → ℝ} (hg : ∀ k, 0 ≤ g k) {r : ℕ}
    (hr : 0<r) (hχ : 0<susceptibility g r) (φ : Space → ℝ) (hm : Measurable φ) :
    (∫ v, φ v ∂twoPointMeasure g r) =
    ∫ v, normalization g r*g (gridIndex r v)*φ (scaledSite r (gridIndex r v)) := by
  have hA : Measurable (fun v => ENNReal.ofReal (normalization g r*g (gridIndex r v))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_of_countable (f := g)).comp (measurable_gridIndex r)))
  have hN : 0≤normalization g r := div_nonneg (by positivity) hχ.le
  have hm' : Measurable (fun v => scaledSite r (gridIndex r v)) :=
    (measurable_of_countable (f := scaledSite r)).comp (measurable_gridIndex r)
  rw [←map_stepDensity g hr,integral_map hm'.aemeasurable
    hm.aestronglyMeasurable,integral_withDensity_eq_integral_toReal_smul hA
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg hN (hg _)), smul_eq_mul]

private theorem grid_displacement_le {r : ℕ} (hr : 0<r) (v : Space) :
    ‖v-scaledSite r (gridIndex r v)‖ ≤ 2 := by
  have hp : 0 < (r:ℝ) := by exact_mod_cast hr
  have h₁ : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  let k := scaledSite r (gridIndex r v)
  have h (i : Fin 3) : 0 ≤ v i-k i ∧ v i-k i ≤ 1 := by
    change 0 ≤ v i-(⌊(r:ℝ)*v i⌋:ℝ)/(r:ℝ) ∧ v i-(⌊(r:ℝ)*v i⌋:ℝ)/(r:ℝ) ≤ 1
    have hlo := Int.floor_le ((r:ℝ)*v i)
    have hhi := Int.lt_floor_add_one ((r:ℝ)*v i)
    constructor
    · rw [sub_nonneg, div_le_iff₀ hp]
      linarith [mul_comm (v i) (r:ℝ)]
    · apply sub_le_comm.mp
      rw [le_div_iff₀ hp,sub_mul]
      linarith [mul_comm (v i) (r:ℝ)]
  have hh (i : Fin 3) : ((v-k) i)^2 ≤ 1 := by
    change (v i-k i)^2 ≤ 1
    nlinarith [sq_nonneg (v i-k i), (h i).2, mul_nonneg (h i).1 (sub_nonneg.mpr (h i).2)]
  have hall : ‖v-k‖^2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    linarith [hh 0,hh 1,hh 2]
  nlinarith [norm_nonneg (v-k)]

/-- On a compact annulus, a locally uniform lattice profile gives the
actual vague test integral of the original point masses. -/
theorem offOrigin_test_tendsto {g : Site → ℝ} (hg : ∀ k, 0≤g k)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (hχ : ∀ n, 0<susceptibility g (R n))
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (φ : C_c(Space,ℝ)) (h0 : 0 ∉ tsupport φ) :
    Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n)) atTop (𝓝 (∫ v, f v*φ v)) := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  obtain ⟨B,hB,hN⟩ := hsp.eventually_bounded hR hf hK h0
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn φ.continuous.continuousOn
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let K := Metric.closedBall (0:Space) (D+2)
  have hCK : IsCompact K := isCompact_closedBall _ _
  let bnd := K.indicator (fun _ => B * max C 0)
  let L (n : ℕ) (v : Space) := normalization g (R n)*g (gridIndex (R n) v)*
      φ (scaledSite (R n) (gridIndex (R n) v))
  have hL (n : ℕ) : Measurable (L n) :=
    (measurable_of_countable (f := fun k => normalization g (R n)*g k*φ (scaledSite (R n) k))).comp
      (measurable_gridIndex _)
  apply Tendsto.congr' (f₁ := fun n => ∫ v, L n v)
  · filter_upwards [hR.eventually_ge_atTop 1] with n hn
    exact (twoPointMeasure_test_step hg (by omega) (hχ n) _ φ.continuous.measurable).symm
  apply tendsto_integral_filter_of_dominated_convergence bnd
    (Eventually.of_forall fun n => (hL n).aestronglyMeasurable)
  · filter_upwards [hR.eventually_ge_atTop 1,hN] with n hn hB'
    apply ae_of_all
    intro v
    let w := scaledSite (R n) (gridIndex (R n) v)
    by_cases hw : w ∈ tsupport φ
    · have hv : v ∈ K := by
        change dist v 0 ≤ D+2
        rw [dist_zero_right]
        have hd : ‖w‖ ≤ D := hD w hw
        have hw' : ‖v-w‖ ≤ 2 := grid_displacement_le (by omega : 0<R n) v
        calc
          ‖v‖ = ‖(v-w)+w‖ := by rw [sub_add_cancel]
          _ ≤ ‖v-w‖+‖w‖ := norm_add_le _ _
          _ ≤ D+2 := by linarith
      change ‖normalization g (R n)*g (gridIndex (R n) v)*φ w‖ ≤ bnd v
      rw [norm_mul,show bnd v = B*max C 0 from indicator_of_mem hv _]
      exact mul_le_mul (hB' _ hw) ((hC w hw).trans (le_max_left C 0)) (norm_nonneg _) hB
    · have hh := image_eq_zero_of_notMem_tsupport hw
      change ‖_*φ w‖ ≤ K.indicator (fun _ => B*max C 0) v
      rw [hh,mul_zero,norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg hB (le_max_right _ _)) _
  · exact (integrable_indicator_iff hCK.measurableSet).2 (integrableOn_const hCK.measure_lt_top.ne)
  · have hne : ∀ᵐ v : Space ∂volume, v≠0 := by simp [ae_iff]
    filter_upwards [hne] with v hv
    have hq := gridIndex_scaled_tendsto (v := fun _ => v) hR tendsto_const_nhds
    exact (hsp v hv _ hq).mul (φ.continuous.continuousAt.tendsto.comp hq)

end IsingScaling.Packet
