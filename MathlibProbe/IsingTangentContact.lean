import MathlibProbe.IsingTangentAperture

/-! Contact and absolutely continuous parts for the same physical
realizing scale sequence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped CompactlySupported Topology ENNReal
namespace IsingScaling.Packet

/-- Joint convergence against all moving lattice sites already implies
continuity of the limiting density off zero. This diagonal choice of
actual sites requires no spatial derivative bound on the limit. -/
theorem OffOriginLimit.continuousOn {g : Site → ℝ} {R : ℕ → ℕ} {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (hR : Tendsto R atTop atTop) : ContinuousOn f {0}ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict,continuous_iff_continuousAt]
  intro a
  apply tendsto_of_seq_tendsto
  intro v hv
  let δ (m : ℕ) := 1/((m:ℝ)+1)
  have hδ (m) : 0<δ m := by unfold δ; positivity
  let q (m j : ℕ) := gridIndex (R j) (v m).val
  have hgrid (m) : Tendsto (fun j => scaledSite (R j) (q m j)) atTop (𝓝 (v m).val) :=
    gridIndex_scaled_tendsto hR tendsto_const_nhds
  have H (m : ℕ) : ∃ N : ℕ, ∀ j ≥ N,
      dist (scaledSite (R j) (q m j)) (v m).val < δ m ∧
      dist (normalization g (R j)*g (q m j)) (f (v m).val) < δ m := by
    have l := Metric.tendsto_nhds.1 (hgrid m) _ (hδ m)
    have r := Metric.tendsto_nhds.1 (hsp (v m).val (v m).2 (q m) (hgrid m)) _ (hδ m)
    exact eventually_atTop.1 (l.and r)
  choose N hN using H
  let u (m : ℕ) := m + ∑ i ∈ Finset.range (m+1), N i
  have hu : StrictMono u := strictMono_nat_of_lt_succ (fun m => by
    change m+_ < (m+1)+∑ i ∈ Finset.range ((m+1)+1), N i
    rw [Finset.sum_range_succ (n:=m+1)]
    omega)
  have hle (m : ℕ) : N m ≤ u m := by
    unfold u
    rw [Finset.sum_range_succ]
    omega
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hga := (continuous_subtype_val.continuousAt.tendsto.comp hv).congr_dist
    (f₂ := fun m => scaledSite (R (u m)) (q m (u m)))
    (squeeze_zero (fun _ => dist_nonneg) (fun m => by
      simpa only [Function.comp_apply,dist_comm (v m).val] using (hN m (u m) (hle m)).1.le) hδlim)
  apply ((hsp.subseq hR hu) a.val a.2 (fun m => q m (u m)) hga).congr_dist
  exact squeeze_zero (fun _ => dist_nonneg) (fun m => (hN m (u m) (hle m)).2.le) hδlim

private def contactCut (n : ℕ) (v : Space) := max 0 (min 1 ((n:ℝ)*‖v‖-1))

private theorem contactCut_range (n : ℕ) (v : Space) : contactCut n v ∈ Icc 0 1 :=
  ⟨le_max_left ..,max_le zero_le_one (min_le_left ..)⟩

private def annularTest (φ : C_c(Space,ℝ)) (n : ℕ) : C_c(Space,ℝ) :=
  ⟨⟨fun v => (φ v)*contactCut n v,by unfold contactCut; fun_prop⟩,φ.hasCompactSupport.mul_right⟩

private theorem annularTest_zero (φ : C_c(Space,ℝ)) (n : ℕ) : 0 ∉ tsupport (annularTest φ n) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have h : Tendsto (fun v : Space => (n:ℝ)*‖v‖) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_norm (E := Space)).continuousAt (x:=0)).tendsto.const_mul (n:ℝ)
  filter_upwards [h.eventually_lt_const zero_lt_one] with v hv
  change φ v * max 0 (min 1 ((n:ℝ)*‖v‖-1)) = 0
  rw [max_eq_left ((min_le_right ..).trans (sub_nonpos.mpr hv.le)),mul_zero]

private theorem annularTest_measure (μ : Measure Space) [IsFiniteMeasureOnCompacts μ]
    (φ : C_c(Space,ℝ)) :
    Tendsto (fun n => ∫ v, annularTest φ n v ∂μ) atTop (𝓝 (∫ v in ({0}ᶜ : Set Space), φ v ∂μ)) := by
  rw [←integral_indicator (measurableSet_singleton (0:Space)).compl]
  apply tendsto_integral_of_dominated_convergence (fun v => ‖φ v‖)
    (fun n => (annularTest φ n).continuous.aestronglyMeasurable) φ.integrable.norm
  · intro n
    apply ae_of_all
    intro v
    change ‖φ v * contactCut n v‖ ≤ ‖φ v‖
    rw [norm_mul,show ‖contactCut n v‖=contactCut n v from abs_of_nonneg (contactCut_range n v).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (contactCut_range n v).2
  · apply ae_of_all
    intro v
    by_cases hv : v=0
    · subst v
      have hv0 (n : ℕ) : annularTest φ n (0:Space) = 0 := by
        change φ 0 * max 0 (min 1 ((n:ℝ)*‖(0:Space)‖-1)) = 0
        simp
      change Tendsto (fun n : ℕ => annularTest φ n (0:Space)) atTop
        (𝓝 (({0}ᶜ : Set Space).indicator (fun x => φ x) 0))
      simp only [hv0,indicator_of_notMem (show (0:Space) ∉ ({0}ᶜ : Set Space) by simp)]
      exact tendsto_const_nhds
    · have hv' : v ∈ ({0}ᶜ : Set Space) := hv
      rw [indicator_of_mem hv']
      apply Tendsto.congr' (f₁ := fun _ => φ v) _ tendsto_const_nhds
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (norm_pos_iff.mpr hv)
      filter_upwards [h.eventually_ge_atTop 2] with n hn
      change φ v = φ v * max 0 (min 1 ((n:ℝ)*‖v‖-1))
      rw [min_eq_left (by linarith),max_eq_right zero_le_one,mul_one]

/-- Decompose the actual vague covariance on the given common sequence.
The value assigned to f at the origin is immaterial. -/
theorem tangent_eq_contact_add_density {g : Site → ℝ} (hg : ∀ k, 0≤g k)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (hχ : ∀ n, 0<susceptibility g (R n))
    {f : Space → ℝ} (hsp : OffOriginLimit g R f)
    {μ : Measure Space} [μ.Regular] (hlim : ∀ φ : C_c(Space,ℝ),
      Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n)) atTop (𝓝 (∫ v, φ v ∂μ))) :
    μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun v => ENNReal.ofReal (f v)) := by
  let ν := volume.withDensity (fun v => ENNReal.ofReal (f v))
  have hf := hsp.continuousOn hR
  have hL := offOrigin_locallyIntegrable hg hR hχ hf hsp
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    change volume.withDensity (fun v => ENNReal.ofReal (f v)) K < ∞
    rw [withDensity_apply _ hK.measurableSet]
    exact (lintegral_mono fun v => Real.ofReal_le_enorm (f v)).trans_lt
      (hL.integrableOn_isCompact hK).hasFiniteIntegral⟩
  have hnn (v : Space) (hv : v ≠ 0) : 0≤f v := by
    have hq := hsp v hv _ (gridIndex_scaled_tendsto (v := fun _ => v) hR tendsto_const_nhds)
    apply ge_of_tendsto' hq
    intro n
    exact mul_nonneg (div_nonneg (by positivity) (hχ n).le) (hg _)
  have hInt (φ : C_c(Space,ℝ)) (h0 : 0 ∉ tsupport φ) : (∫ v, φ v ∂μ) = ∫ v, φ v ∂ν := by
    change _ = ∫ v, φ v ∂volume.withDensity (fun v => ENNReal.ofReal (f v))
    have hm : AEMeasurable (fun v => ENNReal.ofReal (f v)) volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable hL.aestronglyMeasurable.aemeasurable
    rw [integral_withDensity_eq_integral_toReal_smul₀ hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply (tendsto_nhds_unique (hlim φ) (offOrigin_test_tendsto hg hR hχ hf hsp φ h0)).trans
    apply integral_congr_ae
    have hn : ∀ᵐ v : Space ∂volume, v ≠ 0 := by simp [ae_iff]
    filter_upwards [hn] with v hv
    simp [ENNReal.toReal_ofReal (hnn v hv)]
  have hrest : μ.restrict ({0}ᶜ : Set Space) = ν.restrict {0}ᶜ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro φ
    apply tendsto_nhds_unique (annularTest_measure μ φ)
    exact (annularTest_measure ν φ).congr'
      (Eventually.of_forall fun n => (hInt _ (annularTest_zero φ n)).symm)
  have hn : ν {0} = 0 := withDensity_absolutelyContinuous _ _ (measure_singleton _)
  have hsv : ν.restrict ({0}ᶜ : Set Space) = ν := by
    simpa only [Measure.restrict_singleton,hn,zero_smul,zero_add] using
      ν.restrict_add_restrict_compl (measurableSet_singleton (0:Space))
  calc
    μ = μ.restrict {0} + μ.restrict {0}ᶜ :=
      (μ.restrict_add_restrict_compl (measurableSet_singleton (0:Space))).symm
    _ = _ := by rw [Measure.restrict_singleton,hrest,hsv]

#print axioms tangent_eq_contact_add_density
end IsingScaling.Packet
