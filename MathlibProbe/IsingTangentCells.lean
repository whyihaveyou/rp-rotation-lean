import MathlibProbe.IsingOffOriginPackets
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual nearest-grid cell normalization for susceptibility-scaled
two-point measures. Cells are half-open to avoid boundary ambiguities. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace IsingScaling.Packet
open IsingRotation

def gridIndex (r : ℕ) (v : Space) : Site := fun i => ⌊(r:ℝ)*v i⌋

theorem measurable_gridIndex (r : ℕ) : Measurable (gridIndex r) := by
  apply measurable_pi_iff.2
  intro i
  exact ((measurable_const.mul ((EuclideanSpace.proj i).continuous.measurable))).floor

theorem gridIndex_scaled_tendsto {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {v : ℕ → Space} {a : Space} (hv : Tendsto v atTop (𝓝 a)) :
    Tendsto (fun n => scaledSite (R n) (gridIndex (R n) (v n))) atTop (𝓝 a) := by
  have h₀ : Tendsto (fun n => (R n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hR)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro i
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.tendsto.comp hv
  have he : Tendsto (fun n => (v n) i-(R n:ℝ)⁻¹) atTop (𝓝 (a i-0)) := h.sub h₀
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using he) h
  · filter_upwards [hR.eventually_ge_atTop 1] with n hn
    have hr : 0 < (R n:ℝ) := by exact_mod_cast (show 0 < R n by omega)
    change (v n) i-(R n:ℝ)⁻¹ ≤ (⌊(R n:ℝ)*(v n) i⌋:ℝ)/(R n:ℝ)
    rw [le_div_iff₀ hr, sub_mul, inv_mul_cancel₀ hr.ne']
    linarith [Int.lt_floor_add_one ((R n:ℝ)*(v n) i), mul_comm ((v n) i) (R n:ℝ)]
  · filter_upwards [hR.eventually_ge_atTop 1] with n hn
    have hr : 0 < (R n:ℝ) := by exact_mod_cast (show 0 < R n by omega)
    change (⌊(R n:ℝ)*(v n) i⌋:ℝ)/(R n:ℝ) ≤ (v n) i
    rw [div_le_iff₀ hr, mul_comm]
    exact Int.floor_le _

/-- Every grid index has the same Lebesgue mass r⁻³. -/
theorem gridIndex_volume (r : ℕ) (hr : 0<r) :
    MeasurePreserving (gridIndex r) volume (ENNReal.ofReal ((r:ℝ)⁻¹^3) • Measure.count) := by
  refine ⟨measurable_gridIndex r, Measure.ext_of_singleton (fun k => ?_)⟩
  have rpos : 0<(r:ℝ) := by exact_mod_cast hr
  let I (i : Fin 3) := Ico ((k i:ℝ)/(r:ℝ)) (((k i:ℝ)+1)/(r:ℝ))
  have heq : gridIndex r ⁻¹' {k} = (@WithLp.ofLp 2 (Fin 3→ℝ)) ⁻¹' pi univ I := by
    ext v
    simp only [mem_preimage, mem_singleton_iff, funext_iff, gridIndex, Set.mem_pi, mem_univ,
      forall_const, I, mem_Ico, Int.floor_eq_iff, div_le_iff₀ rpos, lt_div_iff₀ rpos]
    simp [mul_comm]
  have hI (i : Fin 3) : volume (I i) = ENNReal.ofReal (r:ℝ)⁻¹ := by
    dsimp only [I]
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [Measure.map_apply (measurable_gridIndex r) (measurableSet_singleton k), heq,
    (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage (MeasurableSet.pi countable_univ
      (fun _ _ => measurableSet_Ico) |>.nullMeasurableSet), volume_pi_pi]
  calc
    _ = ∏ _i : Fin 3, ENNReal.ofReal (r:ℝ)⁻¹ := Finset.prod_congr rfl (fun i _ => hI i)
    _ = _ := by
      simp
      rw [← ENNReal.ofReal_pow (inv_nonneg.mpr rpos.le),inv_pow]

private def cubeStep (g : Site → ℝ) (r : ℕ) (v : Space) : ℝ :=
  (↑(cube r) : Set Site).indicator (fun k => normalization g r*g k) (gridIndex r v)

private theorem cubeStep_mass {g : Site → ℝ} (hg : ∀ k, 0 ≤ g k)
    {r : ℕ} (hr : 0<r) (hχ : 0<susceptibility g r) :
    (∫⁻ v, ‖cubeStep g r v‖ₑ) = 1 := by
  let a (k : Site) := (↑(cube r) : Set Site).indicator (fun k => normalization g r*g k) k
  have hn : 0 ≤ normalization g r := div_nonneg (by positivity) hχ.le
  have ha (k) (hk : k ∈ cube r) : 0≤normalization g r*g k := mul_nonneg hn (hg k)
  change (∫⁻ v, ‖a (gridIndex r v)‖ₑ) = _
  rw [(gridIndex_volume r hr).lintegral_comp (measurable_of_countable (f := fun k => ‖a k‖ₑ)),
    lintegral_smul_measure, smul_eq_mul, lintegral_count,
    tsum_eq_sum (s := cube r) (fun k hk => by simp [a,hk])]
  have hd : (∑ i ∈ cube r, ‖a i‖ₑ) = ENNReal.ofReal (normalization g r * susceptibility g r) := by
    rw [susceptibility,Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg ha]
    exact Finset.sum_congr rfl fun k hk => by simp [a,hk,Real.enorm_of_nonneg (ha k hk)]
  rw [hd, ← ENNReal.ofReal_mul (by positivity)]
  rw [normalization, div_mul_cancel₀ _ hχ.ne', inv_pow, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

private theorem index_in_cube {v : Space} (hv : v ∈ Metric.ball 0 1) (r : ℕ) :
    gridIndex r v ∈ cube r := by
  have h : ‖v‖ < 1 := by simpa [Metric.mem_ball,dist_zero_right] using hv
  apply Fintype.mem_piFinset.2
  intro i
  have hb := (PiLp.norm_apply_le v i).trans_lt h
  have ha := abs_lt.mp (show |v i| < 1 from hb)
  apply Finset.mem_Icc.2
  constructor
  · apply Int.le_floor.mpr
    simp only [Int.cast_neg, Int.cast_natCast]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (show 0 ≤ v i+1 by linarith [ha.1])]
  · have hh : (r:ℝ)*v i ≤ r := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (show 0 ≤ 1-v i by linarith [ha.2])]
    simpa [gridIndex] using Int.floor_le_floor hh

/-- Fatou on the unit ball controls the actual density at the contact
point using just the original susceptibility normalization. -/
theorem offOrigin_integrableOn_ball {g : Site → ℝ} (hg : ∀ k, 0 ≤ g k)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (hχ : ∀ n, 0<susceptibility g (R n))
    {f : Space → ℝ} (hsp : OffOriginLimit g R f) :
    IntegrableOn f (Metric.ball 0 1) := by
  let μ := (volume : Measure Space).restrict (Metric.ball 0 1)
  let F (n : ℕ) := cubeStep g (R n)
  have hF (n : ℕ) : Measurable (F n) :=
    (measurable_of_countable (f := (↑(cube (R n)) : Set Site).indicator
      (fun k => normalization g (R n)*g k))).comp (measurable_gridIndex _)
  have ht : ∀ᵐ v ∂μ, Tendsto (fun n => F n v) atTop (𝓝 (f v)) := by
    have hne : ∀ᵐ v : Space ∂volume, v ≠ 0 := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae hne] with v hv hn
    have hh := hsp v hn (fun n => gridIndex (R n) v) (gridIndex_scaled_tendsto hR tendsto_const_nhds)
    simpa only [F,cubeStep,indicator_of_mem (index_in_cube hv _)] using hh
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n).aestronglyMeasurable) ht, ?_⟩
  change (∫⁻ v, ‖f v‖ₑ ∂μ) < ∞
  have heq : (fun v => ‖f v‖ₑ) =ᵐ[μ] fun v => liminf (fun n => ‖F n v‖ₑ) atTop :=
    ht.mono fun v hv => hv.enorm.liminf_eq.symm
  rw [lintegral_congr_ae heq]
  apply (lintegral_liminf_le (fun n => (hF n).enorm)).trans_lt
  apply lt_of_le_of_lt (b := (1:ℝ≥0∞)) _ ENNReal.one_lt_top
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [hR.eventually_ge_atTop 1] with n hn
  exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans
    (cubeStep_mass hg (by omega) (hχ n)).le

theorem offOrigin_locallyIntegrable {g : Site → ℝ} (hg : ∀ k, 0 ≤ g k)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (hχ : ∀ n, 0<susceptibility g (R n))
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) :
    LocallyIntegrable f := by
  intro x
  by_cases hx : x=0
  · subst x
    exact ⟨_,Metric.ball_mem_nhds _ zero_lt_one, offOrigin_integrableOn_ball hg hR hχ hsp⟩
  · have hi := hf.integrableAt_nhdsWithin (μ := (volume : Measure Space))
      isOpen_compl_singleton.measurableSet hx
    rwa [isOpen_compl_singleton.nhdsWithin_eq hx] at hi

end IsingScaling.Packet
