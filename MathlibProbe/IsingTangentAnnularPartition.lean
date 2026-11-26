import MathlibProbe.IsingPhysicalTwoPointProfiles
import MathlibProbe.IsingPhysicalPacketIdentification
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! The spatial annuli on which estimates at infinity are used. The
unresolved choice of a constant contact mass never enters a shell:
all shell factors vanish in a neighbourhood of the origin. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff SchwartzMap ENNReal
namespace IsingScaling.Packet
open IsingRotation

/-- The cutoff is fixed in macroscopic Euclidean coordinates. -/
def spatialShellBump : ContDiffBump (0:Space) := ⟨1,2,by norm_num,by norm_num⟩

def spatialShellMother (x : Space) : ℝ :=
  spatialShellBump ((2:ℝ)⁻¹ • x) - spatialShellBump x

theorem spatialShellMother_smooth : ContDiff ℝ ∞ spatialShellMother :=
by
  have h : ContDiff ℝ ∞ (fun x : Space => (2:ℝ)⁻¹ • x) := contDiff_const_smul ((2:ℝ)⁻¹)
  exact (spatialShellBump.contDiff.comp h).sub spatialShellBump.contDiff

theorem spatialShellMother_even (x : Space) : spatialShellMother (-x) = spatialShellMother x := by
  simp only [spatialShellMother,smul_neg,ContDiffBump.neg]

theorem spatialShellMother_tsupport :
    tsupport spatialShellMother ⊆ {x : Space | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 4} := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro x hx
  change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 4
  by_contra H
  rw [not_and_or,not_le,not_le] at H
  apply hx
  rcases H with h|h
  · have h₁ : spatialShellBump x = 1 := spatialShellBump.one_of_mem_closedBall (by
      simpa [Metric.mem_closedBall,spatialShellBump] using h.le)
    have h₂ : spatialShellBump ((2:ℝ)⁻¹ • x) = 1 := spatialShellBump.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,
        abs_of_pos (show 0<(2:ℝ) by norm_num),spatialShellBump]
      linarith)
    simp only [spatialShellMother,h₁,h₂,sub_self]
  · have h₁ : spatialShellBump x = 0 := spatialShellBump.zero_of_le_dist (by
      change 2 ≤ dist x 0; rw [dist_zero_right]; linarith)
    have h₂ : spatialShellBump ((2:ℝ)⁻¹ • x) = 0 := spatialShellBump.zero_of_le_dist (by
      change 2 ≤ dist _ 0
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (show 0<(2:ℝ) by norm_num)]
      linarith)
    simp only [spatialShellMother,h₁,h₂,sub_self]

theorem spatialShellMother_compact : HasCompactSupport spatialShellMother := by
  apply (isCompact_closedBall (0:Space) 4).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  simpa [Metric.mem_closedBall] using (spatialShellMother_tsupport hx).2

def spatialShellWeight (j : ℕ) (x : Space) : ℝ := spatialShellBump (((2:ℝ)^j)⁻¹ • x)
def spatialShellInner (f : Space → ℝ) (x : Space) : ℝ := spatialShellBump x * f x
def spatialShell (f : Space → ℝ) (j : ℕ) (x : Space) : ℝ :=
  spatialShellMother (((2:ℝ)^j)⁻¹ • x) * f x

theorem spatialShellWeight_step (j : ℕ) (x : Space) :
    spatialShellMother (((2:ℝ)^j)⁻¹ • x) = spatialShellWeight (j+1) x-spatialShellWeight j x := by
  simp only [spatialShellMother,spatialShellWeight,smul_smul,pow_succ,mul_inv_rev]

theorem spatialShell_telescope (N : ℕ) (x : Space) (f : Space → ℝ) :
    spatialShellInner f x + ∑ j ∈ Finset.range N, spatialShell f j x = spatialShellWeight N x * f x := by
  induction N with
  | zero => simp [spatialShellInner,spatialShellWeight]
  | succ N ih =>
    rw [Finset.sum_range_succ,←add_assoc,ih,spatialShell,spatialShellWeight_step]
    ring

theorem spatialShellWeight_eventually (x : Space) : ∀ᶠ N : ℕ in atTop, spatialShellWeight N x = 1 := by
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually_ge_atTop ‖x‖] with N hN
  apply spatialShellBump.one_of_mem_closedBall
  change dist _ 0 ≤ 1
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (by positivity : 0<(2:ℝ)^N)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(2:ℝ)^N)).2 (by simpa using hN)

theorem OffOriginLimit.even {β g} (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {f : Space → ℝ} (hsp : OffOriginLimit g R f) (x : Space) :
    f (-x) = f x := by
  by_cases hx : x=0
  · simp [hx]
  let q (n : ℕ) := gridIndex (R n) x
  have hq : Tendsto (fun n => scaledSite (R n) (q n)) atTop (𝓝 x) :=
    gridIndex_scaled_tendsto hR tendsto_const_nhds
  have hneg (r : ℕ) (a:Site) : scaledSite r (-a) = -scaledSite r a := by
    ext i
    change (((-(a i):ℤ):ℝ)/(r:ℝ)) = -((a i:ℝ)/(r:ℝ))
    simp only [Int.cast_neg,neg_div]
  have hgn (a:Site) : g (-a)=g a := by
    have he : signedPerm (Equiv.refl _) (fun _ => true) a = -a := rfl
    simpa only [he] using freeLimit_signedPerm hg (Equiv.refl _) (fun _ => true) a
  have hq' := hsp (-x) (neg_ne_zero.mpr hx) (fun n => -q n) (by simpa only [hneg] using hq.neg)
  exact tendsto_nhds_unique (by simpa only [hgn] using hq') (hsp x hx q hq)

theorem spatialShellInner_even {f : Space → ℝ} (he : ∀ x, f (-x)=f x) (x : Space) :
    spatialShellInner f (-x)=spatialShellInner f x := by simp only [spatialShellInner,ContDiffBump.neg,he]

theorem spatialShell_even {f : Space → ℝ} (he : ∀ x, f (-x)=f x) (j : ℕ) (x : Space) :
    spatialShell f j (-x)=spatialShell f j x := by simp only [spatialShell,smul_neg,spatialShellMother_even,he]

private theorem compact_weight_integrable {f : Space → ℝ} (hL : LocallyIntegrable f)
    (w : Space → ℝ) (hw : Continuous w) (hK : HasCompactSupport w) :
    Integrable (fun x => ((w x * f x : ℝ):ℂ)) := by
  suffices H : Integrable (fun x => w x * f x) by exact H.ofReal
  apply (integrableOn_iff_integrable_of_support_subset (s:=tsupport w) ?_).1
  · simpa only [mul_comm] using (hL.integrableOn_isCompact hK).mul_continuousOn hw.continuousOn hK
  · intro x hx
    apply subset_tsupport w
    intro hzero
    exact hx (by change w x * f x = 0; rw [hzero,zero_mul])

theorem spatialShellInner_integrable {f : Space → ℝ} (hL : LocallyIntegrable f) :
    Integrable (fun x => (spatialShellInner f x:ℂ)) :=
  compact_weight_integrable hL _ spatialShellBump.continuous spatialShellBump.hasCompactSupport

theorem spatialShell_integrable {f : Space → ℝ} (hL : LocallyIntegrable f) (j : ℕ) :
    Integrable (fun x => (spatialShell f j x:ℂ)) := by
  exact compact_weight_integrable hL (fun x => spatialShellMother (((2:ℝ)^j)⁻¹ • x))
    (spatialShellMother_smooth.continuous.comp (continuous_const_smul _))
    (spatialShellMother_compact.comp_smul (by positivity : ((2:ℝ)^j)⁻¹ ≠ 0))

private theorem integral_cutoff_limit {F : Space → ℂ} (hF : Integrable F) :
    Tendsto (fun N => ∫ x, (spatialShellWeight N x:ℂ)*F x) atTop (𝓝 (∫ x, F x)) := by
  have hc (n : ℕ) : Continuous (fun x => (spatialShellWeight n x:ℂ)) :=
    Complex.continuous_ofReal.comp (spatialShellBump.continuous.comp (continuous_const_smul ((2:ℝ)^n)⁻¹))
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
    (fun n => (hc n).aestronglyMeasurable.mul hF.aestronglyMeasurable) hF.norm
  · intro n
    apply ae_of_all
    intro x
    change ‖(spatialShellWeight n x:ℂ)*F x‖ ≤ ‖F x‖
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ spatialShellWeight n x from spatialShellBump.nonneg)]
    exact mul_le_of_le_one_left (norm_nonneg _) spatialShellBump.le_one
  · apply ae_of_all
    intro x
    apply Tendsto.congr' (f₁ := fun _ => F x) _ tendsto_const_nhds
    filter_upwards [spatialShellWeight_eventually x] with n hn
    simp [hn]

/-- Dyadic decomposition of the physical integral. In addition to the
inner and annular densities this retains the exact original atom. -/
theorem spatialShell_test_partition {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    {f : Space → ℝ} (hL : LocallyIntegrable f) (hB : BoundedAwayFromOrigin f)
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hμ : μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ψ : 𝓢(Space,ℂ)) :
    Integrable ψ μ ∧ Tendsto (fun N => ((μ {0}).toReal:ℂ)*ψ 0 +
      (∫ x, (spatialShellInner f x:ℂ)*ψ x) +
      ∑ j ∈ Finset.range N, ∫ x, (spatialShell f j x:ℂ)*ψ x) atTop (𝓝 (∫ x, ψ x ∂μ)) := by
  have hF := weighted_schwartz hL hB hf ψ
  have hfin : ∀ᵐ x ∂(volume:Measure Space), ENNReal.ofReal (f x) < ⊤ := .of_forall fun _ => ENNReal.ofReal_lt_top
  have hd : Integrable ψ (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
    apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal hfin).2
    simpa only [ENNReal.toReal_ofReal (hn _),Complex.real_smul] using hF
  have ha : Integrable ψ (μ {0} • Measure.dirac (0:Space)) :=
    (integrable_dirac (by simp)).smul_measure measure_singleton_lt_top.ne
  have hv : (∫ x, ψ x ∂μ) = ((μ {0}).toReal:ℂ)*ψ 0 + ∫ x, (f x:ℂ)*ψ x := by
    conv_lhs => rw [hμ]
    rw [integral_add_measure ha hd,integral_smul_measure,integral_dirac,
      integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal hfin]
    simp only [ENNReal.toReal_ofReal (hn _),Complex.real_smul]
  refine ⟨hμ ▸ ha.add_measure hd,?_⟩
  rw [hv]
  have h := (tendsto_const_nhds (x:=((μ {0}).toReal:ℂ)*ψ 0)).add (integral_cutoff_limit hF)
  apply h.congr
  intro N
  rw [add_assoc]
  congr 1
  have hi := (spatialShellInner_integrable hL).mul_bdd ψ.continuous.aestronglyMeasurable
    (.of_forall (ψ.norm_le_seminorm ℝ))
  have hs j := (spatialShell_integrable hL j).mul_bdd ψ.continuous.aestronglyMeasurable
    (.of_forall (ψ.norm_le_seminorm ℝ))
  rw [←integral_finsetSum _ (fun j _ => hs j),←integral_add hi (integrable_finsetSum _ (fun j _ => hs j))]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have ht := congrArg (fun u : ℝ => (u:ℂ)*ψ x) (spatialShell_telescope N x f)
  simpa only [Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_mul,add_mul,Finset.sum_mul,mul_assoc]
    using ht.symm

#print axioms spatialShell_test_partition
end IsingScaling.Packet
