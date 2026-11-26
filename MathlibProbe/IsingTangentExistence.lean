import MathlibProbe.IsingPhysicalTwoPointProfiles
import MathlibProbe.IsingTangentNonzero
import MathlibProbe.IsingTwoPointRotation
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Compactness of the original untruncated lattice measures. Keeping the
entire unit-ball restriction as a finite measure accounts for any mass
concentrating at the origin. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal CompactlySupported
namespace IsingScaling.Packet

private theorem in_cube_of_scaled {r N : ℕ} (hr : 0<r) {D : ℝ} {x : Site}
    (h : ‖scaledSite r x‖ ≤ D) (hN : D*(r:ℝ) ≤ N) : x ∈ cube N := by
  apply Fintype.mem_piFinset.2
  intro i
  have hi := (PiLp.norm_apply_le (scaledSite r x) i).trans h
  change |(x i:ℝ)/(r:ℝ)| ≤ D at hi
  have hp : 0<(r:ℝ) := by exact_mod_cast hr
  rw [abs_div,abs_of_pos hp] at hi
  have hlt := abs_le.mp (((div_le_iff₀ hp).1 hi).trans hN)
  exact Finset.mem_Icc.2 ⟨by exact_mod_cast hlt.1,by exact_mod_cast hlt.2⟩

private theorem ball_mass_bound {g : Site → ℝ} {r N : ℕ} (hr : 0<r)
    {D : ℝ} (hN : D*(r:ℝ) ≤ N) :
    twoPointMeasure g r (Metric.closedBall 0 D) ≤
      ∑ k ∈ cube N, ENNReal.ofReal (g k/susceptibility g r) := by
  let S := Metric.closedBall (0:Space) D
  let a (k : Site) := ENNReal.ofReal (g k/susceptibility g r)
  have he : (twoPointMeasure g r) S = ∑' k : Site, a k * (Measure.dirac (scaledSite r k)) S := by
    rw [twoPointMeasure,Measure.sum_apply _ Metric.isClosed_closedBall.measurableSet]
    rfl
  rw [he,tsum_eq_sum (s:=cube N) (fun k hk => ?_)]
  · apply Finset.sum_le_sum
    intro k _
    by_cases hx : scaledSite r k ∈ S <;>
      simp [hx,a]
  · have hx : scaledSite r k ∉ S := fun h =>
      hk (in_cube_of_scaled hr (by simpa [S,Metric.mem_closedBall] using h) hN)
    simp [hx]

theorem finite_on_compacts_twoPointMeasure (g : Site → ℝ) {r : ℕ} (hr : 0<r) :
    IsFiniteMeasureOnCompacts (twoPointMeasure g r) := by
  constructor
  intro K hK
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn (f:=id) continuous_id.continuousOn
  have hs : K ⊆ Metric.closedBall 0 D := fun v hv => by simpa [Metric.mem_closedBall] using hD v hv
  have h := ball_mass_bound (g:=g) (N:=⌈D*(r:ℝ)⌉₊) hr (Nat.le_ceil _)
  exact ((measure_mono hs).trans h).trans_lt (ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top))

theorem unitBall_mass_twoPointMeasure {g : Site → ℝ} (hg : ∀ x,0≤g x) {r : ℕ}
    (hr : 0<r) (hχ : 0<susceptibility g r) :
    twoPointMeasure g r (Metric.closedBall 0 1) ≤ 1 := by
  have h := ball_mass_bound (g:=g) (N:=r) hr (D:=1) (by simp)
  refine h.trans ?_
  rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg (hg k) hχ.le),←Finset.sum_div]
  change ENNReal.ofReal (susceptibility g r/susceptibility g r) ≤ 1
  simp [hχ.ne']

private def innerBump : ContDiffBump (0:Space) := ⟨1/2,1,by norm_num,by norm_num⟩
private def coreLaw (g : Site → ℝ) (r : ℕ) : Measure Space :=
  (twoPointMeasure g r).withDensity (fun x => ENNReal.ofReal (innerBump x))

private theorem coreLaw_le (g : Site → ℝ) (r : ℕ) :
    coreLaw g r ≤ (twoPointMeasure g r).restrict (Metric.closedBall 0 1) := by
  rw [←withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  apply withDensity_mono (.of_forall (fun x => ?_))
  by_cases hx : x ∈ Metric.closedBall (0:Space) 1
  · simp only [indicator_of_mem hx,Pi.one_apply]
    exact ENNReal.ofReal_le_one.mpr innerBump.le_one
  · have he : innerBump x = 0 := innerBump.zero_of_le_dist (by
      change 1 ≤ dist x 0; exact le_of_lt (not_le.mp hx))
    simp [hx,he]

private theorem coreLaw_compact {g : Site → ℝ} (hg : ∀ x,0≤g x) {r : ℕ}
    (hr : 0<r) (hχ : 0<susceptibility g r) :
    coreLaw g r univ ≤ 1 ∧ coreLaw g r (Metric.closedBall 0 1)ᶜ = 0 := by
  constructor
  · exact ((coreLaw_le g r) univ).trans (by simpa using unitBall_mass_twoPointMeasure hg hr hχ)
  · apply le_antisymm _ bot_le
    exact ((coreLaw_le g r) _).trans (by rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]; simp)

private def outsideTest (φ : C_c(Space,ℝ)) : C_c(Space,ℝ) :=
  ⟨⟨fun x => φ x*(1-innerBump x),φ.continuous.mul (continuous_const.sub innerBump.continuous)⟩,
    φ.hasCompactSupport.mul_right⟩

private theorem outsideTest_away (φ : C_c(Space,ℝ)) : 0 ∉ tsupport (outsideTest φ) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [innerBump.eventuallyEq_one] with x hx
  change φ x * (1-innerBump x) = 0
  change innerBump x=1 at hx
  simp [hx]

/-- The core part is a finite, tight family on the *entire* unit ball.
The exterior part converges by the off-origin grid limit. -/
theorem OffOriginLimit.extract_vague {g : Site → ℝ} (hg : ∀ x,0≤g x)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (hpos : ∀ n,0<R n) (hχ : ∀ n,0<susceptibility g (R n))
    {f : Space → ℝ} (hsp : OffOriginLimit g R f) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (R (u n)))
        atTop (𝓝 (∫ x, φ x ∂μ)) := by
  classical
  let K := Metric.closedBall (0:Space) 1
  have H n := coreLaw_compact hg (hpos n) (hχ n)
  let η (n : ℕ) : FiniteMeasure Space :=
    ⟨coreLaw g (R n),⟨(H n).1.trans_lt (by simp)⟩⟩
  have hmem n : (η n).mass ≤ 1 ∧ (η n) Kᶜ = 0 := by
    constructor
    · change (coreLaw g (R n) univ).toNNReal ≤ 1
      exact_mod_cast ENNReal.toNNReal_mono (by simp : (1:ℝ≥0∞)≠⊤) (H n).1
    · change (coreLaw g (R n) Kᶜ).toNNReal = 0
      rw [(H n).2]; rfl
  let p (n : ℕ) : ProbabilityMeasure Space := if η n = 0 then
    ⟨Measure.dirac (0:Space),inferInstance⟩ else (η n).normalize
  have hp (n) : p n Kᶜ = 0 := by
    by_cases h : η n = 0
    · have he : p n = ⟨Measure.dirac (0:Space),inferInstance⟩ := ite_eq_left h
      rw [he]
      change ((Measure.dirac (0:Space)) Kᶜ).toNNReal = 0
      simp [K]
    · have he : p n = (η n).normalize := ite_eq_right h
      rw [he,FiniteMeasure.normalize_eq_of_nonzero _ h, (hmem n).2,mul_zero]
  have he (n) : (η n).mass • (p n).toFiniteMeasure = η n := by
    by_cases h : η n = 0
    · simp [h]
    · have he : p n = (η n).normalize := ite_eq_right h
      rw [he]
      exact (η n).self_eq_mass_smul_normalize.symm
  have hK := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (E:=Space) (u:=fun _ => 0) (K:=fun _ => K) tendsto_const_nhds
    (fun _ => isCompact_closedBall (0:Space) 1) (Or.inl inferInstance)
  obtain ⟨p₀,_,v,hv,hp₀⟩ := hK.tendsto_subseq (x:=p) (fun n _ => (hp n).le)
  obtain ⟨a,_,s,hs,ha⟩ := (isCompact_Icc (a:=(0:ℝ≥0)) (b:=1)).tendsto_subseq
    (x:=fun n => (η (v n)).mass) (fun n => ⟨bot_le,(hmem _).1⟩)
  let u := v ∘ s
  have hu := hv.comp hs
  let ν := a • p₀.toFiniteMeasure
  have hweak : Tendsto (fun n => η (u n)) atTop (𝓝 ν) := by
    have hp₁ := ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
      (hp₀.comp hs.tendsto_atTop)
    exact (ha.smul hp₁).congr (fun n => he (u n))
  let F x := max (f x) 0
  have hspF : OffOriginLimit g R F := by
    intro x hx q hq
    have hl := hsp x hx q hq
    have hp : 0 ≤ f x := ge_of_tendsto hl (Eventually.of_forall fun n =>
      mul_nonneg (div_nonneg (by positivity) (hχ n).le) (hg _))
    simpa only [F,max_eq_left hp] using hl
  let L x := (1-innerBump x)*F x
  have hfc := hspF.continuousOn hR
  have hfm := measurable_of_continuousOn_compl_singleton 0 hfc
  have hL : Measurable L := (measurable_const.sub innerBump.continuous.measurable).mul hfm
  have hLn (x) : 0 ≤ L x := mul_nonneg (sub_nonneg.mpr innerBump.le_one) (le_max_right ..)
  let ζ := volume.withDensity (fun x => ENNReal.ofReal (L x))
  have hloc := offOrigin_locallyIntegrable hg hR hχ hfc hspF
  let : IsFiniteMeasureOnCompacts ζ := ⟨fun T hT => by
    change volume.withDensity _ T < ⊤
    rw [withDensity_apply _ hT.measurableSet]
    apply lt_of_le_of_lt (lintegral_mono (f:=fun x=>ENNReal.ofReal (L x))
      (g:=fun x=>‖F x‖ₑ) (fun x => ?_)) (hloc.integrableOn_isCompact hT).hasFiniteIntegral
    exact (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (le_max_right ..) (sub_le_self _ innerBump.nonneg))).trans
      (Real.ofReal_le_enorm _)⟩
  let : IsFiniteMeasureOnCompacts ((ν : Measure Space)+ζ) := ⟨fun T hT => by
    rw [Measure.add_apply]; exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _,hT.measure_lt_top⟩⟩
  refine ⟨u,(ν : Measure Space)+ζ,hu,inferInstance,?_⟩
  intro φ
  have hin : Tendsto (fun n => ∫ x, φ x ∂coreLaw g (R (u n))) atTop (𝓝 (∫ x, φ x ∂ν)) :=
    (FiniteMeasure.continuous_integral_boundedContinuousFunction φ.toBoundedContinuousFunction).continuousAt.tendsto.comp hweak
  have hout := (offOrigin_test_tendsto hg hR hχ hfc hspF (outsideTest φ) (outsideTest_away φ)).comp hu.tendsto_atTop
  have hiζ : Integrable φ ζ := φ.integrable
  have hz : (∫ x, φ x ∂ζ) = ∫ x, F x * (outsideTest φ) x := by
    change (∫ x, φ x ∂volume.withDensity _) = _
    rw [integral_withDensity_eq_integral_toReal_smul hL.ennreal_ofReal (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hLn _),smul_eq_mul]
    apply integral_congr_ae (.of_forall (fun x => ?_))
    change (1-innerBump x)*F x*φ x = F x*(φ x*(1-innerBump x))
    ring
  rw [integral_add_measure φ.integrable hiζ,hz]
  apply (hin.add hout).congr
  intro n
  let r := R (u n)
  let m := twoPointMeasure g r
  let : IsFiniteMeasureOnCompacts m := finite_on_compacts_twoPointMeasure g (hpos (u n))
  change (∫ x, φ x ∂m.withDensity _) + (∫ x, outsideTest φ x ∂m) = _
  rw [integral_withDensity_eq_integral_toReal_smul innerBump.continuous.measurable.ennreal_ofReal
    (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal innerBump.nonneg,smul_eq_mul]
  have hb : Integrable (fun x => innerBump x * φ x) m := φ.integrable.bdd_mul
    innerBump.continuous.aestronglyMeasurable (.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg innerBump.nonneg]; exact innerBump.le_one)
  rw [←integral_add hb (outsideTest φ).integrable]
  apply integral_congr_ae (.of_forall (fun x => ?_))
  change innerBump x*φ x+φ x*(1-innerBump x)=φ x
  ring

/-- Every diverging physical scale sequence admits a locally finite
two-point tangent with a common convergent off-origin profile. -/
theorem extract_physical_tangent {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space) (f : Space → ℝ), StrictMono u ∧
      IsLocallyFiniteMeasure μ ∧ OffOriginLimit g (R ∘ u) f ∧
      ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (R (u n)))
        atTop (𝓝 (∫ x, φ x ∂μ)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hR.eventually_ge_atTop 1)
  let v (n : ℕ) := N+n
  have hv : StrictMono v := fun _ _ h => Nat.add_lt_add_left h _
  have hRv := hR.comp hv.tendsto_atTop
  obtain ⟨u,f,hu,hsp⟩ := exists_offOriginLimit hg hβ hRv
  have H : Tendsto ((R ∘ v) ∘ u) atTop atTop := hRv.comp hu.tendsto_atTop
  obtain ⟨hn,hχ⟩ := hg.positive_cube_mass hβ
  obtain ⟨w,μ,hw,hm,hlim⟩ := hsp.extract_vague hn H
    (fun n => hN _ (Nat.le_add_right N (u n))) (fun n => hχ _)
  exact ⟨(v ∘ u) ∘ w,μ,f,(hv.comp hu).comp hw,hm,hsp.subseq H hw,hlim⟩

#print axioms extract_physical_tangent
end IsingScaling.Packet

namespace IsingScaling

/-- Every prescribed sequence of diverging scales for the free cubic Ising
two-point function has a nonzero, orthogonally invariant vague limit along
a subsequence. All orthogonal maps act on the same limit measure. -/
theorem exists_rotation_invariant_tangent {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
      (∀ φ : C_c(Space, ℝ),
        Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure (thermodynamicTwoPoint β) (R (u n)))
          atTop (𝓝 (∫ x, φ x ∂μ))) ∧
      (∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ) := by
  have hg := thermodynamicTwoPoint_isLimit hβ
  obtain ⟨u, μ, _, hu, hfin, _, hlim⟩ := Packet.extract_physical_tangent hg hβ hR
  let : IsLocallyFiniteMeasure μ := hfin
  obtain ⟨hn, hχ⟩ := hg.positive_cube_mass hβ
  have ht : IsTwoPointTangent β μ :=
    ⟨thermodynamicTwoPoint β, R ∘ u, hg, hn, fun n => hχ (R (u n)),
      hR.comp hu.tendsto_atTop, hlim⟩
  exact ⟨u, μ, hu, hfin, ht.ne_zero, hlim, ht.rotation_invariant hβ⟩

#print axioms exists_rotation_invariant_tangent

/-- For every fixed compactly supported continuous test, rotating the
argument changes its susceptibility-normalized thermodynamic two-point
integral by a quantity tending to zero along all integer scales. -/
theorem thermodynamicTwoPoint_rotated_test_difference {β : ℝ} (hβ : 0 ≤ β)
    (φ : C_c(Space, ℝ)) (O : Space ≃ₗᵢ[ℝ] Space) :
    Tendsto (fun r : ℕ =>
      (∫ x, φ (O x) ∂twoPointMeasure (thermodynamicTwoPoint β) r) -
      (∫ x, φ x ∂twoPointMeasure (thermodynamicTwoPoint β) r)) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro R hR
  obtain ⟨u, μ, _, _, _, hlim, hrot⟩ := exists_rotation_invariant_tangent hβ hR
  let φO := φ.comp O.toHomeomorph.toCocompactMap
  have heq : (∫ x, φ (O x) ∂μ) = ∫ x, φ x ∂μ := by
    calc _ = ∫ x, φ x ∂μ.map O :=
          (integral_map O.continuous.aemeasurable φ.continuous.aestronglyMeasurable).symm
         _ = _ := by rw [hrot O]
  have hlimO := hlim φO
  change Tendsto (fun n =>
      ∫ x, φ (O x) ∂twoPointMeasure (thermodynamicTwoPoint β) (R (u n)))
      atTop (𝓝 (∫ x, φ (O x) ∂μ)) at hlimO
  refine ⟨u, ?_⟩
  have hd := hlimO.sub (hlim φ)
  rw [heq] at hd
  simpa only [sub_self] using hd

#print axioms thermodynamicTwoPoint_rotated_test_difference

/-- Bilinear two-point test functional obtained by evaluating two compact
tests on the same displacement variable is asymptotically orthogonally
invariant. This is a direct corollary of the kernel test statement above. -/
theorem thermodynamicTwoPoint_bilinear_test_difference {β : ℝ} (hβ : 0 ≤ β)
    (φ ψ : C_c(Space, ℝ)) (O : Space ≃ₗᵢ[ℝ] Space) :
    Tendsto (fun r : ℕ =>
      (∫ x, φ (O x) * ψ (O x) ∂twoPointMeasure (thermodynamicTwoPoint β) r) -
      (∫ x, φ x * ψ x ∂twoPointMeasure (thermodynamicTwoPoint β) r)) atTop (𝓝 0) := by
  let η : C_c(Space, ℝ) := φ * ψ
  have hη := thermodynamicTwoPoint_rotated_test_difference hβ η O
  change Tendsto (fun r : ℕ =>
      (∫ x, φ (O x) * ψ (O x) ∂twoPointMeasure (thermodynamicTwoPoint β) r) -
      (∫ x, φ x * ψ x ∂twoPointMeasure (thermodynamicTwoPoint β) r)) atTop (𝓝 0) at hη
  exact hη

#print axioms thermodynamicTwoPoint_bilinear_test_difference

end IsingScaling
