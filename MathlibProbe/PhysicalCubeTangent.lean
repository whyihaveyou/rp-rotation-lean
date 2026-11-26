import MathlibProbe.IsingTangentExistence
import MathlibProbe.IsingTwoPointCubeReadout
import Mathlib.Analysis.Convex.Measure

/-! Closed cube tests of actual thermodynamic two-point tangent measures. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported

namespace IsingScaling

def closedCoordinateCube (a : ℝ) : Set Space :=
  ⋂ i : Fin 3, (fun x : Space => x i) ⁻¹' Icc (-a) a

theorem isCompact_closedCoordinateCube (a : ℝ) : IsCompact (closedCoordinateCube a) := by
  let T := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have he : closedCoordinateCube a = T ⁻¹' (univ.pi fun _ => Icc (-a) a) := by
    ext x
    change (x ∈ ⋂ i : Fin 3, (fun y : Space => y i) ⁻¹' Icc (-a) a) ↔
      (T x) ∈ univ.pi (fun _ => Icc (-a) a)
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left] <;> rfl
  rw [he]
  exact T.isCompact_preimage.mpr (isCompact_univ_pi fun i => isCompact_Icc)

private theorem convex_closedCoordinateCube (a : ℝ) : Convex ℝ (closedCoordinateCube a) := by
  apply convex_iInter
  intro i x hx y hy c d hc hd hcd
  change c * x i + d * y i ∈ Icc (-a) a
  exact (convex_Icc (-a) a) hx hy hc hd hcd

/-- A positive-radius cube is a continuity set for a density together with
an arbitrary point mass at the origin. -/
theorem null_frontier_closedCoordinateCube_of_density {μ : Measure Space}
    {f : Space → ℝ}
    (hm : μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : 0 < a) : μ (frontier (closedCoordinateCube a)) = 0 := by
  have hvol : volume (frontier (closedCoordinateCube a)) = 0 :=
    (convex_closedCoordinateCube a).addHaar_frontier volume
  have ho : (0 : Space) ∈ interior (closedCoordinateCube a) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Space) ha)
    intro v hv
    simp only [closedCoordinateCube,mem_iInter,mem_preimage,mem_Icc]
    intro i
    have h := (PiLp.norm_apply_le v i).trans_lt (by simpa using hv : ‖v‖ < a)
    exact abs_le.mp h.le
  have hout : (0 : Space) ∉ frontier (closedCoordinateCube a) :=
    fun h => disjoint_interior_frontier.le_bot ⟨ho,h⟩
  have hd := withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (f x)) hvol
  conv_lhs => rw [hm]
  simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ isClosed_frontier.measurableSet,
    hout,hd]

theorem IsTwoPointTangent.null_frontier_closedCoordinateCube {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β)
    {a : ℝ} (ha : 0 < a) : μ (frontier (closedCoordinateCube a)) = 0 := by
  obtain ⟨_,_,_,_,hm,_⟩ := ht.exists_rotation_invariant_density hβ
  exact null_frontier_closedCoordinateCube_of_density hm ha

private theorem compact_open_test {K U : Set Space} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ f : C_c(Space,ℝ), ∀ (ν : Measure Space) [IsFiniteMeasureOnCompacts ν],
    ν.real K ≤ (∫ x, f x ∂ν) ∧ (ν U ≠ ⊤ → (∫ x, f x ∂ν) ≤ ν.real U) := by
  obtain ⟨g,hgK,hgc,hgU,hgr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let f : C_c(Space,ℝ) := ⟨g,hgc⟩
  refine ⟨f,?_⟩
  intro ν _
  constructor
  · rw [← integral_indicator_one hK.measurableSet]
    apply integral_mono ((continuousOn_const.integrableOn_compact hK).integrable_indicator
      hK.measurableSet) f.integrable
    intro x
    change K.indicator 1 x ≤ g x
    by_cases hx : x ∈ K
    · simp [hx, hgK hx]
    · simp [hx, (hgr x).1]
  · intro hν
    have : Fact (ν U < ⊤) := ⟨hν.lt_top⟩
    rw [← integral_indicator_one hU.measurableSet]
    apply integral_mono f.integrable (IntegrableOn.integrable_indicator integrableOn_const
      hU.measurableSet)
    intro x
    change g x ≤ U.indicator 1 x
    by_cases hx : x ∈ tsupport g
    · simp [hgU hx, (hgr x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]


/-- Portmanteau for compact continuity sets under compactly supported test convergence.
Local finiteness of the approximating measures is only required eventually. -/
theorem tendsto_real_compact_of_vague {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    {ν : ℕ → Measure Space} (hν : ∀ᶠ n in atTop, IsFiniteMeasureOnCompacts (ν n))
    (hv : ∀ f : C_c(Space,ℝ), Tendsto (fun n => ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set Space} (hK : IsCompact K) (hfront : μ (frontier K) = 0) :
    Tendsto (fun n => (ν n).real K) atTop (𝓝 (μ.real K)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha' : a < 0
    · exact Eventually.of_forall fun n => ha'.trans_le ENNReal.toReal_nonneg
    have hKi : μ (interior K) = μ K := measure_interior_of_null_frontier hfront
    have hlow : ENNReal.ofReal a < μ (interior K) := by
      rw [hKi]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt ha') hK.measure_lt_top.ne).mpr ha
    obtain ⟨T,hTi,hT,haT⟩ := isOpen_interior.exists_lt_isCompact hlow
    obtain ⟨f,hf⟩ := compact_open_test hT isOpen_interior hTi
    have hLt : a < ∫ x, f x ∂μ :=
      ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt ha') hT.measure_lt_top.ne).mp haT).trans_le
        (hf μ).1
    filter_upwards [(tendsto_order.mp (hv f)).1 a hLt,hν] with n hn hnfin
    have := hnfin
    have hfin : ν n (interior K) ≠ ⊤ :=
      ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne
    exact hn.trans_le (((hf (ν n)).2 hfin).trans (measureReal_mono interior_subset hK.measure_lt_top.ne))
  · intro b hb
    have hhigh : μ K < ENNReal.ofReal b :=
      (ENNReal.lt_ofReal_iff_toReal_lt hK.measure_lt_top.ne).mpr hb
    obtain ⟨U,hKU,hU,hUb⟩ := hK.exists_isOpen_lt_of_lt _ hhigh
    obtain ⟨f,hf⟩ := compact_open_test hK hU hKU
    have hUfin : μ U ≠ ⊤ := (hUb.trans ENNReal.ofReal_lt_top).ne
    have hLt : (∫ x, f x ∂μ) < b := ((hf μ).2 hUfin).trans_lt
      ((ENNReal.lt_ofReal_iff_toReal_lt hUfin).mp hUb)
    filter_upwards [(hv f).eventually_lt_const hLt,hν] with n hn hnfin
    have := hnfin
    exact ((hf (ν n)).1).trans_lt hn

/-- The same physical sequence as in the premise, with every fixed positive cube radius. -/
theorem IsTwoPointTangent.tendsto_real_closedCoordinateCube {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β)
    {g : Site → ℝ} {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (hv : ∀ f : C_c(Space,ℝ), Tendsto (fun n => ∫ x, f x ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ x, f x ∂μ))) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (twoPointMeasure g (R n)).real (closedCoordinateCube a))
      atTop (𝓝 (μ.real (closedCoordinateCube a))) := by
  apply tendsto_real_compact_of_vague _ hv (isCompact_closedCoordinateCube a)
    (ht.null_frontier_closedCoordinateCube hβ ha)
  exact (hR.eventually_ge_atTop 1).mono fun n h => Packet.finite_on_compacts_twoPointMeasure g h

/-- If all actual locally finite tangents assign the same mass to the s-cube, the
thermodynamic susceptibility quotient converges on the full sequence of scales. -/
theorem thermodynamic_ratio_tendsto_of_common_tangent_mass {β : ℝ} (hβ : 0 ≤ β)
    {s : ℕ} (hs : 0 < s) {M : ℝ}
    (hm : ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
      IsTwoPointTangent β μ → μ.real (observationCube s) = M) :
    Tendsto (fun r : ℕ => susceptibility (thermodynamicTwoPoint β) (s*r) /
      susceptibility (thermodynamicTwoPoint β) r) atTop (𝓝 M) := by
  apply tendsto_of_subseq_tendsto
  intro R hR
  obtain ⟨u,μ,hu,hμ,_,hv,_⟩ := exists_rotation_invariant_tangent hβ hR
  letI := hμ
  let g := thermodynamicTwoPoint β
  have hg := thermodynamicTwoPoint_isLimit hβ
  obtain ⟨hn,hχ⟩ := hg.positive_cube_mass hβ
  have hRu := hR.comp hu.tendsto_atTop
  have ht : IsTwoPointTangent β μ :=
    ⟨g, R ∘ u, hg, hn, fun j => hχ _, hRu, hv⟩
  have hc := ht.tendsto_real_closedCoordinateCube hβ hRu hv (show 0 < (s:ℝ) by exact_mod_cast hs)
  change Tendsto (fun j => (twoPointMeasure g (R (u j))).real (observationCube s))
    atTop (𝓝 (μ.real (observationCube s))) at hc
  rw [hm μ ht] at hc
  refine ⟨u, hc.congr' ?_⟩
  filter_upwards [hRu.eventually_ge_atTop 1] with j hj
  change (twoPointMeasure (thermodynamicTwoPoint β) (R (u j)) (observationCube s)).toReal = _
  change 0 < R (u j) at hj
  rw [thermodynamicTwoPoint_observationCube_mass (r := R (u j)) hβ hj s, ENNReal.toReal_ofReal
    (div_nonneg (hχ _).le (hχ _).le)]

/-- Unit cube mass persists for each locally finite actual tangent, including its
possible atom at the origin. -/
theorem IsTwoPointTangent.real_unit_cube_eq_one {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β) :
    μ.real (observationCube 1) = 1 := by
  obtain ⟨R,hR,hv⟩ := ht.realizes_thermodynamic hβ
  have hc := ht.tendsto_real_closedCoordinateCube hβ hR hv (show (0:ℝ) < ((1:ℕ):ℝ) by norm_num)
  obtain ⟨_,hχ⟩ := (thermodynamicTwoPoint_isLimit hβ).positive_cube_mass hβ
  change Tendsto (fun n => (twoPointMeasure (thermodynamicTwoPoint β) (R n)).real (observationCube 1))
    atTop (𝓝 (μ.real (observationCube 1))) at hc
  apply tendsto_nhds_unique hc
  apply Tendsto.congr' (f₁ := fun _ => (1:ℝ)) _ tendsto_const_nhds
  filter_upwards [hR.eventually_ge_atTop 1] with n hn
  change 1 = (twoPointMeasure (thermodynamicTwoPoint β) (R n) (observationCube 1)).toReal
  rw [thermodynamicTwoPoint_observationCube_mass hβ hn, one_mul, div_self (hχ _).ne']
  simp

/-- The scalar identification required for the dyadic and triadic physical cube
masses yields B1, with no separate convergence or compactness hypothesis. -/
theorem physicalB1_of_common_tangent_masses {β M₂ M₃ : ℝ} (hβ : 0 ≤ β)
    (hm₂ : ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
      IsTwoPointTangent β μ → μ.real (observationCube 2) = M₂)
    (hm₃ : ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
      IsTwoPointTangent β μ → μ.real (observationCube 3) = M₃) :
    Tendsto (fun r => susceptibility (thermodynamicTwoPoint β) (2*r) /
      susceptibility (thermodynamicTwoPoint β) r) atTop (𝓝 M₂) ∧
    Tendsto (fun r => susceptibility (thermodynamicTwoPoint β) (3*r) /
      susceptibility (thermodynamicTwoPoint β) r) atTop (𝓝 M₃) :=
  ⟨thermodynamic_ratio_tendsto_of_common_tangent_mass hβ (by decide) hm₂,
   thermodynamic_ratio_tendsto_of_common_tangent_mass hβ (by decide) hm₃⟩

#print axioms IsTwoPointTangent.null_frontier_closedCoordinateCube
#print axioms IsTwoPointTangent.real_unit_cube_eq_one
#print axioms physicalB1_of_common_tangent_masses
#print axioms IsTwoPointTangent.tendsto_real_closedCoordinateCube
#print axioms thermodynamic_ratio_tendsto_of_common_tangent_mass

end IsingScaling
