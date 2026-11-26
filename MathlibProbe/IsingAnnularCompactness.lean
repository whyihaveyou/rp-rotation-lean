import MathlibProbe.IsingTangentCells

/-! Extraction of a common moving-site profile from compact annular
control of the lattice correlations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace IsingScaling.Packet
open IsingRotation

private theorem all_bound_of_eventual {W : ℕ → ℝ} (h : ∃ B, ∀ᶠ n in atTop, ‖W n‖≤B) :
    ∃ B, ∀ n, ‖W n‖ ≤ B := by
  obtain ⟨B,N,hN⟩ := h.imp (fun _ => eventually_atTop.1)
  refine ⟨max B 0+∑ i ∈ Finset.range N, ‖W i‖,fun n => ?_⟩
  by_cases hn : n<N
  · have hb := Finset.single_le_sum (s := Finset.range N) (f := fun i => ‖W i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hn)
    linarith [le_max_right B 0]
  · have hs : 0≤∑ i ∈ Finset.range N, ‖W i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith [hN n (le_of_not_gt hn),le_max_left B 0]

/-- A single subsequence works at all nonzero real points, including
arbitrary varying lattice sites tending to each point. -/
theorem extract_of_site_oscillation {g : Site → ℝ} {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (hval : ∀ x : Space, x ≠ 0 → ∃ B : ℝ, ∀ᶠ n in atTop,
      ‖normalization g (R n)*g (gridIndex (R n) x)‖ ≤ B)
    (hosc : ∀ x : Space, x ≠ 0 → ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ᶠ n in atTop,
      ∀ k l : Site, dist (scaledSite (R n) k) x < δ → dist (scaledSite (R n) l) x < δ →
      dist (normalization g (R n)*g k) (normalization g (R n)*g l)<ε) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ OffOriginLimit g (R ∘ u) f := by
  let X := ({0}ᶜ : Set Space)
  let : Nonempty X := ⟨⟨xyz 1 0 0,by
    intro hh
    have e := congrArg (fun s : Space => s 0) (mem_singleton_iff.mp hh)
    norm_num [xyz] at e⟩⟩
  obtain ⟨d,hd⟩ := TopologicalSpace.exists_dense_seq X
  let L (n : ℕ) (x : Space) := normalization g (R n)*g (gridIndex (R n) x)
  choose B hB using fun i : ℕ => all_bound_of_eventual (W := fun n => L n (d i).val)
    (hval _ (d i).2)
  have hK := isCompact_univ_pi (fun i => isCompact_Icc (a := -B i) (b := B i))
  obtain ⟨l,_,u,hu,hlim⟩ := hK.tendsto_subseq (x := fun n i => L n (d i).val) (by
    intro n i _
    exact abs_le.mp (hB i n))
  have hcoord (i) : Tendsto (fun j => L (u j) (d i).val) atTop (𝓝 (l i)) :=
    (tendsto_pi_nhds.1 hlim) i
  have hnear (x : Space) (hx : x≠0) {ε : ℝ} (hε : 0<ε) :
      ∃ i : ℕ, ∀ᶠ j in atTop, dist (L (u j) x) (l i) < ε := by
    obtain ⟨δ,hδ,h⟩ := hosc x hx (ε/2) (half_pos hε)
    obtain ⟨i,hdi⟩ := Metric.denseRange_iff.1 hd (⟨x,hx⟩ : X) (δ/2) (half_pos hδ)
    refine ⟨i,?_⟩
    have hr := hR.comp hu.tendsto_atTop
    have hx' := Metric.tendsto_nhds.1 (gridIndex_scaled_tendsto (v := fun _ => x) hr tendsto_const_nhds) δ hδ
    have hd' := Metric.tendsto_nhds.1 (gridIndex_scaled_tendsto (v := fun _ => (d i).val)
      hr tendsto_const_nhds) (δ/2) (half_pos hδ)
    filter_upwards [hu.tendsto_atTop.eventually h,hx',hd',Metric.tendsto_nhds.1 (hcoord i) (ε/2)
      (half_pos hε)] with j hj hxj hdj hlj
    change dist x (d i).val < δ/2 at hdi
    have hdiag : dist (d i).val x < δ/2 := (dist_comm x (d i).val) ▸ hdi
    change dist (scaledSite (R (u j)) (gridIndex (R (u j)) (d i).val)) (d i).val < δ/2 at hdj
    have hk : dist (scaledSite (R (u j)) (gridIndex (R (u j)) (d i).val)) x < δ := by
      exact (dist_triangle _ (d i).val _).trans_lt (by linarith)
    have hdist : dist (L (u j) x) (L (u j) (d i).val) < ε/2 := hj _ _ hxj hk
    exact (dist_triangle _ (L (u j) (d i).val) _).trans_lt (by linarith)
  let f x := limUnder atTop fun j => L (u j) x
  refine ⟨u,f,hu,?_⟩
  intro x hx q hq
  have hcs : CauchySeq (fun j => L (u j) x) := Metric.cauchySeq_iff.2 (by
    intro ε he
    obtain ⟨i,hi⟩ := hnear x hx (half_pos he)
    obtain ⟨M,hM⟩ := eventually_atTop.1 hi
    refine ⟨M,fun m hm n hn => ?_⟩
    exact (dist_triangle _ (l i) _).trans_lt (by linarith [hM m hm, hM n hn, dist_comm (l i) (L (u n) x)]))
  apply hcs.tendsto_limUnder.congr_dist
  apply Metric.tendsto_nhds.2
  intro ε he
  obtain ⟨δ,hδ,ho⟩ := hosc x hx ε he
  have hq₀ := gridIndex_scaled_tendsto (v:= fun _ => x) (hR.comp hu.tendsto_atTop) tendsto_const_nhds
  filter_upwards [hu.tendsto_atTop.eventually ho,Metric.tendsto_nhds.1 hq₀ δ hδ,
    Metric.tendsto_nhds.1 hq δ hδ] with j hj hj₀ hj₁
  simpa [Real.dist_eq,abs_of_nonneg (dist_nonneg (α:=ℝ))] using hj _ _ hj₀ hj₁

end IsingScaling.Packet
