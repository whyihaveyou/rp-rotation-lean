import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Analytic continuation of finite-volume comparisons

The inner and outer disks in the compactness argument have a strictly positive
gap. All constants are independent of the sequence index. The functions are
ordinary complex functions, so the result applies directly to differences of
finite-volume spin expectations after their compact bounds have been verified.
-/

noncomputable section

open Complex Filter Metric Set Topology
open scoped BoundedContinuousFunction NNReal

namespace IsingScaling.RotorVitali

/-- The elementary disk case of normal-family compactness. A uniform bound on
the larger disk gives a uniformly convergent subsequence on the smaller one. -/
theorem disk_normal_subsequence {F : ℕ → ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hgap : r < R)
    (holo : ∀ n, DifferentiableOn ℂ (F n) (ball c R))
    (bound : ∃ M : ℝ, ∀ n z, z ∈ closedBall c R → ‖F n z‖ ≤ M) :
    ∃ g : ℂ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => F (φ n)) g atTop (closedBall c r) := by
  classical
  obtain ⟨M, hM⟩ := bound
  have hM0 : 0 ≤ M := (norm_nonneg (F 0 c)).trans
    (hM 0 c (mem_closedBall_self (hr.le.trans hgap.le)))
  let D := closedBall c r
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hD : D ⊆ ball c R := fun _ hz => (mem_closedBall.mp hz).trans_lt hgap
  let b (n : ℕ) : D →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z => F n z, ((holo n).continuousOn.mono hD).domRestrict⟩
  let δ := R - r
  have hδ : 0 < δ := sub_pos.mpr hgap
  let K : ℝ≥0 := ⟨2 * M / δ, div_nonneg (by positivity) hδ.le⟩
  have lip (n : ℕ) : LipschitzWith K (b n) := by
    apply LipschitzWith.of_dist_le_mul
    intro v u
    change dist (F n v) (F n u) ≤ (2 * M / δ) * dist (v : ℂ) (u : ℂ)
    have hsmall : ball (u : ℂ) δ ⊆ ball c R := by
      intro w hw
      rw [mem_ball] at hw ⊢
      have hu := mem_closedBall.mp u.property
      calc dist w c ≤ dist w (u : ℂ) + dist (u : ℂ) c := dist_triangle ..
           _ < R := by dsimp [δ] at hw; linarith
    have hbound {w : ℂ} (hw : w ∈ closedBall c R) :
        dist (F n w) (F n u) ≤ 2 * M := by
      rw [dist_eq_norm]
      calc ‖F n w - F n u‖ ≤ ‖F n w‖ + ‖F n u‖ := norm_sub_le ..
           _ ≤ 2 * M := by
             have := hM n w hw
             have := hM n u (ball_subset_closedBall (hD u.property))
             linarith
    by_cases hv : (v : ℂ) ∈ ball (u : ℂ) δ
    · exact Complex.dist_le_div_mul_dist_of_mapsTo_ball ((holo n).mono hsmall)
        (fun w hw => hbound (ball_subset_closedBall (hsmall hw))) hv
    · have hdist : δ ≤ dist (v : ℂ) (u : ℂ) := le_of_not_gt hv
      calc dist (F n v) (F n u) ≤ 2 * M := hbound (ball_subset_closedBall (hD v.property))
           _ = (2 * M / δ) * δ := (div_mul_cancel₀ _ hδ.ne').symm
           _ ≤ _ := mul_le_mul_of_nonneg_left hdist (div_nonneg (by positivity) hδ.le)
  have compactRange : IsCompact (closure (range b)) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M)
      (isCompact_closedBall _ _)
    · rintro _ z ⟨n, rfl⟩
      change dist (F n z) 0 ≤ M
      simpa using hM n z (ball_subset_closedBall (hD z.property))
    · apply (LipschitzWith.uniformEquicontinuous _ K ?_).equicontinuous
      rintro ⟨_, n, rfl⟩
      exact lip n
  obtain ⟨p, _, φ, hφ, hp⟩ := compactRange.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  let g (z : ℂ) : ℂ := if hz : z ∈ D then p ⟨z,hz⟩ else 0
  refine ⟨g, φ, hφ, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hp) ε hε] with n hn
  intro z hz
  have point := BoundedContinuousFunction.dist_coe_le_dist (f := b (φ n)) (g := p)
    (⟨z,hz⟩ : D)
  have hg : g z = p ⟨z,hz⟩ := by simp [g, show z ∈ D from hz]
  change dist (g z) (F (φ n) z) < ε
  rw [hg, dist_comm]
  exact point.trans_lt hn

/-- Vitali uniqueness on a disk. Pointwise convergence on any set with a
non-isolated point in the disk suffices. -/
theorem disk_vitali_zero {F : ℕ → ℂ → ℂ} {c z₀ : ℂ} {r R : ℝ} {E : Set ℂ}
    (hr : 0 < r) (hgap : r < R)
    (holo : ∀ n, DifferentiableOn ℂ (F n) (ball c R))
    (bound : ∃ M : ℝ, ∀ n z, z ∈ closedBall c R → ‖F n z‖ ≤ M)
    (hE : E ⊆ ball c r) (hz₀ : z₀ ∈ ball c r) (hacc : z₀ ∈ closure (E \ {z₀}))
    (hzero : ∀ z ∈ E, Tendsto (fun n => F n z) atTop (𝓝 0)) :
    ∀ x ∈ ball c r, Tendsto (fun n => F n x) atTop (𝓝 0) := by
  intro x hx
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨M, hM⟩ := bound
  obtain ⟨g, φ, hφ, hlim⟩ := disk_normal_subsequence (F := fun n => F (ns n))
    hr hgap (fun n => holo (ns n)) ⟨M, fun n => hM (ns n)⟩
  have hlim' := hlim.mono ball_subset_closedBall
  have hsub : ball c r ⊆ ball c R := ball_subset_ball hgap.le
  have hag := (hlim'.tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun n => (holo (ns (φ n))).mono hsub) isOpen_ball).analyticOnNhd isOpen_ball
  have ez : ∀ z ∈ E, g z = 0 := by
    intro z hz
    exact tendsto_nhds_unique (hlim'.tendsto_at (hE hz))
      (((hzero z hz).comp hns).comp hφ.tendsto_atTop)
  have ident := hag.eqOn_zero_of_preconnected_of_mem_closure
    (convex_ball c r).isPreconnected hz₀
    (closure_mono (show E \ {z₀} ⊆ {z | g z = 0} \ {z₀} from
      fun z hz => ⟨ez z hz.1, hz.2⟩) hacc)
  refine ⟨φ, ?_⟩
  simpa only [show g x = 0 from ident hx] using hlim'.tendsto_at hx

private lemma dist_real_points (t c : ℝ) :
    dist (t : ℂ) (c : ℂ) = |t - c| := by
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The large real interval can be bounded and is independent of the target
positive field. Compact uniform bounds on the half-plane are the only
normal-family hypothesis. -/
theorem rightHalfPlane_vitali_zero {F : ℕ → ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (holo : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.re})
    (bound : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 < z.re} →
      ∃ M : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ M)
    (hlarge : ∀ t : ℝ, a < t → t < b → Tendsto (fun n => F n (t : ℂ)) atTop (𝓝 0))
    {x : ℝ} (hx : 0 < x) : Tendsto (fun n => F n (x : ℂ)) atTop (𝓝 0) := by
  let m := min a x
  let c := max b x
  let r := c - m / 2
  let R := c - m / 4
  have hm : 0 < m := lt_min ha hx
  have hma : m ≤ a := min_le_left ..
  have hmx : m ≤ x := min_le_right ..
  have hbc : b ≤ c := le_max_left ..
  have hxc : x ≤ c := le_max_right ..
  have hr : 0 < r := by dsimp only [r]; linarith
  have hgap : r < R := by dsimp only [r, R]; linarith
  have hhalf : closedBall (c : ℂ) R ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have h1 : c - z.re ≤ dist z (c : ℂ) := by
      calc c - z.re = ((c : ℂ) - z).re := by simp
           _ ≤ ‖(c : ℂ) - z‖ := Complex.re_le_norm _
           _ = dist z (c : ℂ) := by rw [dist_comm, dist_eq_norm]
    have h2 := mem_closedBall.mp hz
    change 0 < z.re
    dsimp only [R] at h2
    linarith
  have hin (t : ℝ) (hmt : m ≤ t) (htc : t ≤ c) : (t : ℂ) ∈ ball (c : ℂ) r := by
    rw [mem_ball, dist_real_points, abs_of_nonpos (sub_nonpos.mpr htc)]
    dsimp only [r]
    linarith
  let E : Set ℂ := Complex.ofReal '' Ioo a b
  have hE : E ⊆ ball (c : ℂ) r := by
    rintro z ⟨t, ht, rfl⟩
    exact hin _ (hma.trans ht.1.le) (ht.2.le.trans hbc)
  have hacc : (a : ℂ) ∈ closure (E \ {(a : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let d := min ((b - a)/2) (ε/2)
    have hd : 0 < d := lt_min (by linarith) (by linarith)
    have hdab : d ≤ (b-a)/2 := min_le_left ..
    have hde : d ≤ ε/2 := min_le_right ..
    refine ⟨((a + d : ℝ) : ℂ), ⟨⟨a+d, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩, ?_⟩
    · simp only [mem_singleton_iff, Complex.ofReal_inj]
      linarith
    · rw [dist_real_points, abs_of_nonpos (by linarith)]
      linarith
  apply disk_vitali_zero hr hgap (fun n => (holo n).mono (ball_subset_closedBall.trans hhalf))
    (bound _ (isCompact_closedBall _ _) hhalf) hE (hin a hma (hab.le.trans hbc)) hacc
    (fun z ⟨t, ht, he⟩ => he ▸ hlarge t ht.1 ht.2)
  exact hin x hmx hxc

/-- Two finite-volume exhaustions may have different functions and different
compact bounds. Vanishing of their difference on one large-field interval
propagates to each positive real field. -/
theorem rightHalfPlane_vitali_compare {F G : ℕ → ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.re})
    (hG : ∀ n, DifferentiableOn ℂ (G n) {z : ℂ | 0 < z.re})
    (bF : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 < z.re} →
      ∃ M : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ M)
    (bG : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 < z.re} →
      ∃ M : ℝ, ∀ n z, z ∈ K → ‖G n z‖ ≤ M)
    (hlarge : ∀ t : ℝ, a < t → t < b →
      Tendsto (fun n => F n (t : ℂ) - G n (t : ℂ)) atTop (𝓝 0))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => F n (x : ℂ) - G n (x : ℂ)) atTop (𝓝 0) := by
  apply rightHalfPlane_vitali_zero (F := fun n z => F n z - G n z) ha hab
    (fun n => (hF n).sub (hG n)) _ hlarge hx
  intro K hK hU
  obtain ⟨M, hM⟩ := bF K hK hU
  obtain ⟨N, hN⟩ := bG K hK hU
  exact ⟨M + N, fun n z hz => (norm_sub_le _ _).trans (add_le_add (hM n z hz) (hN n z hz))⟩

/-- Convergence on a real interval gives existence of the limit at every
positive real field. The limit on the initial interval can depend on the
field. The compactness at the single target point supplies a candidate,
and the comparison theorem identifies the whole sequence with it. -/
theorem rightHalfPlane_vitali_limit_exists {F : ℕ → ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (holo : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.re})
    (bound : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 < z.re} →
      ∃ M : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ M)
    (hlarge : ∀ t : ℝ, a < t → t < b →
      ∃ l : ℂ, Tendsto (fun n => F n (t : ℂ)) atTop (𝓝 l))
    {x : ℝ} (hx : 0 < x) :
    ∃ l : ℂ, Tendsto (fun n => F n (x : ℂ)) atTop (𝓝 l) := by
  have hsubset : {(x : ℂ)} ⊆ {z : ℂ | 0 < z.re} := singleton_subset_iff.mpr hx
  obtain ⟨M, hM⟩ := bound _ isCompact_singleton hsubset
  have hb (n : ℕ) : F n (x : ℂ) ∈ closedBall (0 : ℂ) M := by
    simpa using hM n x (mem_singleton _)
  obtain ⟨l, _, φ, hφ, hl⟩ := (isCompact_closedBall (0 : ℂ) M).tendsto_subseq hb
  have hc := rightHalfPlane_vitali_compare (F := F) (G := fun n => F (φ n)) ha hab
    holo (fun n => holo (φ n)) bound (fun K hK hU => by
      obtain ⟨C,hC⟩ := bound K hK hU
      exact ⟨C, fun n => hC (φ n)⟩) (fun t hat htb => by
        obtain ⟨lt,ht⟩ := hlarge t hat htb
        simpa using ht.sub (ht.comp hφ.tendsto_atTop)) hx
  refine ⟨l, ?_⟩
  simpa [Function.comp_def] using hc.add hl

end IsingScaling.RotorVitali
