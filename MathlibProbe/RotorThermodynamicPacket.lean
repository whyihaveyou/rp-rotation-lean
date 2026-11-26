import MathlibProbe.RotorPhysicalSiteReflection
import MathlibProbe.ReflectedLatticePacket
import MathlibProbe.IsingOffOriginPackets

/-!
# Even-layer spectra of stationary free-cube sphere-spin limits

One joint subsequence of the original finite free-cube Gibbs pair functions
must converge to a stationary pair function. The proof transports the finite
site-reflection inequalities and the unit-spin bound along this subsequence.
Signed coordinate permutations conjugate the finite mirrors, giving every
cubic orientation on the same subsequence without a symmetry premise on the
limit. Existence or canonical selection of a stationary limit is separate.
-/

noncomputable section
open Finset Filter MeasureTheory
open scoped Topology InnerProductSpace
set_option maxHeartbeats 800000

namespace IsingScaling.Rotor

variable {N : ℕ}

/-- The sign convention for the displacement is first site minus second site. -/
def IsStationaryFreeCubePairLimit (θ : Measure (Spin N)) (β : ℝ)
    (radii : ℕ → ℕ) (g : Site → ℝ) : Prop :=
  ∀ x y : Site, Tendsto (fun k => SiteReflection.freePair θ β (radii k) x y)
    atTop (𝓝 (g (x - y)))

/-- The original Gibbs integrals always have a common limit along a
subsequence at all pairs simultaneously. Stationarity is an additional property. -/
theorem exists_joint_freePair_subsequence (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    (β : ℝ) (radii : ℕ → ℕ) :
    ∃ (G : Site → Site → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ x y,
      Tendsto (fun k => SiteReflection.freePair θ β (radii (φ k)) x y) atTop (𝓝 (G x y)) := by
  let f (k : ℕ) (z : Site × Site) : Set.Icc (-1:ℝ) 1 :=
    ⟨SiteReflection.freePair θ β (radii k) z.1 z.2,
      abs_le.mp (SiteReflection.abs_freePair_le_one θ β (radii k) z.1 z.2)⟩
  obtain ⟨u, φ, hφ, hu⟩ := CompactSpace.tendsto_subseq f
  refine ⟨fun x y => (u (x,y) : ℝ), φ, hφ, ?_⟩
  intro x y
  exact (continuous_subtype_val.comp (continuous_apply (x,y))).continuousAt.tendsto.comp hu

private theorem eventually_in_free_cube (radii : ℕ → ℕ) (hR : Tendsto radii atTop atTop)
    (x : Site) : ∀ᶠ k in atTop, x ∈ cube (radii k) := by
  filter_upwards [hR.eventually (eventually_ge_atTop (∑ i, (x i).natAbs))] with k hk
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  omega

private theorem signedPerm_sub' (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (x y : Site) : signedPerm p s (x - y) = signedPerm p s x - signedPerm p s y := by
  funext i
  change (if s i then -(x (p i) - y (p i)) else x (p i) - y (p i)) =
    (if s i then -x (p i) else x (p i)) - (if s i then -y (p i) else y (p i))
  cases s i <;> simp <;> omega

private theorem signedPerm_symm_sub' (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (x y : Site) : (signedPerm p s).symm (x - y) =
      (signedPerm p s).symm x - (signedPerm p s).symm y := by
  apply (signedPerm p s).injective
  rw [Equiv.apply_symm_apply, signedPerm_sub', Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem energy_reindex {L : ℕ} (e : Equiv.Perm (BoxSite L))
    (hd : ∀ x y, latticeDistance (e x) (e y) = latticeDistance x y)
    (σ τ : SiteReflection.Config N L) (hs : ∀ x, τ (e x) = σ x) :
    SiteReflection.energy τ = SiteReflection.energy σ := by
  let term (q : SiteReflection.Config N L) (x y : BoxSite L) : ℝ :=
    if latticeDistance x y = 1 then ⟪(q x).val,(q y).val⟫_ℝ else 0
  have hterm (x y : BoxSite L) : term τ (e x) (e y) = term σ x y := by
    simp only [term, hd, hs]
  change (∑ x, ∑ y, term τ x y) / 2 = (∑ x, ∑ y, term σ x y) / 2
  calc
    _ = (∑ x, ∑ y, term τ (e x) (e y)) / 2 := by
      simp_rw [fun x => Equiv.sum_comp e (term τ (e x))]
      rw [Equiv.sum_comp e (fun x => ∑ y, term τ x y)]
    _ = _ := by simp_rw [hterm]

/-- Reindexing independent site priors preserves the full Gibbs numerator
and the partition function on a centered cube. -/
theorem freePair_signedPerm (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    (β : ℝ) (L : ℕ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (a b : Site) :
    SiteReflection.freePair θ β L (signedPerm p s a) (signedPerm p s b) =
      SiteReflection.freePair θ β L a b := by
  classical
  by_cases ha : a ∈ cube L
  case neg => simp [SiteReflection.freePair, ha, (signedPerm_cube p s L a).not.mp ha]
  by_cases hb : b ∈ cube L
  case neg => simp [SiteReflection.freePair, hb, (signedPerm_cube p s L b).not.mp hb]
  let x : BoxSite L := ⟨a,ha⟩
  let y : BoxSite L := ⟨b,hb⟩
  let e : Equiv.Perm (BoxSite L) := (signedPerm p s).subtypeEquiv (signedPerm_cube p s L)
  let f : (BoxSite L → Spin N) ≃ᵐ (BoxSite L → Spin N) :=
    MeasurableEquiv.piCongrLeft (fun _ : BoxSite L => Spin N) e
  let A (v w : BoxSite L) (σ : SiteReflection.Config N L) : ℝ :=
    Real.exp (β * SiteReflection.energy σ) * ⟪(σ v).val,(σ w).val⟫_ℝ
  have hμ := measurePreserving_piCongrLeft (fun _ : BoxSite L => θ) e
  have hs (σ : SiteReflection.Config N L) (i : BoxSite L) : f σ (e i) = σ i :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : BoxSite L => Spin N) e σ i
  have hd (v w : BoxSite L) : latticeDistance (e v) (e w) = latticeDistance v w :=
    signedPerm_distance p s v w
  have he (σ : SiteReflection.Config N L) : A (e x) (e y) (f σ) = A x y σ := by
    simp only [A, energy_reindex e hd σ (f σ) (hs σ), hs]
  have hi := hμ.integral_comp' (A (e x) (e y))
  change (∫ σ, A (e x) (e y) (f σ) ∂(Measure.pi (fun _ : BoxSite L => θ))) = _ at hi
  simp_rw [he] at hi
  change SiteReflection.freePair θ β L (e x) (e y) = SiteReflection.freePair θ β L x y
  simp only [SiteReflection.freePair_inside, SiteReflection.boxCorrelation]
  exact congrArg (fun z : ℝ => z / SiteReflection.partition θ β L) hi.symm

private theorem stationary_limit_reflected_reindexed
    (P : ℕ → Site → Site → ℝ) (radii : ℕ → ℕ) (hR : Tendsto radii atTop atTop)
    {g : Site → ℝ} (hlim : ∀ x y,
      Tendsto (fun k => P (radii k) x y) atTop (𝓝 (g (x - y))))
    (hpos : ∀ {L : ℕ} (M : BoxSiteMirror L) {ι : Type} [Fintype ι]
      (x : ι → BoxSite L), (∀ i, 0 ≤ M.tip (x i)) → ∀ c : ι → ℝ,
      0 ≤ ∑ i, ∑ j, c i * c j * P L (x i) (M.refl (x j)))
    (t : Site → ℤ) (r : Site → Site) (M : ∀ L, BoxSiteMirror L)
    (ht : ∀ L (x : BoxSite L), (M L).tip x = t x)
    (hr : ∀ L (x : BoxSite L), ((M L).refl x).val = r x)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Packet.SiteReflectedPositive (fun z => g ((signedPerm p s).symm z)) t r := by
  classical
  let e := signedPerm p s
  apply Packet.siteReflectedPositive_of_tendsto
    (G := fun k x y => P (radii k) (e.symm x) (e.symm y))
  · intro x y
    rw [signedPerm_symm_sub']
    exact hlim _ _
  intro ι _ x hx c
  let y (i : ι) := e.symm (x i)
  let z (i : ι) := e.symm (r (x i))
  have hall : ∀ᶠ k in atTop, ∀ i, y i ∈ cube (radii k) :=
    Filter.eventually_all.mpr fun i => eventually_in_free_cube radii hR (y i)
  filter_upwards [hall] with k hk
  let L := radii k
  let Y (i : ι) : BoxSite L := ⟨y i, hk i⟩
  let eL : Equiv.Perm (BoxSite L) := (signedPerm p s).subtypeEquiv (signedPerm_cube p s L)
  let M' := (M L).reindex p s
  have hval (i : ι) : (eL (Y i)).val = x i := e.apply_symm_apply _
  have htip (i : ι) : 0 ≤ M'.tip (Y i) := by
    change 0 ≤ (M L).tip (eL (Y i))
    rw [ht, hval]
    exact hx i
  have hmirror (i : ι) : (M'.refl (Y i)).val = z i := by
    change e.symm (((M L).refl (eL (Y i))).val) = _
    rw [hr, hval]
  simpa only [hmirror] using hpos M' Y htip c

theorem IsStationaryFreeCubePairLimit.abs_le_one
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ} (h : IsStationaryFreeCubePairLimit θ β radii g)
    (x : Site) : |g x| ≤ 1 := by
  have hlim := (h x 0).abs
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall fun k =>
    SiteReflection.abs_freePair_le_one θ β (radii k) x 0)

theorem IsStationaryFreeCubePairLimit.even
    {θ : Measure (Spin N)} {β : ℝ} {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit θ β radii g) (x : Site) : g (-x) = g x := by
  have h₁ := h 0 x
  have h₂ := h x 0
  simp only [zero_sub] at h₁
  simp only [sub_zero] at h₂
  apply tendsto_nhds_unique h₁
  simpa only [SiteReflection.freePair_comm θ β _ 0 x] using h₂

theorem IsStationaryFreeCubePairLimit.origin
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ} (h : IsStationaryFreeCubePairLimit θ β radii g) :
    g 0 = 1 := by
  have h₀ := h 0 0
  rw [sub_self] at h₀
  apply tendsto_nhds_unique h₀
  apply tendsto_const_nhds.congr'
  filter_upwards with k
  have hmem : (0 : Site) ∈ cube (radii k) := by simp [cube, Fintype.mem_piFinset]
  exact (SiteReflection.freePair_same θ β (⟨0, hmem⟩ : BoxSite (radii k))).symm

theorem IsStationaryFreeCubePairLimit.cubic
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ} (h : IsStationaryFreeCubePairLimit θ β radii g) :
    Packet.CubicKernel g := by
  intro p s x
  let e := signedPerm p s
  have h₁ := h (e x) 0
  have h₂ := h x 0
  simp only [sub_zero] at h₁ h₂
  have heq : ∀ k, SiteReflection.freePair θ β (radii k) (e x) 0 =
      SiteReflection.freePair θ β (radii k) x 0 := by
    intro k
    simpa only [signedPerm_zero] using
      (freePair_signedPerm θ β (radii k) p s x 0)
  have h₂' : Tendsto (fun k => SiteReflection.freePair θ β (radii k) (e x) 0)
      atTop (𝓝 (g x)) := h₂.congr' (Eventually.of_forall (fun k => (heq k).symm))
  exact tendsto_nhds_unique h₁ h₂'

/-- Both physical mirror forms, including all their cubic images, hold for
the same stationary pair limit. The model dimension enters the pair in h. -/
theorem IsStationaryFreeCubePairLimit.reflected_reindexed
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ} (h : IsStationaryFreeCubePairLimit θ β radii g)
    (hR : Tendsto radii atTop atTop) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Packet.SiteReflectedPositive (fun z => g ((signedPerm p s).symm z)) (fun v => v 0)
      (signedPerm (Equiv.refl _) (fun k => decide (k = 0))) ∧
    Packet.SiteReflectedPositive (fun z => g ((signedPerm p s).symm z)) (fun v => v 0-v 1)
      (signedPerm (Equiv.swap 0 1) (fun _ => false)) := by
  have hrp {L : ℕ} (M : BoxSiteMirror L) {ι : Type} [Fintype ι]
      (x : ι → BoxSite L) (hx : ∀ i, 0 ≤ M.tip (x i)) (c : ι → ℝ) :=
    SiteReflection.freePair_reflection_positive θ β M x hx c
  constructor
  · exact stationary_limit_reflected_reindexed (SiteReflection.freePair θ β) radii hR h
      hrp
      (fun v : Site => v 0)
      (signedPerm (Equiv.refl _) (fun k => decide (k = 0)))
      (fun L => axisSiteMirror L) (fun _ _ => rfl) (fun _ _ => rfl) p s
  · exact stationary_limit_reflected_reindexed (SiteReflection.freePair θ β) radii hR h
      hrp
      (fun v : Site => v 0 - v 1)
      (signedPerm (Equiv.swap 0 1) (fun _ => false))
      (fun L => diagonalSiteMirror L) (fun _ _ => rfl) (fun _ _ => rfl) p s

/-- For any fixed integer sphere dimension with a single-site probability,
each physical even-layer packet has a positive finite Hausdorff spectrum. -/
theorem IsStationaryFreeCubePairLimit.gridPacket_spectrum
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ} (h : IsStationaryFreeCubePairLimit θ β radii g)
    (hR : Tendsto radii atTop atTop) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => g ((signedPerm p s).symm z)) c x y n := by
  obtain ⟨haxis, hdiag⟩ := h.reflected_reindexed hR p s
  exact Packet.gridPacket_spectrum_of_site_reflection
    (fun z => h.abs_le_one ((signedPerm p s).symm z))
    haxis hdiag diagonal c x y

/-- Specialization to normalized surface area on the actual unit sphere.
The nonzero dimension assumption makes this single-site prior a probability. -/
theorem surfacePrior_gridPacket_spectrum (N : ℕ) [NeZero N] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hR : Tendsto radii atTop atTop) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => g ((signedPerm p s).symm z)) c x y n :=
  h.gridPacket_spectrum hR p s diagonal c x y

theorem IsStationaryFreeCubePairLimit.normalizedPacketSource
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ} (h : IsStationaryFreeCubePairLimit θ β radii g)
    (hR : Tendsto radii atTop atTop) (R : ℕ → ℕ)
    (hχ : ∀ n, 0 < susceptibility g (R n)) : Packet.NormalizedPacketSource g R where
  moments := by
    intro d ι _ c x y
    have hperm :
        signedPerm (Equiv.refl (Fin 3)) (fun _ : Fin 3 => false) =
          Equiv.refl Site := by
      ext z i
      rfl
    simpa [hperm] using
      h.gridPacket_spectrum hR (Equiv.refl _) (fun _ => false) d c x y
  cubic := h.cubic
  cube_pos := hχ

end IsingScaling.Rotor

#print axioms IsingScaling.Rotor.IsStationaryFreeCubePairLimit.gridPacket_spectrum
#print axioms IsingScaling.Rotor.surfacePrior_gridPacket_spectrum
#print axioms IsingScaling.Rotor.exists_joint_freePair_subsequence
#print axioms IsingScaling.Rotor.IsStationaryFreeCubePairLimit.normalizedPacketSource
