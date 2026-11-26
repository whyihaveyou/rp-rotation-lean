import MathlibProbe.RotorThermodynamicPacket
import MathlibProbe.IsingGibbsPositivity
import MathlibProbe.RotorSphereSign
import MathlibProbe.ModelPacketLatticeCompactness

/-!
# Positivity of ferromagnetic sphere-spin correlations

Average one spin coordinate over independent sitewise reflections before
integrating the Gibbs numerator. At each fixed configuration a change of
the Ising signs replaces every amplitude by its absolute value. The other
coordinates give a constant factor and the remaining Ising pair numerator
has nonnegative couplings. Summing over the spin coordinates gives positive
cube susceptibility, including along a stationary thermodynamic subsequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped InnerProductSpace Topology CompactlySupported
namespace IsingScaling.Rotor

variable {N L : ℕ}

private def amplitudeGauge {V : Type*} (a : V → ℝ) : Equiv.Perm (V → Bool) where
  toFun ε v := if a v < 0 then !(ε v) else ε v
  invFun ε v := if a v < 0 then !(ε v) else ε v
  left_inv ε := by funext v; by_cases h : a v < 0 <;> simp [h]
  right_inv ε := by funext v; by_cases h : a v < 0 <;> simp [h]

private lemma gauge_amplitude {V : Type*} (a : V → ℝ) (ε : V → Bool) (v : V) :
    value ((amplitudeGauge a ε) v) * a v = value (ε v) * |a v| := by
  by_cases h : a v < 0
  · cases hb : ε v <;> simp [amplitudeGauge, hb, value, h, abs_of_neg h]
  · simp [amplitudeGauge, h, abs_of_nonneg (le_of_not_gt h)]

private theorem sign_sum_nonneg {V E : Type*} [Fintype V] [DecidableEq V]
    (K : Finset E) (ends : E → V × V) (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (a : V → ℝ) (x y : V) :
    0 ≤ ∑ ε : V → Bool, (value (ε x) * a x) * (value (ε y) * a y) *
      Real.exp (∑ e ∈ K, J e *
        ((value (ε (ends e).1) * a (ends e).1) *
          (value (ε (ends e).2) * a (ends e).2))) := by
  let W (ε : V → Bool) := (value (ε x) * a x) * (value (ε y) * a y) *
    Real.exp (∑ e ∈ K, J e *
      ((value (ε (ends e).1) * a (ends e).1) *
        (value (ε (ends e).2) * a (ends e).2)))
  let J' (e : E) := J e * |a (ends e).1| * |a (ends e).2|
  have hpositive := finite_pair_bond_sum_nonneg K ends J'
    (fun e => mul_nonneg (mul_nonneg (hJ e) (abs_nonneg _)) (abs_nonneg _)) x y
  change 0 ≤ ∑ ε, W ε
  rw [← Equiv.sum_comp (amplitudeGauge a) W]
  refine (mul_nonneg (mul_nonneg (abs_nonneg (a x)) (abs_nonneg (a y))) hpositive).trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  simp only [W, gauge_amplitude]
  have hs : (∑ e ∈ K, J' e * (value (ε (ends e).1) * value (ε (ends e).2))) =
      ∑ e ∈ K, J e *
        ((value (ε (ends e).1) * |a (ends e).1|) *
          (value (ε (ends e).2) * |a (ends e).2|)) := by
    apply Finset.sum_congr rfl
    intro e _
    dsimp [J']
    ring
  rw [hs]
  ring

private def signConfig {V : Type*} (flip : Spin N ≃ᵐ Spin N)
    (ε : V → Bool) (σ : V → Spin N) : V → Spin N :=
  fun v => if ε v then σ v else flip (σ v)

private theorem signConfig_preserving {V : Type*} [Fintype V]
    (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    (flip : Spin N ≃ᵐ Spin N) (hflip : MeasurePreserving flip θ θ) (ε : V → Bool) :
    MeasurePreserving (signConfig flip ε)
      (Measure.pi (fun _ : V => θ)) (Measure.pi (fun _ : V => θ)) := by
  apply measurePreserving_pi (fun _ => θ) (fun _ => θ) (f := fun v u => if ε v then u else flip u)
  intro v
  cases hb : ε v
  · simpa using hflip
  · exact MeasurePreserving.id θ

private theorem orbit_integral_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    (flip : Spin N ≃ᵐ Spin N) (hflip : MeasurePreserving flip θ θ)
    (F : (V → Spin N) → ℝ) (hF : Integrable F (Measure.pi (fun _ : V => θ)))
    (horbit : ∀ σ, 0 ≤ ∑ ε : V → Bool, F (signConfig flip ε σ)) :
    0 ≤ ∫ σ, F σ ∂(Measure.pi (fun _ : V => θ)) := by
  let μ := Measure.pi (fun _ : V => θ)
  have hp (ε : V → Bool) := signConfig_preserving θ flip hflip ε
  have hi (ε : V → Bool) : Integrable (fun σ => F (signConfig flip ε σ)) μ :=
    (hp ε).integrable_comp_of_integrable hF
  have he (ε : V → Bool) :
      (∫ σ, F (signConfig flip ε σ) ∂μ) = ∫ σ, F σ ∂μ :=
    (hp ε).hasLaw.integral_comp hF.aestronglyMeasurable
  have h0 : 0 ≤ ∫ σ, ∑ ε : V → Bool, F (signConfig flip ε σ) ∂μ := integral_nonneg horbit
  rw [integral_finsetSum _ (fun ε _ => hi ε)] at h0
  simp only [he, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h0
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast Fintype.card_pos (α := V → Bool))

private def erased (k : Fin N) (u v : Spin N) : ℝ :=
  ∑ l ∈ Finset.univ.erase k, u.val l * v.val l

private theorem signConfig_inner {V : Type*} (k : Fin N) (flip : Spin N ≃ᵐ Spin N)
    (hflip : ∀ (l : Fin N) (u : Spin N), (flip u).val l =
      if l = k then -u.val l else u.val l)
    (ε : V → Bool) (σ : V → Spin N) (v w : V) :
    ⟪(signConfig flip ε σ v).val, (signConfig flip ε σ w).val⟫_ℝ =
      erased k (σ v) (σ w) + (value (ε v) * (σ v).val k) * (value (ε w) * (σ w).val k) := by
  have hk (u : V) : (signConfig flip ε σ u).val k = value (ε u) * (σ u).val k := by
    cases h : ε u <;> simp [signConfig, h, hflip, value]
  have hother (u : V) (l : Fin N) (hl : l ≠ k) :
      (signConfig flip ε σ u).val l = (σ u).val l := by
    cases h : ε u <;> simp [signConfig, h, hflip, hl]
  rw [PiLp.inner_apply]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro l hl
    rw [Real.inner_apply, hother v l (Finset.ne_of_mem_erase hl),
      hother w l (Finset.ne_of_mem_erase hl), mul_comm]
  · rw [Real.inner_apply, hk, hk, mul_comm]

private def pairCoupling (β : ℝ) (e : BoxSite L × BoxSite L) : ℝ :=
  if latticeDistance e.1 e.2 = 1 then β / 2 else 0

private theorem energy_bonds (β : ℝ) (σ : SiteReflection.Config N L) :
    β * SiteReflection.energy σ = ∑ e : BoxSite L × BoxSite L,
      pairCoupling β e * ⟪(σ e.1).val,(σ e.2).val⟫_ℝ := by
  change β * ((∑ x : BoxSite L, ∑ y : BoxSite L, if latticeDistance x y = 1 then
      ⟪(σ x).val,(σ y).val⟫_ℝ else 0) / 2) = _
  rw [show ∀ a : ℝ, β * (a/2) = (β/2) * a by intro a; ring]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases h : latticeDistance x y = 1 <;> simp [pairCoupling, h]

private theorem continuous_energy : Continuous (SiteReflection.energy (N := N) (L := L)) := by
  change Continuous (fun σ : SiteReflection.Config N L =>
    (∑ x : BoxSite L, ∑ y : BoxSite L, if latticeDistance x y = 1 then
      ⟪(σ x).val,(σ y).val⟫_ℝ else 0) / 2)
  apply Continuous.div_const
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  by_cases h : latticeDistance x y = 1 <;> simp only [h, ↓reduceIte] <;> fun_prop

private def coordinateNumerator (β : ℝ) (k : Fin N) (v w : BoxSite L)
    (σ : SiteReflection.Config N L) : ℝ :=
  Real.exp (β * SiteReflection.energy σ) * ((σ v).val k * (σ w).val k)

private theorem coord_integrable (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    (β : ℝ) (k : Fin N) (v w : BoxSite L) :
    Integrable (coordinateNumerator β k v w) (Measure.pi (fun _ : BoxSite L => θ)) := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  apply Continuous.mul ((continuous_const.mul continuous_energy).rexp)
  fun_prop

/-- A coordinate numerator with arbitrary ferromagnetic ordered bonds. -/
private def bondCoordinate {V : Type*} [Fintype V] (J : V × V → ℝ)
    (k : Fin N) (v w : V) (σ : V → Spin N) : ℝ :=
  Real.exp (∑ e : V × V, J e * ⟪(σ e.1).val,(σ e.2).val⟫_ℝ) *
    ((σ v).val k * (σ w).val k)

private theorem bond_coordinate_orbit_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (J : V × V → ℝ) (hJ : ∀ e, 0 ≤ J e) (k : Fin N)
    (flip : Spin N ≃ᵐ Spin N) (hflip : ∀ (l : Fin N) (u : Spin N), (flip u).val l =
      if l = k then -u.val l else u.val l)
    (v w : V) (σ : V → Spin N) :
    0 ≤ ∑ ε : V → Bool, bondCoordinate J k v w (signConfig flip ε σ) := by
  let K : Finset (V × V) := Finset.univ
  let a (i : V) := (σ i).val k
  let C := ∑ e ∈ K, J e * erased k (σ e.1) (σ e.2)
  have hp := sign_sum_nonneg K id J hJ a v w
  refine (mul_nonneg (Real.exp_pos C).le hp).trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  have ha (i : V) : (signConfig flip ε σ i).val k = value (ε i) * a i := by
    cases he : ε i <;> simp [he, signConfig, hflip, a, value]
  have hE : (∑ e : V × V, J e *
      ⟪(signConfig flip ε σ e.1).val,(signConfig flip ε σ e.2).val⟫_ℝ) =
      C + ∑ e ∈ K, J e * ((value (ε e.1) * a e.1) * (value (ε e.2) * a e.2)) := by
    simp_rw [signConfig_inner k flip hflip ε σ, mul_add, Finset.sum_add_distrib]
    rfl
  simp only [bondCoordinate, hE, Real.exp_add, ha, id_eq]
  ring

private theorem coordinate_orbit_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : Fin N)
    (flip : Spin N ≃ᵐ Spin N) (hflip : ∀ (l : Fin N) (u : Spin N), (flip u).val l =
      if l = k then -u.val l else u.val l)
    (v w : BoxSite L) (σ : SiteReflection.Config N L) :
    0 ≤ ∑ ε : BoxSite L → Bool, coordinateNumerator β k v w (signConfig flip ε σ) := by
  have hJ (e : BoxSite L × BoxSite L) : 0 ≤ pairCoupling β e := by
    unfold pairCoupling
    split <;> positivity
  simpa only [coordinateNumerator,energy_bonds,bondCoordinate] using
    bond_coordinate_orbit_nonneg (pairCoupling β) hJ k flip hflip v w σ

/-- The physical zero-field sphere-product Gibbs numerator with any finite
set of ordered pair couplings. Diagonal and coincident directed bonds are
allowed. For an energy with the usual half factor take J(v,w)=H(v,w)/2. -/
theorem surface_bond_dot_numerator_nonneg (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (J : V × V → ℝ) (hJ : ∀ e, 0 ≤ J e) (v w : V) :
    0 ≤ ∫ σ : V → Spin N, Real.exp (∑ e : V × V, J e * ⟪(σ e.1).val,(σ e.2).val⟫_ℝ) *
      ⟪(σ v).val,(σ w).val⟫_ℝ ∂(Measure.pi fun _ : V => SiteReflection.surfacePrior N) := by
  classical
  let θ := SiteReflection.surfacePrior N
  have hc (k : Fin N) : Integrable (bondCoordinate J k v w) (Measure.pi fun _ : V => θ) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold bondCoordinate
    apply Continuous.mul _ (by fun_prop)
    apply Continuous.rexp
    exact continuous_finsetSum _ (fun e _ => continuous_const.mul (by fun_prop))
  have hd (σ : V → Spin N) : Real.exp (∑ e : V × V, J e * ⟪(σ e.1).val,(σ e.2).val⟫_ℝ) *
      ⟪(σ v).val,(σ w).val⟫_ℝ = ∑ k, bondCoordinate J k v w σ := by
    rw [PiLp.inner_apply (x := (σ v).val) (y := (σ w).val), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [bondCoordinate,Real.inner_apply]
  simp_rw [hd]
  rw [integral_finsetSum _ (fun k _ => hc k)]
  exact Finset.sum_nonneg fun k _ => orbit_integral_nonneg θ
    (SiteReflection.SphereSign.flipCoord k) (SiteReflection.SphereSign.flipCoord_preserving k)
    _ (hc k) (bond_coordinate_orbit_nonneg J hJ k _ (SiteReflection.SphereSign.flipCoord_apply k) v w)

/-- The product Gibbs dot correlation is nonnegative for any single-site
sphere probability invariant under each coordinate reflection. -/
theorem freePair_nonneg_of_coordinate_flips (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    (flip : Fin N → Spin N ≃ᵐ Spin N)
    (hp : ∀ k, MeasurePreserving (flip k) θ θ)
    (hf : ∀ (k l : Fin N) (u : Spin N),
      ((flip k) u).val l = if l = k then -u.val l else u.val l)
    {β : ℝ} (hβ : 0 ≤ β) (L : ℕ) (x y : Site) :
    0 ≤ SiteReflection.freePair θ β L x y := by
  classical
  by_cases hx : x ∈ cube L
  case neg => simp [SiteReflection.freePair, hx]
  by_cases hy : y ∈ cube L
  case neg => simp [SiteReflection.freePair, hy]
  let v : BoxSite L := ⟨x,hx⟩
  let w : BoxSite L := ⟨y,hy⟩
  have hdot (σ : SiteReflection.Config N L) :
      Real.exp (β * SiteReflection.energy σ) * ⟪(σ v).val,(σ w).val⟫_ℝ =
        ∑ k : Fin N, coordinateNumerator β k v w σ := by
    simp only [PiLp.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [coordinateNumerator, Real.inner_apply]
  simp only [SiteReflection.freePair, dite_eq_left hx, dite_eq_left hy, SiteReflection.boxCorrelation]
  apply div_nonneg _ (SiteReflection.partition_pos θ β L).le
  change 0 ≤ ∫ σ : SiteReflection.Config N L,
    Real.exp (β * SiteReflection.energy σ) * ⟪(σ v).val,(σ w).val⟫_ℝ
      ∂(Measure.pi (fun _ : BoxSite L => θ))
  simp_rw [hdot]
  rw [integral_finsetSum _ (fun k _ => coord_integrable θ β k v w)]
  exact sum_nonneg fun k _ => orbit_integral_nonneg θ (flip k) (hp k) _
    (coord_integrable θ β k v w) (coordinate_orbit_nonneg hβ k (flip k) (hf k) v w)

/-- Nonnegativity for the zero-field surface-area rotor on a finite free cube. -/
theorem surface_freePair_nonneg (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (L : ℕ) (x y : Site) : 0 ≤ SiteReflection.freePair (SiteReflection.surfacePrior N) β L x y :=
  freePair_nonneg_of_coordinate_flips (SiteReflection.surfacePrior N)
    SiteReflection.SphereSign.flipCoord SiteReflection.SphereSign.flipCoord_preserving
    SiteReflection.SphereSign.flipCoord_apply hβ L x y

theorem IsStationaryFreeCubePairLimit.surface_nonneg [NeZero N] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (x : Site) : 0 ≤ g x := by
  have hlim := h x 0
  rw [sub_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun k => surface_freePair_nonneg N hβ (radii k) x 0)

/-- Sharp cubes include the origin with unit dot correlation. -/
theorem IsStationaryFreeCubePairLimit.surface_susceptibility_ge_one [NeZero N] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (R : ℕ) : 1 ≤ susceptibility g R := by
  have hz : (0 : Site) ∈ cube R := by simp [cube, Fintype.mem_piFinset]
  calc
    (1 : ℝ) = g 0 := h.origin.symm
    _ ≤ susceptibility g R := Finset.single_le_sum (fun z _ => h.surface_nonneg hβ z) hz

/-- The ferromagnetic physical packet source with its susceptibility floor proved. -/
theorem IsStationaryFreeCubePairLimit.surface_normalizedPacketSource [NeZero N] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hR : Tendsto radii atTop atTop) (R : ℕ → ℕ) :
    Packet.NormalizedPacketSource g R :=
  h.normalizedPacketSource hR R (fun n => zero_lt_one.trans_le (h.surface_susceptibility_ge_one hβ (R n)))

/-- The identity mirror has every vertex on its wall. Its reflected
form is the Gibbs mean of the squared norm of a spin linear combination. -/
private def gramMirror (L : ℕ) : BoxSiteMirror L where
  tip _ := 0
  refl := Equiv.refl _
  invol _ := rfl
  wall _ _ := rfl
  neg _ := by simp
  dist _ _ := rfl
  separated _ _ h := False.elim (lt_irrefl _ h)

theorem IsStationaryFreeCubePairLimit.stationaryPositive {θ : Measure (Spin N)}
    [IsProbabilityMeasure θ] {β : ℝ} {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit θ β radii g) (hR : Tendsto radii atTop atTop) :
    SpatialEnvelope.StationaryPositive g := by
  classical
  have hf : Packet.SiteReflectedPositive g (fun _ => 0) id := by
    apply Packet.siteReflectedPositive_of_tendsto (G := fun k => SiteReflection.freePair θ β (radii k))
    · exact h
    ·
      intro ι _ x _ c
      have ha (i : ι) : ∀ᶠ k : ℕ in atTop, x i ∈ cube (radii k) := by
        filter_upwards [hR.eventually (eventually_ge_atTop
          (∑ j, ((x i) j).natAbs))] with k hk
        simp only [cube, Fintype.mem_piFinset, mem_Icc]
        intro j
        have hj := Finset.single_le_sum (f := fun t => ((x i) t).natAbs)
          (fun t _ => Nat.zero_le _) (mem_univ j)
        omega
      filter_upwards [Filter.eventually_all.mpr ha] with k hk
      exact SiteReflection.freePair_reflection_positive θ β (gramMirror (radii k))
        (fun i => ⟨x i,hk i⟩) (fun _ => le_rfl) c
  intro ι _ x c
  exact hf x (fun _ => le_rfl) c

/-- Rotation of a vague susceptibility-normalized sphere-spin pair limit
when its rescaled kernel has a spatial profile on this same subsequence. -/
theorem IsStationaryFreeCubePairLimit.surface_rotation_of_spatial_limit [NeZero N] {β : ℝ}
    {radii R : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hRadii : Tendsto radii atTop atTop) (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ)))
    {f : Space → ℝ} (hsp : Packet.OffOriginLimit g R f) (O : Space ≃ₗᵢ[ℝ] Space) :
    μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x :=
  ModelPackets.rotation_of_spatial_limit (h.surface_normalizedPacketSource hβ hRadii R)
    (h.surface_nonneg hβ) hR hv hsp O

/-- The microscopic local oscillation inequality gives one further
subsequence for the spatial profile and all rotations of the given measure. -/
theorem IsStationaryFreeCubePairLimit.surface_rotation_of_localOscillation [NeZero N] {β : ℝ}
    {radii R : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hRadii : Tendsto radii atTop atTop)
    {C : ℝ} {D r₀ : ℕ} (hC : 0 ≤ C) (hD : 2 ≤ D)
    (hosc : SpatialEnvelope.LocalOscillation g C D r₀)
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ))) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ Packet.OffOriginLimit g (R ∘ u) f ∧
      ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x :=
  ModelPackets.rotation_of_localOscillation (h.surface_normalizedPacketSource hβ hRadii R)
    (h.surface_nonneg hβ) (fun z => (le_abs_self _).trans (h.abs_le_one z))
    (h.stationaryPositive hRadii) hC hD hosc hR hv

end IsingScaling.Rotor

#print axioms IsingScaling.Rotor.freePair_nonneg_of_coordinate_flips
#print axioms IsingScaling.Rotor.surface_freePair_nonneg
#print axioms IsingScaling.Rotor.IsStationaryFreeCubePairLimit.surface_normalizedPacketSource
#print axioms IsingScaling.Rotor.IsStationaryFreeCubePairLimit.surface_rotation_of_spatial_limit
#print axioms IsingScaling.Rotor.IsStationaryFreeCubePairLimit.surface_rotation_of_localOscillation
