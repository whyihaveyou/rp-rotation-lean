import MathlibProbe.RotorPeriodicMirrorLift
import MathlibProbe.ModelPacketPhysicalRotation
import MathlibProbe.RawLatticeAngularReadout
import MathlibProbe.RotorPhysicalProfileSymmetry
import MathlibProbe.RotorPeriodicHorizontalAction
import MathlibProbe.RotorPeriodicFerromagneticPair

/-! # One nearest-neighbour rotor Gibbs law and its original two-point packets

Fix a positive auxiliary strength δ. Choose growing *even* ordinary tori
and one weak limit of their entire spin laws at the physical interaction
J(β,δ), together with a representing probability on the momentum torus.
This choice precedes every signed mirror test. The coordinate site and
bond forms pass down precisely this subsequence. To prove the remaining
diagonal form, approximate minus its horizontal group average by the
Fourier multiplier of an admissible lattice interaction derivative.
The pressure comparison supplies an adapted spin law along this
direction, on which the same actual diagonal form is nonnegative.
The two momentum probabilities each cost at most the uniform approximation
error. Spatial symmetries of the finite Gibbs laws identify the integrated
group averages with the initial real tests on both sides.

Take a subsequence of these full cubic spin laws as δ decreases to zero.
Every finite signed mirror form is a continuous spin cylinder, so all
three inequalities hold for the common limiting law. The interactions
converge in lattice ℓ¹ to the six nearest-neighbour couplings; convergence
of the local specifications gives that same law the nearest-neighbour
DLR equations. Conjugating the diagonal mirror by one coordinate sign
change yields the packet normal (1,-1,0). All readouts below keep the
original dot pair and its own cube susceptibility.
-/

noncomputable section
open scoped Topology ENNReal InnerProductSpace
open MeasureTheory Filter Finset
namespace IsingScaling.Rotor.PressureSelection.PhysicalMirrorSelection
open PeriodicMirrorLift IsingRotation Packet
open LatticeWalk PhysicalVariations PeriodicCouplingMixture

/-- Literal physical mirror geometries on the displacement variable. -/
structure ThreeMirrors (g : Site → ℝ) : Prop where
  axis : SiteReflectedPositive g (fun z => z 0) PeriodicMirrorLift.axis
  diagonal : SiteReflectedPositive g (fun z => z 0+z 1) PeriodicMirrorLift.diagonal
  bond : RawLatticeOscillation.AxialBondForm g

theorem ThreeMirrors.of_pair_limit {g : ℕ → Site → ℝ} {f : Site → ℝ}
    (hg : ∀ n, ThreeMirrors (g n)) (hf : ∀ z, Tendsto (fun n => g n z) atTop (𝓝 (f z))) :
    ThreeMirrors f := by
  have hform {v : Site → ℤ} {r : Site → Site} (h : ∀ n, SiteReflectedPositive (g n) v r) :
      SiteReflectedPositive f v r := by
    apply siteReflectedPositive_of_tendsto (G:=fun n x y => g n (x-y)) (fun x y => hf (x-y))
    intro ι _ x hx c
    exact Eventually.of_forall (fun n => h n x hx c)
  constructor
  · intro ι _ x hx c
    exact hform (v:=fun z => z 0) (r:=PeriodicMirrorLift.axis) (fun n => (hg n).axis) x hx c
  · intro ι _ x hx c
    exact hform (v:=fun z => z 0+z 1) (r:=PeriodicMirrorLift.diagonal) (fun n => (hg n).diagonal) x hx c
  · intro ι _ x hx c
    exact hform (v:=fun z => z 0-1) (r:=PeriodicMirrorLift.bond) (fun n => (hg n).bond) x hx c

private def flip (z : Site) : Site := ![z 0,-z 1,z 2]

private theorem flip_eq (z : Site) :
    flip z=signedPerm (Equiv.refl _) (fun i => decide (i=1)) z := by
  funext i; fin_cases i <;> rfl

private theorem flip_sub_diagonal (x y : Site) :
    flip x-PeriodicMirrorLift.diagonal (flip y)=flip (x-NormalDifference.refl .faceDiagonal y) := by
  ext i
  fin_cases i <;> simp [flip,PeriodicMirrorLift.diagonal,NormalDifference.refl] <;> omega

theorem ThreeMirrors.normalForms {g : Site → ℝ} (h : ThreeMirrors g) (hc : CubicKernel g)
    (d : PacketNormal) :
    SiteReflectedPositive g (NormalDifference.tip d) (NormalDifference.refl d) := by
  cases d with
  | axis => exact h.axis
  | faceDiagonal =>
    intro ι _ x hx v
    have hh := h.diagonal (fun i => flip (x i)) (fun i => by
      change 0≤x i 0 + -x i 1
      simpa only [NormalDifference.tip,sub_eq_add_neg] using hx i) v
    have he (i j : ι) :
        g (flip (x i)-PeriodicMirrorLift.diagonal (flip (x j))) =
          g (x i-NormalDifference.refl .faceDiagonal (x j)) := by
      rw [flip_sub_diagonal,flip_eq,hc]
    simpa only [he] using hh

theorem ThreeMirrors.packetForms {g : Site → ℝ} (h : ThreeMirrors g) (hc : CubicKernel g)
    (d : Bool) :
    SiteReflectedPositive g (ParitySmoothing.tip d) (ParitySmoothing.reflection d) := by
  cases d
  · have he : ParitySmoothing.reflection false=NormalDifference.refl .axis := by
      funext z i; fin_cases i <;> rfl
    rw [he]
    intro ι _ x hx c
    exact h.normalForms hc .axis x hx c
  · have he : ParitySmoothing.reflection true=NormalDifference.refl .faceDiagonal := by
      funext z i; fin_cases i <;> rfl
    rw [he]
    intro ι _ x hx c
    exact h.normalForms hc .faceDiagonal x hx c

theorem pair_bound {N : ℕ} (P : ProbabilityMeasure (SpinField N)) (z : Site) :
    |fieldPair P z|≤1 := by
  unfold fieldPair
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : SpinField N, (1:ℝ) ∂(P : Measure _) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const _)
      apply Eventually.of_forall
      intro s
      change ‖⟪(s 0).val,(s z).val⟫_ℝ‖ ≤ 1
      have hh := norm_inner_le_norm (𝕜:=ℝ) (s 0).val (s z).val
      rw [mem_sphere_zero_iff_norm.mp (s 0).property,mem_sphere_zero_iff_norm.mp (s z).property,one_mul] at hh
      exact hh
    _ = 1 := by simp

theorem ThreeMirrors.rawSource {N : ℕ} {P : ProbabilityMeasure (SpinField N)}
    (h : ThreeMirrors (fieldPair P)) (hc : CubicKernel (fieldPair P)) (hn : ∀ z,0≤fieldPair P z)
    (R : ℕ → ℕ) : NormalizedPacketSource (fieldPair P) R 0 := by
  constructor
  · intro d ι _ v x y
    exact gridPacket_spectrum_of_site_reflection (pair_bound P) (h.packetForms hc false)
      (h.packetForms hc true) d v x y
  · exact hc
  · intro n
    unfold susceptibility
    exact Finset.sum_pos' (fun i _ => hn i) ⟨0,by simp [cube],by rw [fieldPair_zero]; norm_num⟩

theorem ThreeMirrors.rawAngular {N : ℕ} {P : ProbabilityMeasure (SpinField N)}
    (h : ThreeMirrors (fieldPair P)) (hc : CubicKernel (fieldPair P)) (hn : ∀ z,0≤fieldPair P z)
    (hP : ShiftInvariant P) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x≠0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization (fieldPair P) (R n) * (fieldPair P (k n)-fieldPair P (l n))) atTop (𝓝 0) := by
  exact RawLatticeOscillation.angular_of_localOscillation (h.rawSource hc hn R) hn
    (fun z => (le_abs_self _).trans (pair_bound P z))
    (fun x c => fieldPair_gram hP x c) (by norm_num : 0≤(96:ℝ)) (by norm_num : 2≤(16:ℕ))
    (RawLatticeOscillation.localOscillation_of_site_bond (pair_bound P) hc (h.normalForms hc) h.bond)
    hR O hx hk hl

/-- Integration of a uniformly small Fourier error against the original
probability: no unobservable odd part of that momentum law is assumed
invariant. -/
private theorem mean_error (μ : ProbabilityMeasure Momentum) (H T : C(Momentum,ℝ)) {ε : ℝ}
    (h : ∀ k, |H k + horizontalMean T k| < ε)
    (he : (∫ k, horizontalMean T k ∂(μ : Measure Momentum))=∫ k, T k ∂(μ : Measure Momentum)) :
    |(∫ k, H k ∂(μ : Measure Momentum)) + ∫ k, T k ∂(μ : Measure Momentum)| ≤ ε := by
  rw [←he,← integral_add (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((horizontalMean T).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    ←Real.norm_eq_abs]
  simpa using norm_integral_le_of_norm_le_const (μ := (μ : Measure Momentum))
    (f := fun k => H k + horizontalMean T k) (C:=ε)
    (Eventually.of_forall fun k => by simpa only [Real.norm_eq_abs] using (h k).le)

private theorem base_even (β δ : ℝ) (z : Site) : J β δ (-z)=J β δ z :=
  J_even β δ z

/-- The full spin law is a limit along actual unperturbed ordinary
tori at the indicated fixed auxiliary interaction. -/
def CubicOrigin (N : ℕ) [NeZero N] (β δ : ℝ) (P : ProbabilityMeasure (SpinField N)) : Prop :=
  ∃ l : ℕ → ℕ, StrictMono l ∧ Tendsto
    (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (2*(l n+1)) (J β δ))) atTop (𝓝 P)

/-- Common finite-period origin and all three reflected two-point
forms at fixed positive auxiliary strength. The direction-dependent
comparison laws are selected only after this one probability law. -/
theorem auxiliary_state_with_origin (N : ℕ) [NeZero N] {β δ : ℝ} (hβ : 0≤β) (hδ : 0<δ) :
    ∃ P : ProbabilityMeasure (SpinField N), CubicOrigin N β δ P ∧ ShiftInvariant P ∧
      LocalGibbs.IsGibbs N (J β δ) (l1_abs_summable _) P ∧
      (∀ z, 0≤fieldPair P z) ∧ CubicKernel (fieldPair P) ∧ ThreeMirrors (fieldPair P) := by
  let sides (n : ℕ) := 2*(n+1)
  letI (n : ℕ) : NeZero (sides n) := ⟨by unfold sides; omega⟩
  have hsides : Tendsto sides atTop atTop := tendsto_atTop_mono (fun n => by dsimp [sides]; omega) tendsto_id
  obtain ⟨P,μ,l,hl,hstat,hG,hP,hμ,hvar⟩ :=
    LocalGibbs.common_cubic_variational_gibbs_state N (J β δ) (l1_abs_summable _)
      (base_even β δ) sides hsides
  have hcubic : CubicKernel (fieldPair P) := fun p s z =>
    PeriodicHorizontal.cubic_limit_pair_signedPerm N (fun n => sides (l n)) (fun _ => J β δ) P hP
      p s (Eventually.of_forall fun _ => J_signedPerm β δ p s) z
  have hpos := FerromagneticPair.physical_base_pair_nonneg N hβ hδ.le (fun n => sides (l n)) P hP
  refine ⟨P,⟨l,hl,hP⟩,hstat,hG,hpos,hcubic,?_⟩
  have hhalf : Tendsto (fun n => l n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ _) hl.tendsto_atTop
  have hc : ∀ᶠ _n : ℕ in atTop, AllGibbsHalves (J β δ) :=
    Eventually.of_forall (fun _ => baseline_all hβ hδ.le)
  constructor
  · intro I _ x hx c
    exact cubic_site_limit_reflected N hhalf (fun _ => J β δ) P hP hc x hx c
  · intro I _ x hx c
    let T := reflectedTest PeriodicMirrorLift.diagonal x c
    have hpint : (∫ k,T k ∂(μ : Measure Momentum)) =
        ∑ i, ∑ j, c i*c j*fieldPair P (x i-PeriodicMirrorLift.diagonal (x j)) := by
      simp only [T,integral_reflectedTest,hμ]
    rw [←hpint]
    by_contra! hbad
    let ε := -(∫ k, T k ∂(μ : Measure Momentum))/4
    have hε : 0<ε := by dsimp only [ε]; linarith
    obtain ⟨d,t,ht,_,ha,hfit,hslope⟩ := reflected_test_sequence β hδ hε PeriodicMirrorLift.diagonal x c
    let K (n : ℕ) : Profile := perturbed β δ d (t n)
    let H := interactionMultiplier (derivative d) (l1_abs_summable _)
    obtain ⟨Q,ν,hQ,_,hν,hcmp⟩ :=
      hvar (derivative d) K t ht (l1_abs_summable _) (fun n => l1_abs_summable (perturbed β δ d (t n))) hslope
    have hQref := diagonal_variation_reflected N (sides:=fun n => sides (l n))
      (hsides.comp hl.tendsto_atTop) K Q hQ
      (Eventually.of_forall fun n => perturbed_all_of_allowed hβ hδ.le d (t n) (ha n)) x hx c
    have hνT : 0≤∫ k,T k ∂(ν : Measure Momentum) := by
      simpa only [T,integral_reflectedTest,hν] using hQref
    have hPInv := PeriodicHorizontal.cubic_limit_invariant N (fun n => sides (l n)) (fun _ => J β δ) P hP
      (Eventually.of_forall fun _ a z => J_signedPerm β δ _ a.1 z)
    have hQInv := PeriodicHorizontal.adapted_limit_invariant N (fun n => sides (l n)) K Q hQ
      (Eventually.of_forall fun n a z => perturbed_horizontal β δ d (t n) a.2 a.1 z)
    have hμerr := (abs_le.mp (mean_error μ H T hfit
      (PeriodicHorizontal.integral_mean_reflected_eq P hPInv μ hμ _ x c))).1
    have hνerr := (abs_le.mp (mean_error ν H T hfit
      (PeriodicHorizontal.integral_mean_reflected_eq Q hQInv ν hν _ x c))).2
    change (∫ k,H k ∂(μ : Measure Momentum)) ≤ ∫ k,H k ∂(ν : Measure Momentum) at hcmp
    dsimp only [ε] at hμerr hνerr
    linarith
  · intro I _ x hx c
    exact cubic_bond_limit_reflected N hhalf (fun _ => J β δ) P hP hc x
      (fun i => by have hi := hx i; change 0≤x i 0-1 at hi; omega) c

theorem auxiliary_state (N : ℕ) [NeZero N] {β δ : ℝ} (hβ : 0≤β) (hδ : 0<δ) :
    ∃ P : ProbabilityMeasure (SpinField N), ShiftInvariant P ∧
      LocalGibbs.IsGibbs N (J β δ) (l1_abs_summable _) P ∧
      (∀ z, 0≤fieldPair P z) ∧ CubicKernel (fieldPair P) ∧ ThreeMirrors (fieldPair P) := by
  obtain ⟨P,_,h⟩ := auxiliary_state_with_origin N hβ hδ
  exact ⟨P,h⟩

/-- All fields are properties of the one original nearest-neighbour
sphere-spin probability measure P on the infinite lattice. -/
structure Selected (N : ℕ) [NeZero N] (β : ℝ) (P : ProbabilityMeasure (SpinField N)) : Prop where
  stationary : ShiftInvariant P
  gibbs : LocalGibbs.IsNearestGibbs N β P
  ferromagnetic : ∀ z, 0≤fieldPair P z
  cubic : CubicKernel (fieldPair P)
  mirrors : ThreeMirrors (fieldPair P)

/-- Selection at arbitrary finite positive spin dimension and inverse
temperature β ≥ 0. No uniqueness or pressure differentiability is needed. -/
theorem exists_state_with_origin (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0≤β) :
    ∃ Q : ProbabilityMeasure (SpinField N), Selected N β Q ∧
      ∃ (δ : ℕ → ℝ) (P : ℕ → ProbabilityMeasure (SpinField N)), (∀ n, 0<δ n) ∧
        Tendsto δ atTop (𝓝 0) ∧ (∀ n, CubicOrigin N β (δ n) (P n)) ∧ Tendsto P atTop (𝓝 Q) := by
  let δ (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hd0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose P horigin hstat hg hn hc hm using (fun n => auxiliary_state_with_origin N hβ (hd n))
  obtain ⟨Q,l,hl,hQ,hF⟩ := spinField_subsequence N P
  have hpair (z : Site) : Tendsto (fun n => fieldPair (P (l n)) z) atTop (𝓝 (fieldPair Q z)) :=
    hF (fieldDot N 0 z)
  refine ⟨Q,⟨ShiftInvariant.of_tendsto hQ (fun n => hstat (l n)),?_,?_,?_,?_⟩,
    δ ∘ l,P ∘ l,(fun n => hd (l n)),hd0.comp hl.tendsto_atTop,(fun n => horigin (l n)),hQ⟩
  · exact LocalGibbs.nearest_gibbs_of_weak_l1_limits N hQ (fun n => J β (δ (l n))) β
      (fun _ => l1_abs_summable _) ((J_l1_nearest β).comp (hd0.comp hl.tendsto_atTop))
      (fun n => hg (l n))
  · exact FerromagneticPair.fieldPair_nonneg_of_tendsto hQ (fun n => hn (l n))
  · intro p s z
    exact tendsto_nhds_unique (hpair (signedPerm p s z))
      ((hpair z).congr' (Eventually.of_forall fun n => (hc (l n) p s z).symm))
  · exact ThreeMirrors.of_pair_limit (fun n => hm (l n)) hpair

theorem exists_state (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0≤β) :
    ∃ P : ProbabilityMeasure (SpinField N), Selected N β P := by
  obtain ⟨P,h,_⟩ := exists_state_with_origin N hβ
  exact ⟨P,h⟩

/-- The susceptibility is the sharp cube susceptibility of this actual
spin law at each R. The lattice kernel has the unshifted moment packet. -/
theorem Selected.packet {N : ℕ} [NeZero N] {β : ℝ} {P : ProbabilityMeasure (SpinField N)}
    (h : Selected N β P) (R : ℕ → ℕ) : NormalizedPacketSource (fieldPair P) R 0 :=
  h.mirrors.rawSource h.cubic h.ferromagnetic R

/-- The three coordinate and six face-diagonal site planes are the cubic
conjugates of these two actual spatial mirrors. The axial bond forms
have the same change of coordinates. -/
theorem Selected.cubic_mirrors {N : ℕ} [NeZero N] {β : ℝ} {P : ProbabilityMeasure (SpinField N)}
    (h : Selected N β P) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    let e := signedPerm p s
    (SiteReflectedPositive (fieldPair P) (fun z => e z 0) (fun z => e.symm (axis (e z)))) ∧
    (SiteReflectedPositive (fieldPair P) (fun z => e z 0+e z 1) (fun z => e.symm (diagonal (e z)))) ∧
    SiteReflectedPositive (fieldPair P) (fun z => e z 0-1) (fun z => e.symm (bond (e z))) := by
  let e := signedPerm p s
  have he (x y : Site) : e (x-y)=e x-e y := by
    funext i
    change (if s i then -(x (p i)-y (p i)) else x (p i)-y (p i)) =
      (if s i then -x (p i) else x (p i))-(if s i then -y (p i) else y (p i))
    cases s i <;> simp <;> omega
  have tr (u : Site → ℤ) (r : Site → Site) (hh : SiteReflectedPositive (fieldPair P) u r) :
      SiteReflectedPositive (fieldPair P) (fun z => u (e z)) (fun z => e.symm (r (e z))) := by
    intro I _ x hx c
    have eq (i j : I) : fieldPair P (e (x i)-r (e (x j))) =
        fieldPair P (x i-e.symm (r (e (x j)))) := by
      rw [←h.cubic p s (x i-e.symm (r (e (x j))))]
      change fieldPair P _ = fieldPair P (e _)
      rw [he,Equiv.apply_symm_apply]
    simpa only [eq] using hh (fun i => e (x i)) hx c
  exact ⟨fun x hx c => tr (fun z => z 0) axis h.mirrors.axis x hx c,
    fun x hx c => tr (fun z => z 0+z 1) diagonal h.mirrors.diagonal x hx c,
    fun x hx c => tr (fun z => z 0-1) bond h.mirrors.bond x hx c⟩

theorem Selected.isotropic {N : ℕ} [NeZero N] {β : ℝ} {P : ProbabilityMeasure (SpinField N)}
    (h : Selected N β P) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hv : ModelPackets.VaguePairLimit (fieldPair P) R μ) :
    ModelPackets.IsotropicPairMeasure μ :=
  ModelPackets.isotropic_of_site_forms (pair_bound P) h.ferromagnetic (by rw [fieldPair_zero]; norm_num)
    h.cubic (fun x c => fieldPair_gram h.stationary x c) (h.mirrors.packetForms h.cubic) hR hv

theorem Selected.exists_tangent {N : ℕ} [NeZero N] {β : ℝ} {P : ProbabilityMeasure (SpinField N)}
    (h : Selected N β P) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      ModelPackets.VaguePairLimit (fieldPair P) (R ∘ u) μ ∧ ModelPackets.IsotropicPairMeasure μ :=
  ModelPackets.exists_isotropic_of_site_forms (pair_bound P) h.ferromagnetic (by rw [fieldPair_zero]; norm_num)
    h.cubic (fun x c => fieldPair_gram h.stationary x c) (h.mirrors.packetForms h.cubic) hR

theorem Selected.raw_angular {N : ℕ} [NeZero N] {β : ℝ} {P : ProbabilityMeasure (SpinField N)}
    (h : Selected N β P) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x≠0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization (fieldPair P) (R n) * (fieldPair P (k n)-fieldPair P (l n))) atTop (𝓝 0) :=
  h.mirrors.rawAngular h.cubic h.ferromagnetic h.stationary hR O hx hk hl

/-- End-to-end physical statement. The same full spin law is chosen
before all measurement scales, tangent measures and spatial isometries. -/
theorem exists_nearest_with_rotational_two_point (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0≤β) :
    ∃ P : ProbabilityMeasure (SpinField N), ShiftInvariant P ∧ LocalGibbs.IsNearestGibbs N β P ∧
      ThreeMirrors (fieldPair P) ∧ (∀ R : ℕ → ℕ, NormalizedPacketSource (fieldPair P) R 0) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
          ModelPackets.VaguePairLimit (fieldPair P) (R ∘ u) μ ∧ ModelPackets.IsotropicPairMeasure μ) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
        ModelPackets.VaguePairLimit (fieldPair P) R μ → ModelPackets.IsotropicPairMeasure μ) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x≠0 →
        ∀ k l : ℕ → Site, Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
        Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
        Tendsto (fun n => normalization (fieldPair P) (R n) *
          (fieldPair P (k n)-fieldPair P (l n))) atTop (𝓝 0)) := by
  obtain ⟨P,h⟩ := exists_state N hβ
  exact ⟨P,h.stationary,h.gibbs,h.mirrors,h.packet,fun _ hR => h.exists_tangent hR,
    fun _ hR _ _ hv => h.isotropic hR hv,fun _ hR O _ hx _ _ hk hl => h.raw_angular hR O hx hk hl⟩

#print axioms auxiliary_state
#print axioms exists_state_with_origin
#print axioms exists_state
#print axioms Selected.packet
#print axioms Selected.cubic_mirrors
#print axioms Selected.isotropic
#print axioms Selected.exists_tangent
#print axioms Selected.raw_angular
#print axioms exists_nearest_with_rotational_two_point

end IsingScaling.Rotor.PressureSelection.PhysicalMirrorSelection
