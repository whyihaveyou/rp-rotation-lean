import MathlibProbe.RotorHeisenbergFieldFinite
import MathlibProbe.ModelPacketCubeReadout
import MathlibProbe.RotorPhysicalMirrorSelection

/-! # Rotational readouts for the free Heisenberg state as the external field vanishes

`CommonFreeLimit` states the precise positive-field thermodynamic input from
Fröhlich and Rodriguez, *Some Applications of the Lee–Yang Theorem*,
Propositions 6–7 and §4. The full free-cube law converges to a stationary
state. Its dot pair also gives the limit in the free bond-centred rectangles.
The finite spin integrals, both site forms, the bond form, and nonnegativity
are derived for the same positive-field law. The inequalities persist at
every weak accumulation point as `h ↓ 0`. All angular and cube readouts
use the dot pair and susceptibility of that accumulation point.
-/

noncomputable section
open MeasureTheory Finset Filter
open scoped InnerProductSpace Topology
namespace IsingScaling.Rotor.HeisenbergField
open IsingRotation Packet ModelPackets PressureSelection

/-- Extend a finite spin configuration by `firstSpin` off its cube. -/
def extendCube (L : ℕ) : C(SiteReflection.Config 3 L, SpinField 3) where
  toFun s x := if hx : x ∈ cube L then s ⟨x,hx⟩ else firstSpin
  continuous_toFun := continuous_pi fun x => by
    by_cases hx : x ∈ cube L <;> simp only [hx, ↓reduceDIte] <;> fun_prop

/-- Free-boundary Heisenberg Gibbs law with uniform on-site source on the
finite cube, viewed as a full spin field by extending outside the cube. -/
def cubeLaw (β h : ℝ) (L : ℕ) : ProbabilityMeasure (SpinField 3) :=
  let θ := Measure.pi (fun _ : BoxSite L => fieldPrior h)
  let E (s : SiteReflection.Config 3 L) := β * SiteReflection.energy s
  have hc : Continuous E := by
    change Continuous (fun s : SiteReflection.Config 3 L => β * ((∑ x : BoxSite L, ∑ y : BoxSite L,
      if latticeDistance x y = 1 then ⟪(s x).val,(s y).val⟫_ℝ else 0)/2))
    apply continuous_const.mul
    apply Continuous.div_const
    apply continuous_finsetSum
    intro x _
    apply continuous_finsetSum
    intro y _
    by_cases he : latticeDistance x y = 1 <;> simp only [he, ↓reduceIte] <;> fun_prop
  let P : ProbabilityMeasure (SiteReflection.Config 3 L) :=
    ⟨θ.tilted E, isProbabilityMeasure_tilted (hc.rexp.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))⟩
  P.map (extendCube L).continuous.measurable.aemeasurable

/-- Every continuous field measurement of the finite free law is its
original finite-dimensional surface-spin Gibbs integral. -/
theorem cubeLaw_integral (β h : ℝ) (L : ℕ) (F : C(SpinField 3, ℝ)) :
    (∫ s, F s ∂(cubeLaw β h L : Measure _)) =
      ∫ s : SiteReflection.Config 3 L, F (extendCube L s) ∂
        ((Measure.pi fun _ : BoxSite L => fieldPrior h).tilted (fun s => β * SiteReflection.energy s)) :=
  integral_map (extendCube L).continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable

theorem cubeLaw_pair (β h : ℝ) (L : ℕ) {x y : Site} (hx : x ∈ cube L) (hy : y ∈ cube L) :
    (∫ s, fieldDot 3 x y s ∂(cubeLaw β h L : Measure _)) =
      SiteReflection.freePair (fieldPrior h) β L x y := by
  change (∫ s, fieldDot 3 x y s ∂Measure.map (extendCube L)
    ((Measure.pi (fun _ : BoxSite L => fieldPrior h)).tilted (fun s => β*SiteReflection.energy s))) = _
  rw [integral_map (extendCube L).continuous.measurable.aemeasurable
    (fieldDot 3 x y).continuous.aestronglyMeasurable, integral_tilted]
  simp [extendCube, fieldDot, hx, hy, SiteReflection.freePair, SiteReflection.boxCorrelation,
    SiteReflection.partition, smul_eq_mul, div_mul_eq_mul_div, integral_div]

/-- Positive-field thermodynamic statement needed from the Lee–Yang theorem.
The rectangle clause concerns measurements on the actual second shape. -/
structure CommonFreeLimit (β h : ℝ) (P : ProbabilityMeasure (SpinField 3)) : Prop where
  centered : Tendsto (cubeLaw β h) atTop (𝓝 P)
  stationary : ShiftInvariant P
  rectangle : ∀ x y : Site, 0 < x 0 → 0 < y 0 →
    Tendsto (fun L => BondRectangle.crossPair (fieldPrior h) β
      (BondMirror.port L x) (BondMirror.port L y)) atTop (𝓝 (fieldPair P (x-BondMirror.reflected y)))

/-- Common positive-field free limits for every positive field at the
specified nearest-neighbour inverse temperature. -/
def PositiveFieldThermodynamicInput (β : ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → ∃ P : ProbabilityMeasure (SpinField 3), CommonFreeLimit β h P

theorem CommonFreeLimit.unique {β h : ℝ} {P Q : ProbabilityMeasure (SpinField 3)}
    (hp : CommonFreeLimit β h P) (hq : CommonFreeLimit β h Q) : P = Q :=
  tendsto_nhds_unique hp.centered hq.centered

theorem CommonFreeLimit.cubePairs {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)}
    (H : CommonFreeLimit β h P) : IsStationaryFreeCubePairLimit (fieldPrior h) β id (fieldPair P) := by
  intro x y
  have lim := (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot 3 x y)).continuousAt.tendsto.comp
    H.centered
  rw [stationary_dot_integral H.stationary] at lim
  apply lim.congr'
  filter_upwards [BondMirror.ev_cube x, BondMirror.ev_cube y] with L hx hy
  exact cubeLaw_pair β h L hx hy

/-- All the spatial hypotheses on the dot pair used by the angular readout.
They are preserved by weak convergence of the spin laws. -/
structure DotForms (P : ProbabilityMeasure (SpinField 3)) : Prop where
  dot_integral : ∀ x y : Site, (∫ s, fieldDot 3 x y s ∂(P : Measure _)) = fieldPair P (x-y)
  nonnegative : ∀ z, 0 ≤ fieldPair P z
  cubic : CubicKernel (fieldPair P)
  sites : ∀ d : Bool, SiteReflectedPositive (fieldPair P) (ParitySmoothing.tip d) (ParitySmoothing.reflection d)
  bond : RawLatticeOscillation.AxialBondForm (fieldPair P)

/-- The quadratic form is the expectation of the squared block spin,
using only translation covariance of dot products. -/
private theorem DotForms.gram {P : ProbabilityMeasure (SpinField 3)} (h : DotForms P)
    {ι : Type*} [Fintype ι] (x : ι → Site) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair P (x i-x j) := by
  classical
  let v (s : SpinField 3) := ∑ i, c i • (s (x i)).val
  let A (i j : ι) : C(SpinField 3, ℝ) := (c i*c j) • fieldDot 3 (x i) (x j)
  have pos (s : SpinField 3) : 0 ≤ ∑ i, ∑ j, A i j s := by
    convert (real_inner_self_nonneg (x := v s)) using 1
    simp only [v, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      A, ContinuousMap.smul_apply, smul_eq_mul, fieldDot, ContinuousMap.coe_mk]
    simp only [← mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (s (x j)).val (s (x i)).val]
  have key : 0 ≤ ∫ s, ∑ i, ∑ j, A i j s ∂(P : Measure _) := integral_nonneg pos
  have intg (F : C(SpinField 3, ℝ)) := F.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (P : Measure _))
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => intg (A i j)))] at key
  simp_rw [integral_finsetSum _ (fun j _ => intg (A _ j))] at key
  simpa only [A, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, h.dot_integral] using key

/-- The common positive-field thermodynamic law also has translation
invariance at every order. -/
structure PairForms (P : ProbabilityMeasure (SpinField 3)) : Prop where
  stationary : ShiftInvariant P
  nonnegative : ∀ z, 0 ≤ fieldPair P z
  cubic : CubicKernel (fieldPair P)
  sites : ∀ d : Bool, SiteReflectedPositive (fieldPair P) (ParitySmoothing.tip d) (ParitySmoothing.reflection d)
  bond : RawLatticeOscillation.AxialBondForm (fieldPair P)

theorem PairForms.toDotForms {P : ProbabilityMeasure (SpinField 3)} (H : PairForms P) : DotForms P :=
  ⟨stationary_dot_integral H.stationary, H.nonnegative, H.cubic, H.sites, H.bond⟩

private theorem DotForms.withStationarity {P : ProbabilityMeasure (SpinField 3)} (H : DotForms P)
    (hs : ShiftInvariant P) : PairForms P :=
  ⟨hs, H.nonnegative, H.cubic, H.sites, H.bond⟩

theorem dotForms_of_free_pairs {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {P : ProbabilityMeasure (SpinField 3)} {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hdot : ∀ x y : Site, (∫ s, fieldDot 3 x y s ∂(P : Measure _)) = fieldPair P (x-y))
    (c : IsStationaryFreeCubePairLimit (fieldPrior h) β L (fieldPair P))
    (rect : ∀ x y : Site, 0 < x 0 → 0 < y 0 →
      Tendsto (fun j => BondRectangle.crossPair (fieldPrior h) β
        (BondMirror.port (L j) x) (BondMirror.port (L j) y)) atTop
          (𝓝 (fieldPair P (x-BondMirror.reflected y)))) : DotForms P := by
  refine ⟨hdot, ?_, c.cubic, ?_, BondRectangle.axialBond_of_crossPair_limit hβ rect⟩
  · intro z
    have lim := c z 0
    rw [sub_zero] at lim
    exact ge_of_tendsto' lim (fun n => freePair_nonnegative hβ hh (L n) z 0)
  · have hid : signedPerm (Equiv.refl (Fin 3)) (fun _ : Fin 3 => false) = Equiv.refl Site := by
      ext z i
      rfl
    obtain ⟨ha, hd⟩ := c.reflected_reindexed hL (Equiv.refl (Fin 3)) (fun _ : Fin 3 => false)
    simp only [hid, Equiv.refl_symm, Equiv.refl_apply] at ha hd
    intro d
    cases d <;> assumption

/-- Both site mirrors and the axial bond mirror of a single positive-field
free state follow from its two specified finite-volume limits. -/
theorem CommonFreeLimit.forms {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {P : ProbabilityMeasure (SpinField 3)} (H : CommonFreeLimit β h P) : PairForms P :=
  (dotForms_of_free_pairs hβ hh tendsto_id (stationary_dot_integral H.stationary) H.cubePairs
    H.rectangle).withStationarity H.stationary

theorem DotForms.of_weak_limit {P : ℕ → ProbabilityMeasure (SpinField 3)}
    {Q : ProbabilityMeasure (SpinField 3)} (hQ : Tendsto P atTop (𝓝 Q))
    (H : ∀ n, DotForms (P n)) : DotForms Q := by
  have hr (z : Site) : Tendsto (fun n => fieldPair (P n) z) atTop (𝓝 (fieldPair Q z)) :=
    (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot 3 0 z)).continuousAt.tendsto.comp hQ
  have transfer {t : Site → ℤ} {r : Site → Site}
      (ht : ∀ n, SiteReflectedPositive (fieldPair (P n)) t r) : SiteReflectedPositive (fieldPair Q) t r := by
    apply siteReflectedPositive_of_tendsto (G := fun n x y => fieldPair (P n) (x-y)) (fun x y => hr _)
    intro ι _ x hx b
    exact Eventually.of_forall fun n => ht n x hx b
  refine ⟨?_, fun z => ge_of_tendsto' (hr z) (fun n => (H n).nonnegative z), ?_, ?_, ?_⟩
  · intro x y
    have hl := (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot 3 x y)).continuousAt.tendsto.comp hQ
    exact tendsto_nhds_unique hl ((hr _).congr' (Eventually.of_forall fun n => ((H n).dot_integral x y).symm))
  · intro p s z
    exact tendsto_nhds_unique (hr (signedPerm p s z))
      ((hr z).congr' (Eventually.of_forall fun n => ((H n).cubic p s z).symm))
  · intro d
    exact transfer (fun n => (H n).sites d)
  · exact transfer (t := fun x => x 0-1) (r := fun x => ![1-x 0,x 1,x 2]) (fun n => (H n).bond)

theorem PairForms.of_weak_limit {P : ℕ → ProbabilityMeasure (SpinField 3)}
    {Q : ProbabilityMeasure (SpinField 3)} (hQ : Tendsto P atTop (𝓝 Q))
    (H : ∀ n, PairForms (P n)) : PairForms Q :=
  (DotForms.of_weak_limit hQ (fun n => (H n).toDotForms)).withStationarity
    (ShiftInvariant.of_tendsto hQ (fun n => (H n).stationary))

/-- Any sequence of positive fields tending to zero, and any weak accumulation
point of the full corresponding free states along that sequence. -/
def VanishingFieldOrigin (β : ℝ) (Q : ProbabilityMeasure (SpinField 3)) : Prop :=
  ∃ (h : ℕ → ℝ) (P : ℕ → ProbabilityMeasure (SpinField 3)), (∀ j, 0 < h j) ∧
    Tendsto h atTop (𝓝 0) ∧ (∀ j, CommonFreeLimit β (h j) (P j)) ∧ Tendsto P atTop (𝓝 Q)

/-- Compactness supplies a full-law accumulation point on every prescribed
positive field sequence once the fixed-field thermodynamic input is given. -/
theorem exists_vanishing_field_origin {β : ℝ} (H : PositiveFieldThermodynamicInput β)
    (h : ℕ → ℝ) (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (Q : ProbabilityMeasure (SpinField 3)) (k : ℕ → ℕ), StrictMono k ∧
      VanishingFieldOrigin β Q ∧ ∃ P : ℕ → ProbabilityMeasure (SpinField 3),
        (∀ j, CommonFreeLimit β (h j) (P j)) ∧ Tendsto (P ∘ k) atTop (𝓝 Q) := by
  choose P hP using (fun j => H (h j) (hp j))
  obtain ⟨Q,k,hk,hQ,_⟩ := spinField_subsequence 3 P
  exact ⟨Q,k,hk,⟨h ∘ k, P ∘ k, fun j => hp (k j), hz.comp hk.tendsto_atTop,
    fun j => hP (k j), hQ⟩,P,hP,hQ⟩

theorem VanishingFieldOrigin.forms {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) : PairForms Q := by
  obtain ⟨h,P,hp,_,hP,hQ⟩ := H
  exact PairForms.of_weak_limit hQ (fun j => (hP j).forms hβ (hp j).le)

private theorem DotForms.packet {P : ProbabilityMeasure (SpinField 3)} (H : DotForms P) (R : ℕ → ℕ) :
    NormalizedPacketSource (fieldPair P) R 0 := by
  refine ⟨?_, H.cubic, ?_⟩
  · intro d ι _ c x y
    exact gridPacket_spectrum_of_site_reflection (PhysicalMirrorSelection.pair_bound P)
      (H.sites false) (H.sites true) d c x y
  · intro n
    unfold susceptibility
    exact Finset.sum_pos' (fun i _ => H.nonnegative i) ⟨0, by simp [cube], by rw [fieldPair_zero]; norm_num⟩

private theorem DotForms.normalForms {P : ProbabilityMeasure (SpinField 3)} (H : DotForms P) (d : PacketNormal) :
    SiteReflectedPositive (fieldPair P) (NormalDifference.tip d) (NormalDifference.refl d) := by
  cases d with
  | axis =>
    have r : NormalDifference.refl .axis = ParitySmoothing.reflection false := by ext z i; fin_cases i <;> rfl
    rw [r]
    intro ι _ x hx c
    exact H.sites false x hx c
  | faceDiagonal =>
    have r : NormalDifference.refl .faceDiagonal = ParitySmoothing.reflection true := by ext z i; fin_cases i <;> rfl
    rw [r]
    intro ι _ x hx c
    exact H.sites true x hx c

theorem DotForms.angular {Q : ProbabilityMeasure (SpinField 3)}
    (h : DotForms Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization (fieldPair Q) (R n) * (fieldPair Q (k n)-fieldPair Q (l n)))
      atTop (𝓝 0) := by
  have hb := PhysicalMirrorSelection.pair_bound Q
  exact RawLatticeOscillation.angular_of_localOscillation (h.packet R) h.nonnegative
    (fun z => (le_abs_self _).trans (hb z)) (fun x c => h.gram x c)
    (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ))
    (RawLatticeOscillation.localOscillation_of_site_bond hb h.cubic h.normalForms h.bond) hR O hx hk hl

theorem VanishingFieldOrigin.angular {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization (fieldPair Q) (R n) * (fieldPair Q (k n)-fieldPair Q (l n)))
      atTop (𝓝 0) :=
  (H.forms hβ).toDotForms.angular hR O hx hk hl

theorem DotForms.angular_annulus {Q : ProbabilityMeasure (SpinField 3)}
    (h : DotForms Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {k l : ℕ → Site}
    {a B : ℝ} (ha : 0 < a) (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => normalization (fieldPair Q) (R n) * (fieldPair Q (k n)-fieldPair Q (l n)))
      atTop (𝓝 0) := by
  have hb := PhysicalMirrorSelection.pair_bound Q
  exact RawLatticeOscillation.annular_of_localOscillation (h.packet R) h.nonnegative
    (fun z => (le_abs_self _).trans (hb z)) (fun x c => h.gram x c)
    (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ))
    (RawLatticeOscillation.localOscillation_of_site_bond hb h.cubic h.normalForms h.bond) hR ha hk hl hrad

theorem VanishingFieldOrigin.angular_annulus {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {k l : ℕ → Site}
    {a B : ℝ} (ha : 0 < a) (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => normalization (fieldPair Q) (R n) * (fieldPair Q (k n)-fieldPair Q (l n)))
      atTop (𝓝 0) :=
  (H.forms hβ).toDotForms.angular_annulus hR ha hk hl hrad

theorem DotForms.isotropic {Q : ProbabilityMeasure (SpinField 3)}
    (h : DotForms Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hv : VaguePairLimit (fieldPair Q) R μ) :
    IsotropicPairMeasure μ :=
  isotropic_of_site_forms (PhysicalMirrorSelection.pair_bound Q) h.nonnegative
    (by rw [fieldPair_zero]; norm_num) h.cubic (fun x c => h.gram x c)
    h.sites hR hv

theorem VanishingFieldOrigin.isotropic {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hv : VaguePairLimit (fieldPair Q) R μ) :
    IsotropicPairMeasure μ := (H.forms hβ).toDotForms.isotropic hR hv

theorem DotForms.exists_isotropic_tangent {Q : ProbabilityMeasure (SpinField 3)} (h : DotForms Q)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (fieldPair Q) (R ∘ u) μ ∧ IsotropicPairMeasure μ :=
  exists_isotropic_of_site_forms (PhysicalMirrorSelection.pair_bound Q) h.nonnegative
    (by rw [fieldPair_zero]; norm_num) h.cubic (fun x c => h.gram x c)
    h.sites hR

theorem VanishingFieldOrigin.exists_isotropic_tangent {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (fieldPair Q) (R ∘ u) μ ∧ IsotropicPairMeasure μ :=
  (H.forms hβ).toDotForms.exists_isotropic_tangent hR

theorem VanishingFieldOrigin.cube_readout {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hv : VaguePairLimit (fieldPair Q) R μ)
    {s : ℕ} (hs : 0 < s) :
    Tendsto (fun j => susceptibility (fieldPair Q) (s * R j) / susceptibility (fieldPair Q) (R j))
      atTop (𝓝 (μ.real (observationCube s))) :=
  (H.isotropic hβ hR hv).susceptibility_ratio_tendsto (H.forms hβ).nonnegative hR hv hs

theorem VanishingFieldOrigin.unit_cube {β : ℝ} (hβ : 0 ≤ β) {Q : ProbabilityMeasure (SpinField 3)}
    (H : VanishingFieldOrigin β Q) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hv : VaguePairLimit (fieldPair Q) R μ) :
    μ.real (observationCube 1) = 1 :=
  (H.isotropic hβ hR hv).real_unit_cube_eq_one (H.forms hβ).nonnegative
    (by rw [fieldPair_zero]; norm_num) hR hv

#print axioms CommonFreeLimit.forms
#print axioms exists_vanishing_field_origin
#print axioms VanishingFieldOrigin.angular
#print axioms VanishingFieldOrigin.isotropic
#print axioms VanishingFieldOrigin.exists_isotropic_tangent
#print axioms VanishingFieldOrigin.cube_readout

end IsingScaling.Rotor.HeisenbergField
