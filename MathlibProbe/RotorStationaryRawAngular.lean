import MathlibProbe.RawLatticeAngularReadout
import MathlibProbe.RotorFreePairNonneg

/-! # Raw angular readouts for a common rotor cube and bond-rectangle limit

Consider the free nearest-neighbour rectangle with first coordinates from
−L to L+1 and transverse coordinates from −L to L. Its two congruent halves
share a bond exactly at each site of the first layer. In the ordinary Gibbs
weight, each half contributes its own internal Boltzmann factor. The product
of exponential dot-product kernels from the crossing bonds is positive.
For a finite signed linear combination of spins in one half, absorb its
component and that half's Gibbs weight into a real function. Positivity of
the crossing kernel, summed over spin components and divided by the positive
partition function, gives the physical reflected two-point inequality.

If the cross-pairs in these rectangles approach the same pair kernel as
the centered free cubes, taking the limit gives the half-integer axial
reflection of that kernel. The two ordinary site mirrors already follow from
the centered cubes. Together they control first differences at all lattice
parities, yielding the original pointwise and uniform annular readouts.

The common cross-pair limit is an explicit thermodynamic hypothesis. An
integer-centered cube has an odd number of first-coordinate layers, whereas
the bond rectangle has an even number. Translating the cube's site mirror
by an integer cannot produce the extra mirror.
-/

noncomputable section
open Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology InnerProductSpace BigOperators
namespace IsingScaling.Rotor.BondRectangle
open BondMirror (P V loc)

/-- Independent spins in each half of the free bond-symmetric rectangle. -/
abbrev Half (N L : ℕ) := P L → Spin N
abbrev Record (N L : ℕ) := Half N L × Half N L

variable {N L : ℕ}

private abbrev halfLaw (θ : Measure (Spin N)) (L : ℕ) : Measure (Half N L) :=
  Measure.pi (fun _ : P L => θ)

private def paste (z : Record N L) (i : V L) : Spin N := if i.1 then z.1 i.2 else z.2 i.2

private def term {T : Type*} (p : T → Site) (β : ℝ) (u : T → Spin N) (i j : T) : ℝ :=
  if latticeDistance (p i) (p j) = 1 then (β/2) * ⟪(u i).val,(u j).val⟫_ℝ else 0

private abbrev posSite {L : ℕ} (i : P L) : Site := loc (true,i)
private def halfWeight (β : ℝ) (u : Half N L) : ℝ :=
  Real.exp (∑ i, ∑ j, term posSite β u i j)
private def face (L : ℕ) := univ.filter (fun i : P L => i.1.val = 0)
private def crossing (β : ℝ) (z : Record N L) : ℝ :=
  ∏ i ∈ face L, Real.exp (β * ⟪(z.1 i).val,(z.2 i).val⟫_ℝ)

/-- Full ordinary free-rectangle Gibbs weight, each undirected bond counted once. -/
def weight (β : ℝ) (z : Record N L) : ℝ :=
  Real.exp (∑ i : V L, ∑ j : V L, term loc β (paste z) i j)

private lemma halfWeight_continuous (β : ℝ) : Continuous (halfWeight (N:=N) (L:=L) β) := by
  unfold halfWeight
  apply Continuous.rexp
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  unfold term
  split_ifs <;> fun_prop

private lemma crossing_continuous (β : ℝ) : Continuous (crossing (N:=N) (L:=L) β) := by
  unfold crossing
  fun_prop

private def crossTerm (β : ℝ) (u v : Half N L) (i : P L) : ℝ :=
  if i.1.val = 0 then (β/2) * ⟪(u i).val,(v i).val⟫_ℝ else 0

private lemma cross_row (β : ℝ) (u v : Half N L) (b : Bool) (i : P L) :
    (∑ j : P L, if latticeDistance (loc (b,i)) (loc (!b,j)) = 1
      then (β/2)*⟪(u i).val,(v j).val⟫_ℝ else 0) = crossTerm β u v i := by
  classical
  calc
    _ = ∑ j : P L, if j=i then crossTerm β u v i else 0 := by
      apply sum_congr rfl
      intro j _
      simp only [BondMirror.cross_dist]
      by_cases hij : j=i
      · subst j; simp [crossTerm]
      · simp [hij,Ne.symm hij]
    _ = _ := by simp

private lemma crossing_exp (β : ℝ) (z : Record N L) : crossing β z =
    Real.exp ((∑ i, crossTerm β z.1 z.2 i) + ∑ i, crossTerm β z.1 z.2 i) := by
  rw [← sum_add_distrib, Real.exp_sum]
  unfold crossing face
  rw [prod_filter]
  apply prod_congr rfl
  intro i _
  by_cases hi : i.1.val=0
  · simp only [crossTerm,hi,ite_true]
    congr 1
    ring
  · simp [crossTerm,hi]

private theorem weight_split (β : ℝ) (z : Record N L) :
    weight β z = halfWeight β z.1 * halfWeight β z.2 * crossing β z := by
  have htt (i j : P L) : term loc β (paste z) (true,i) (true,j) =
      term posSite β z.1 i j := rfl
  have hff (i j : P L) : term loc β (paste z) (false,i) (false,j) =
      term posSite β z.2 i j := by unfold term; rw [BondMirror.same_dist]; rfl
  have htf (i : P L) : (∑ j, term loc β (paste z) (true,i) (false,j)) =
      crossTerm β z.1 z.2 i := cross_row β z.1 z.2 true i
  have hft (i : P L) : (∑ j, term loc β (paste z) (false,i) (true,j)) =
      crossTerm β z.1 z.2 i := by
    have hh : crossTerm β z.2 z.1 i = crossTerm β z.1 z.2 i := by
      unfold crossTerm
      rw [real_inner_comm (z.2 i).val]
    exact (cross_row β z.2 z.1 false i).trans hh
  rw [weight, halfWeight, halfWeight,crossing_exp, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  simp only [BondMirror.sum_halves, sum_add_distrib, htt,hff,htf,hft]
  ring

private theorem weight_continuous (β : ℝ) : Continuous (weight (N:=N) (L:=L) β) := by
  simp_rw [show weight (N:=N) (L:=L) β = fun z =>
    halfWeight β z.1 * halfWeight β z.2 * crossing β z from funext (weight_split β)]
  exact (((halfWeight_continuous β).comp continuous_fst).mul
    ((halfWeight_continuous β).comp continuous_snd)).mul (crossing_continuous β)

/-- Pair of actual rotor spins at the positive port i and the reflected port j. -/
def crossPair (θ : Measure (Spin N)) (β : ℝ) {L : ℕ} (i j : P L) : ℝ :=
  (∫ z : Record N L, weight β z * ⟪(z.1 i).val,(z.2 j).val⟫_ℝ
    ∂((halfLaw θ L).prod (halfLaw θ L))) /
  (∫ z : Record N L, weight β z ∂((halfLaw θ L).prod (halfLaw θ L)))

theorem partition_pos (θ : Measure (Spin N)) [IsProbabilityMeasure θ] (β : ℝ) (L : ℕ) :
    0 < ∫ z : Record N L, weight β z ∂((halfLaw θ L).prod (halfLaw θ L)) := by
  apply integral_exp_pos
  exact (weight_continuous β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma sum_integral (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    {T : Type*} [Fintype T] (B : T → Record N L → ℝ) (hc : ∀ i, Continuous (B i)) :
    (∫ z, ∑ i, B i z ∂((halfLaw θ L).prod (halfLaw θ L))) =
      ∑ i, ∫ z, B i z ∂((halfLaw θ L).prod (halfLaw θ L)) :=
  integral_finsetSum _ (fun i _ => (hc i).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

/-- The normalized free-rectangle sphere-spin two-point matrix reflected through x₀=1/2. -/
theorem finite_cross_positive (θ : Measure (Spin N)) [IsProbabilityMeasure θ]
    {β : ℝ} (hβ : 0 ≤ β) {ι : Type*} [Fintype ι] (x : ι → P L) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * crossPair θ β (x i) (x j) := by
  classical
  let U (u : Half N L) := ∑ i, c i • (u (x i)).val
  have hu : Continuous U := by unfold U; fun_prop
  have huk (k : Fin N) : Continuous (fun u => U u k) := by fun_prop
  let μ := (halfLaw θ L).prod (halfLaw θ L)
  have h1 (k : Fin N) : 0 ≤ ∫ z : Record N L, weight β z * U z.1 k * U z.2 k ∂μ := by
    let F (u : Half N L) := halfWeight β u * U u k
    have hf : Continuous F := (halfWeight_continuous β).mul (huk k)
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    have hp := sphere_seam_integral_nonneg N (face L) (fun _ => β) (fun _ _ => hβ)
      (halfLaw θ L) F hf.measurable M (fun u => by
        simpa only [Real.norm_eq_abs] using hM _ (Set.mem_univ _))
    apply hp.trans_eq
    apply integral_congr_ae
    filter_upwards with z
    change F z.1 * F z.2 * crossing β z = weight β z * U z.1 k * U z.2 k
    rw [weight_split]
    unfold F
    ring
  have hdot : 0 ≤ ∫ z : Record N L, weight β z * ⟪U z.1,U z.2⟫_ℝ ∂μ := by
    simp only [PiLp.inner_apply,Real.inner_apply,Finset.mul_sum,← mul_assoc]
    rw [sum_integral θ (fun k z => weight β z * U z.1 k * U z.2 k)
      (fun k => ((weight_continuous β).mul ((huk k).comp continuous_fst)).mul
        ((huk k).comp continuous_snd))]
    exact sum_nonneg fun k _ => h1 k
  let H (i j : ι) (z : Record N L) :=
    c i * c j * (weight β z * ⟪(z.1 (x i)).val,(z.2 (x j)).val⟫_ℝ)
  have hH (i j : ι) : Continuous (H i j) :=
    continuous_const.mul ((weight_continuous β).mul (by fun_prop))
  have hx (z : Record N L) : weight β z * ⟪U z.1,U z.2⟫_ℝ = ∑ i, ∑ j, H i j z := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [U,H,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  simp_rw [hx] at hdot
  rw [sum_integral θ (fun i z => ∑ j, H i j z)
    (fun i => continuous_finsetSum _ (fun j _ => hH i j))] at hdot
  simp_rw [sum_integral θ (H _) (hH _)] at hdot
  simp only [H,integral_const_mul] at hdot
  simp only [crossPair,← mul_div_assoc,← sum_div]
  exact div_nonneg hdot (partition_pos θ β L).le

/-- A fixed positive-half site and its actual reflected site are the two
finite ports eventually along every diverging rectangle sequence. -/
theorem port_locations_eventually {radii : ℕ → ℕ} (hr : Tendsto radii atTop atTop)
    (x : Site) (hx : 0 < x 0) :
    ∀ᶠ k in atTop,
      loc (true,BondMirror.port (radii k) x) = x ∧
        loc (false,BondMirror.port (radii k) x) = BondMirror.reflected x := by
  filter_upwards [hr.eventually (BondMirror.ev_cube x)] with k hk
  let X : BoxSite (radii k) := ⟨x,hk⟩
  have hi : (true,BondMirror.port (radii k) x) = BondMirror.place X := by
    apply Prod.ext
    · exact (BondMirror.place_pos X hx).symm
    · simp [BondMirror.port,hk,X]
  have hl : loc (true,BondMirror.port (radii k) x) = x := hi ▸ BondMirror.place_loc X
  exact ⟨hl,(BondMirror.flip_loc _).trans (congrArg BondMirror.reflected hl)⟩

/-- A shared thermodynamic limit of the cross-pairs of genuine free rectangles
gives the half-integer mirror. No domain monotonicity is assumed. -/
theorem axialBond_of_crossPair_limit {θ : Measure (Spin N)} [IsProbabilityMeasure θ]
    {β : ℝ} (hβ : 0 ≤ β) {g : Site → ℝ} {radii : ℕ → ℕ}
    (hcross : ∀ x y : Site, 0 < x 0 → 0 < y 0 →
      Tendsto (fun k => crossPair θ β (BondMirror.port (radii k) x)
        (BondMirror.port (radii k) y)) atTop (𝓝 (g (x - BondMirror.reflected y)))) :
    RawLatticeOscillation.AxialBondForm g := by
  intro ι _ x hx c
  have hx' (i) : 0 < x i 0 := by have hi : 0 ≤ x i 0 - 1 := hx i; omega
  have hm : Tendsto (fun k => ∑ i, ∑ j, c i * c j *
      crossPair θ β (BondMirror.port (radii k) (x i)) (BondMirror.port (radii k) (x j)))
      atTop (𝓝 (∑ i, ∑ j, c i * c j * g (x i - BondMirror.reflected (x j)))) :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      tendsto_const_nhds.mul (hcross (x i) (x j) (hx' i) (hx' j))))
  exact ge_of_tendsto' hm (fun k => finite_cross_positive θ hβ
    (fun i => BondMirror.port (radii k) (x i)) c)

end IsingScaling.Rotor.BondRectangle

namespace IsingScaling.Rotor
open IsingRotation Packet NormalDifference RawLatticeOscillation

private theorem cube_site_forms {N : ℕ} {θ : Measure (Spin N)} [IsProbabilityMeasure θ]
    {β : ℝ} {g : Site → ℝ} {radii : ℕ → ℕ} (h : IsStationaryFreeCubePairLimit θ β radii g)
    (hr : Tendsto radii atTop atTop) (d : PacketNormal) :
    SiteReflectedPositive g (tip d) (NormalDifference.refl d) := by
  cases d with
  | axis =>
    have e : NormalDifference.refl .axis = signedPerm (Equiv.refl _) (fun i => decide (i=0)) := by
      funext z i; fin_cases i <;> rfl
    rw [e]
    intro ι _ x hx c
    have hp := (h.reflected_reindexed hr (Equiv.refl (Fin 3)) (fun _ : Fin 3 => false)).1 x hx c
    change 0 ≤ ∑ i, ∑ j, c i * c j *
      g (x i - (signedPerm (Equiv.refl (Fin 3)) (fun i => decide (i = 0))) (x j)) at hp
    exact hp
  | faceDiagonal =>
    have e : NormalDifference.refl .faceDiagonal = signedPerm (Equiv.swap 0 1) (fun _ => false) := by
      funext z i; fin_cases i <;> rfl
    rw [e]
    intro ι _ x hx c
    have hp := (h.reflected_reindexed hr (Equiv.refl (Fin 3)) (fun _ : Fin 3 => false)).2 x hx c
    change 0 ≤ ∑ i, ∑ j, c i * c j *
      g (x i - (signedPerm (Equiv.swap 0 1) (fun _ : Fin 3 => false)) (x j)) at hp
    exact hp

theorem IsStationaryFreeCubePairLimit.raw_localOscillation_of_bond {N : ℕ}
    {θ : Measure (Spin N)} [IsProbabilityMeasure θ] {β : ℝ} {g : Site → ℝ} {radii : ℕ → ℕ}
    (h : IsStationaryFreeCubePairLimit θ β radii g)
    (hr : Tendsto radii atTop atTop) (hbond : AxialBondForm g) :
    SpatialEnvelope.LocalOscillation g 96 16 40 := by
  exact localOscillation_of_site_bond h.abs_le_one h.cubic (cube_site_forms h hr) hbond

/-- All moving directions at comparable nonzero scale for one and the same
sphere-spin pair limit on centered cubes and half-integer-centered rectangles. -/
theorem IsStationaryFreeCubePairLimit.raw_angular_annulus_of_crossPair_limit
    {N : ℕ} [NeZero N] {β : ℝ} {radii rectR R : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hr : Tendsto radii atTop atTop)
    (_hrect : Tendsto rectR atTop atTop)
    (hcross : ∀ x y : Site, 0 < x 0 → 0 < y 0 →
      Tendsto (fun k => BondRectangle.crossPair (SiteReflection.surfacePrior N) β
        (BondMirror.port (rectR k) x) (BondMirror.port (rectR k) y)) atTop
        (𝓝 (g (x-BondMirror.reflected y))))
    (hR : Tendsto R atTop atTop) {k l : ℕ → Site} {a B : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0) := by
  exact annular_of_localOscillation (h.surface_normalizedPacketSource hβ hr R)
    (h.surface_nonneg hβ) (fun z => (le_abs_self _).trans (h.abs_le_one z))
    (h.stationaryPositive hr) (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ))
    (h.raw_localOscillation_of_bond hr (BondRectangle.axialBond_of_crossPair_limit hβ hcross))
    hR ha hk hl hrad

/-- Two independently rounded points with any prescribed orthogonal rotation. -/
theorem IsStationaryFreeCubePairLimit.raw_angular_of_bond {N : ℕ} [NeZero N]
    {β : ℝ} {radii R : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hr : Tendsto radii atTop atTop) (hbond : AxialBondForm g)
    (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0)
    {k l : ℕ → Site} (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization g (R n) * (g (k n)-g (l n))) atTop (𝓝 0) :=
  angular_of_localOscillation (h.surface_normalizedPacketSource hβ hr R) (h.surface_nonneg hβ)
    (fun z => (le_abs_self _).trans (h.abs_le_one z)) (h.stationaryPositive hr)
    (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ)) (h.raw_localOscillation_of_bond hr hbond)
    hR O hx hk hl

/-! On the sublattice of displacements with all three coordinates even,
the axial bond mirror reflects the original fine lattice in the integer plane
x₀=1. The centered cube limit already supplies this site form by a translation
of the signed test. Thus arbitrary rotations can be read at independently
chosen even fine sites, with the original susceptibility and any original
scale R. The coarse scale is floor(R/2), its cube contributes a subsum of
the physical susceptibility, and the ratio R/floor(R/2) tends to two. -/

/-- The actual spacing-two sublattice, with no averaging over neighbouring sites. -/
def doubleSite (x : Site) : Site := fun i => 2 * x i

private lemma doubleSite_sub (x y : Site) : doubleSite (x-y) = doubleSite x - doubleSite y := by
  ext i
  change 2*(x i-y i) = 2*x i-2*y i
  ring

private lemma doubleSite_cubic (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) :
    doubleSite (signedPerm p s z) = signedPerm p s (doubleSite z) := by
  funext i
  change 2*(if s i then -z (p i) else z (p i)) =
    if s i then -(2*z (p i)) else 2*z (p i)
  cases s i <;> simp

private lemma doubleSite_form {g : Site → ℝ} (d : PacketNormal)
    (h : SiteReflectedPositive g (tip d) (NormalDifference.refl d)) :
    SiteReflectedPositive (g ∘ doubleSite) (tip d) (NormalDifference.refl d) := by
  intro ι _ x hx c
  have hy (i : ι) : 0 ≤ tip d (doubleSite (x i)) := by
    have hi := hx i
    cases d <;> simp [tip,doubleSite] at hi ⊢ <;> omega
  have hr (z : Site) : NormalDifference.refl d (doubleSite z) = doubleSite (NormalDifference.refl d z) := by
    funext i; cases d <;> fin_cases i <;> simp [NormalDifference.refl,doubleSite]
  simpa only [hr,← doubleSite_sub,Function.comp_apply] using h (fun i => doubleSite (x i)) hy c

private lemma doubleSite_bond {g : Site → ℝ}
    (h : SiteReflectedPositive g (tip .axis) (NormalDifference.refl .axis)) :
    AxialBondForm (g ∘ doubleSite) := by
  intro ι _ x hx c
  let Y (i : ι) : Site := doubleSite (x i) - ![1,0,0]
  have hy (i : ι) : 0 ≤ tip .axis (Y i) := by
    have hi : 0 ≤ x i 0-1 := hx i
    change 0 ≤ 2 * x i 0 - 1
    omega
  have hid (i j : ι) : Y i - NormalDifference.refl .axis (Y j) =
      doubleSite (x i-BondMirror.reflected (x j)) := by
    funext k
    fin_cases k
    · change (2*x i 0-1) - (-(2*x j 0-1)) = 2*(x i 0 - (1-x j 0))
      ring
    · change (2*x i 1-0)-(2*x j 1-0) = 2*(x i 1-x j 1)
      ring
    · change (2*x i 2-0)-(2*x j 2-0) = 2*(x i 2-x j 2)
      ring
  have ha := h Y hy c
  simp only [hid] at ha
  exact ha

private lemma doubleSite_cube_sum_le {g : Site → ℝ} (hn : ∀ z, 0 ≤ g z) {S R : ℕ}
    (hrs : 2*S ≤ R) : susceptibility (g ∘ doubleSite) S ≤ susceptibility g R := by
  classical
  let E : Site ↪ Site := ⟨doubleSite,by
    intro x y h
    funext i
    have H := congrFun h i
    change 2*x i = 2*y i at H
    omega⟩
  have hu : (cube S).map E ⊆ cube R := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hz
    simp only [cube,Fintype.mem_piFinset,mem_Icc] at hx ⊢
    intro i
    have hi := hx i
    change -(R:ℤ) ≤ 2*x i ∧ 2*x i ≤ (R:ℤ)
    omega
  calc
    susceptibility (g ∘ doubleSite) S = ∑ z ∈ (cube S).map E,g z := by rw [sum_map]; rfl
    _ ≤ susceptibility g R := sum_le_sum_of_subset_of_nonneg hu (fun z _ _ => hn z)

private lemma doubleSite_ratio {R : ℕ → ℕ} (hr : Tendsto R atTop atTop) :
    Tendsto (fun n => (2:ℝ) * ((R n/2 : ℕ):ℝ)/(R n:ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=ℕ))).sub
    ((tendsto_mod_div_atTop_nhds_zero_nat (m:=2) (by decide)).comp hr)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [hr.eventually (eventually_ge_atTop 1)] with n hn
  have ht : 2*((R n/2:ℕ):ℝ) + ((R n%2:ℕ):ℝ) = (R n:ℝ) := by
    exact_mod_cast (show 2*(R n/2) + R n%2=R n by omega)
  have hp : (R n:ℝ) ≠ 0 := by exact_mod_cast (show R n ≠ 0 by omega)
  change 1- ((R n%2:ℕ):ℝ)/(R n:ℝ) = _
  field_simp
  linarith

private lemma scaledSite_half_of_double {R : ℕ → ℕ} (hr : Tendsto R atTop atTop)
    {q : ℕ → Site} {x : Space}
    (hq : Tendsto (fun n => scaledSite (R n) (doubleSite (q n))) atTop (𝓝 x)) :
    Tendsto (fun n => scaledSite (R n/2) (q n)) atTop (𝓝 x) := by
  have hratio := (doubleSite_ratio hr).inv₀ (by norm_num : (1:ℝ) ≠ 0)
  rw [inv_one] at hratio
  have hs := hratio.smul hq
  rw [one_smul] at hs
  apply hs.congr'
  filter_upwards [hr.eventually (eventually_ge_atTop 2)] with n hn
  have hp : (R n:ℝ) ≠ 0 := by exact_mod_cast (show R n ≠ 0 by omega)
  have hq' : ((R n/2:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show R n/2 ≠ 0 by omega)
  ext i
  change ((2:ℝ)*((R n/2:ℕ):ℝ)/(R n:ℝ))⁻¹ *
    (((2*(q n i):ℤ):ℝ)/(R n:ℝ)) = ((q n i:ℤ):ℝ)/((R n/2:ℕ):ℝ)
  push_cast
  field_simp

private theorem doubleSite_data {N : ℕ} [NeZero N] {β : ℝ} {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hr : Tendsto radii atTop atTop) (S : ℕ → ℕ) :
    NormalizedPacketSource (g ∘ doubleSite) S ∧ SpatialEnvelope.StationaryPositive (g ∘ doubleSite) ∧
      SpatialEnvelope.LocalOscillation (g ∘ doubleSite) 96 16 40 := by
  let G := g ∘ doubleSite
  have hd (d : PacketNormal) : SiteReflectedPositive G (tip d) (NormalDifference.refl d) :=
    doubleSite_form d (cube_site_forms h hr d)
  have hb (z : Site) : |G z| ≤ 1 := h.abs_le_one _
  have hc : CubicKernel G := fun p s z => by
    change g (doubleSite (signedPerm p s z)) = g (doubleSite z)
    rw [doubleSite_cubic,h.cubic p s]
  have hn (z : Site) : 0 ≤ G z := h.surface_nonneg hβ _
  have hg (s : ℕ) : 0 < susceptibility G s := by
    have hm : (0:Site) ∈ cube s := by simp [cube,Fintype.mem_piFinset]
    have h0 : doubleSite 0 = 0 := by ext i; simp [doubleSite]
    have ho : 0 < G 0 := by change 0 < g (doubleSite 0); rw [h0,h.origin]; norm_num
    exact ho.trans_le (Finset.single_le_sum (fun z _ => hn z) hm)
  constructor
  · refine ⟨?_,hc,fun n => hg (S n)⟩
    intro d ι _ c x y
    have e1 : NormalDifference.refl .axis = signedPerm (Equiv.refl _) (fun i => decide (i=0)) := by
      funext z i; fin_cases i <;> rfl
    have e2 : NormalDifference.refl .faceDiagonal = signedPerm (Equiv.swap 0 1) (fun _ => false) := by
      funext z i; fin_cases i <;> rfl
    have h1 : SiteReflectedPositive G (tip .axis) (NormalDifference.refl .axis) := hd .axis
    have h2 : SiteReflectedPositive G (tip .faceDiagonal) (NormalDifference.refl .faceDiagonal) :=
      hd .faceDiagonal
    rw [e1] at h1
    rw [e2] at h2
    exact gridPacket_spectrum_of_site_reflection hb h1 h2 d c x y
  · constructor
    · intro ι _ x c
      simpa only [← doubleSite_sub,Function.comp_apply] using
        h.stationaryPositive hr (fun i => doubleSite (x i)) c
    · exact localOscillation_of_site_bond hb hc hd (doubleSite_bond (cube_site_forms h hr .axis))

/-- Original rotor dot products at independently chosen points of spacing two.
The susceptibility and the diverging scale are those of the full fine lattice.
This needs only the stationary free centered cube limit, for every positive N. -/
theorem IsStationaryFreeCubePairLimit.raw_angular_even_lattice {N : ℕ} [NeZero N]
    {β : ℝ} {radii R : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hr : Tendsto radii atTop atTop) (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (doubleSite (k n))) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (doubleSite (l n))) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization g (R n) * (g (doubleSite (k n)) - g (doubleSite (l n))))
      atTop (𝓝 0) := by
  let S (n : ℕ) := R n/2
  let G := g ∘ doubleSite
  obtain ⟨src,hp,ho⟩ := doubleSite_data h hβ hr S
  have hS : Tendsto S atTop atTop := (Nat.tendsto_div_const_atTop (n:=2) (by decide)).comp hR
  have ht := angular_of_localOscillation src (fun z => h.surface_nonneg hβ _)
    (fun z => (le_abs_self _).trans (h.abs_le_one _)) hp (by norm_num : 0 ≤ (96:ℝ))
    (by norm_num : 2 ≤ (16:ℕ)) ho hS O hx (scaledSite_half_of_double hR hk) (scaledSite_half_of_double hR hl)
  apply tendsto_iff_dist_tendsto_zero.mpr
  have ht' := (show Tendsto (fun n => |normalization G (S n) * (G (k n)-G (l n))|)
    atTop (𝓝 0) by simpa [G] using ht.abs).const_mul 27
  rw [mul_zero] at ht'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht'
    (Eventually.of_forall fun _ => dist_nonneg)
  filter_upwards [hR.eventually (eventually_ge_atTop 2)] with n hn
  have hX := doubleSite_cube_sum_le (h.surface_nonneg hβ) (S:=S n) (R:=R n) (by dsimp [S]; omega)
  have hR' : (R n:ℝ) ≤ 3*((S n:ℕ):ℝ) := by
    exact_mod_cast (show R n ≤ 3*S n by dsimp [S]; omega)
  have hlarge : 0 < susceptibility g (R n) := zero_lt_one.trans_le (h.surface_susceptibility_ge_one hβ _)
  have hsmall : 0 < susceptibility G (S n) := src.cube_pos n
  have hnormG : 0 ≤ normalization G (S n) := by exact div_nonneg (by positivity) hsmall.le
  have hnormg : 0 ≤ normalization g (R n) := by exact div_nonneg (by positivity) hlarge.le
  have hnorm : normalization g (R n) ≤ 27 * normalization G (S n) := by
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hR' 3
    calc
      normalization g (R n) ≤ (3*(S n:ℝ))^3 / susceptibility g (R n) :=
        div_le_div_of_nonneg_right hpow hlarge.le
      _ ≤ (3*(S n:ℝ))^3 / susceptibility G (S n) :=
        div_le_div_of_nonneg_left (by positivity) hsmall hX
      _ = 27 * normalization G (S n) := by unfold normalization; ring
  simp only [Real.dist_eq,sub_zero,abs_mul,abs_of_nonneg hnormg,abs_of_nonneg hnormG]
  change normalization g (R n) * |G (k n)-G (l n)| ≤ 27 * (normalization G (S n) * |G (k n)-G (l n)|)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hnorm (abs_nonneg _)

/-- Uniform angular readout on the entire physical compact annulus for
spacing-two displacements, even when the two directions vary with scale. -/
theorem IsStationaryFreeCubePairLimit.raw_even_lattice_annulus {N : ℕ} [NeZero N]
    {β : ℝ} {radii R : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hβ : 0 ≤ β) (hr : Tendsto radii atTop atTop) (hR : Tendsto R atTop atTop)
    {k l : ℕ → Site} {a B : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (doubleSite (k n))‖ ∧
      ‖scaledSite (R n) (doubleSite (k n))‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (doubleSite (l n))‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (doubleSite (k n))‖ -
      ‖scaledSite (R n) (doubleSite (l n))‖) atTop (𝓝 0)) :
    Tendsto (fun n => normalization g (R n) * (g (doubleSite (k n)) - g (doubleSite (l n))))
      atTop (𝓝 0) := by
  let K := Metric.closedBall (0:Space) B
  let V (n : ℕ) :=
    (scaledSite (R n) (doubleSite (k n)),scaledSite (R n) (doubleSite (l n)))
  have hm (n : ℕ) : V n ∈ K ×ˢ K := by
    simpa only [Set.mem_prod,V,K,Metric.mem_closedBall,dist_zero_right]
      using And.intro (hk n).2 (hl n)
  apply tendsto_of_subseq_tendsto
  intro u hu
  obtain ⟨⟨x,y⟩,_,v,hv,hxy⟩ := ((isCompact_closedBall (0:Space) B).prod
    (isCompact_closedBall (0:Space) B)).tendsto_subseq (x:=V ∘ u) (fun n => hm _)
  have hseq := hu.comp hv.tendsto_atTop
  have hx := (continuous_fst.tendsto (x,y)).comp hxy
  have hy := (continuous_snd.tendsto (x,y)).comp hxy
  have hxpos : a ≤ ‖x‖ := ge_of_tendsto' hx.norm (fun n => (hk _).1)
  have hne : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hxpos)
  have he : ‖x‖ = ‖y‖ :=
    sub_eq_zero.mp (tendsto_nhds_unique (hx.norm.sub hy.norm) (hrad.comp hseq))
  let O := (Submodule.span ℝ ({x-y} : Set Space))ᗮ.reflection
  have hO : O x = y := Submodule.reflection_sub he
  refine ⟨v,h.raw_angular_even_lattice hβ hr (hR.comp hseq) O hne
    (k:=k ∘ u ∘ v) (l:=l ∘ u ∘ v) hx ?_⟩
  rw [hO]
  exact hy

#print axioms IsStationaryFreeCubePairLimit.raw_angular_even_lattice
#print axioms IsStationaryFreeCubePairLimit.raw_even_lattice_annulus

#print axioms BondRectangle.finite_cross_positive
#print axioms BondRectangle.axialBond_of_crossPair_limit
#print axioms IsStationaryFreeCubePairLimit.raw_angular_annulus_of_crossPair_limit
#print axioms IsStationaryFreeCubePairLimit.raw_angular_of_bond

end IsingScaling.Rotor
