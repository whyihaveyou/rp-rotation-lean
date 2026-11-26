import MathlibProbe.RotorXYGinibre
import MathlibProbe.ModelPacketCubeReadout
import MathlibProbe.RotorStationaryRawAngular

/-! # The canonical free XY pair in three lattice dimensions

The pair integrals increase under isometric embeddings of finite induced
volumes. Translated inclusions between centred cubes thus put each
two-site read between two rooted reads with radii differing by a fixed
integer. The same argument identifies the bond-centred rectangular limit,
so its reflection inequality applies to the original free XY pair.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace
namespace IsingScaling.Rotor.XY

local notation "θ" => SiteReflection.surfacePrior 2

private theorem finitePair_cube {L : ℕ} (β : ℝ) (v w : BoxSite L) :
    finitePair (fun x : BoxSite L => x.val) β v w = SiteReflection.freePair θ β L v w := by
  have he (s : SiteReflection.Config 2 L) :
      (∑ e : BoxSite L × BoxSite L, (if latticeDistance e.1 e.2 = 1 then β/2 else 0) *
        ⟪(s e.1).val,(s e.2).val⟫_ℝ) = β * SiteReflection.energy s := by
    rw [Fintype.sum_prod_type]
    change _ = β * ((∑ x : BoxSite L, ∑ y : BoxSite L,
      if latticeDistance x y = 1 then ⟪(s x).val,(s y).val⟫_ℝ else 0)/2)
    rw [show ∀ a : ℝ, β*(a/2) = (β/2)*a by intro a; ring]
    simp only [Finset.mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
  rw [SiteReflection.freePair_inside]
  simp only [finitePair,graphPair,SiteReflection.boxCorrelation,SiteReflection.partition,he]

private def shiftBox {L T d : ℕ} (a : Site) (ha : ∀ i, (a i).natAbs ≤ d)
    (hLT : L+d ≤ T) : BoxSite L ↪ BoxSite T where
  toFun w := ⟨w.val+a,by
    have hw := w.property
    simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc] at hw ⊢
    intro i
    change -(T:ℤ) ≤ w.val i+a i ∧ w.val i+a i ≤ T
    have := hw i
    have := ha i
    omega⟩
  inj' _ _ h := Subtype.ext (add_right_cancel (congrArg Subtype.val h))

private theorem shiftBox_distance {L T d : ℕ} (a : Site) (ha : ∀ i, (a i).natAbs ≤ d)
    (hLT : L+d ≤ T) (x y : BoxSite L) :
    latticeDistance (shiftBox a ha hLT x) (shiftBox a ha hLT y) = latticeDistance x y := by
  apply Finset.sum_congr rfl
  intro i _
  change (x.val i+a i-(y.val i+a i)).natAbs = _
  rw [add_sub_add_right_eq_sub]

private theorem shifted_comparison {β : ℝ} (hβ : 0 ≤ β) {L T d : ℕ} (a : Site)
    (ha : ∀ i,(a i).natAbs ≤ d) (hLT : L+d ≤ T) (x y : BoxSite L) :
    SiteReflection.freePair θ β L x y ≤ SiteReflection.freePair θ β T (x.val+a) (y.val+a) :=
  (finitePair_cube β x y) ▸ (finitePair_cube β (shiftBox a ha hLT x) (shiftBox a ha hLT y)) ▸
    finitePair_embed Subtype.val Subtype.val (shiftBox a ha hLT) (shiftBox_distance a ha hLT) hβ x y

/-- Supremum of the actual rooted free-cube XY dot integrals at coupling β. -/
def canonicalFreePair (β : ℝ) (z : Site) : ℝ := ⨆ L : ℕ, SiteReflection.freePair θ β L z 0

private theorem rooted_tendsto {β : ℝ} (hβ : 0 ≤ β) (z : Site) :
    Tendsto (fun L => SiteReflection.freePair θ β L z 0) atTop (𝓝 (canonicalFreePair β z)) := by
  apply tendsto_atTop_ciSup
  · intro L T hLT
    by_cases hz : z ∈ cube L
    · let x : BoxSite L := ⟨z,hz⟩
      let y : BoxSite L := ⟨0,by simp [cube]⟩
      simpa only [x,y,add_zero] using
        shifted_comparison hβ 0 (d:=0) (by simp) (by omega : L+0≤T) x y
    · simpa [SiteReflection.freePair,hz] using surface_freePair_nonneg 2 hβ T z 0
  · refine ⟨1,?_⟩
    rintro _ ⟨L,rfl⟩
    exact (le_abs_self _).trans (SiteReflection.abs_freePair_le_one θ β L z 0)

/-- All pairs converge along the entire sequence of centred free cubes.
Both sites may be distinct from the origin. -/
theorem canonicalFreePair_stationary {β : ℝ} (hβ : 0 ≤ β) :
    IsStationaryFreeCubePairLimit θ β id (canonicalFreePair β) := by
  intro x y
  let d := ∑ i, (y i).natAbs
  have hy (i) : (y i).natAbs ≤ d :=
    Finset.single_le_sum (f := fun j => (y j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hneg (i) : ((-y) i).natAbs ≤ d := by simpa using hy i
  have hl := (rooted_tendsto hβ (x-y)).comp (Filter.tendsto_sub_atTop_nat d)
  have hh := (Filter.tendsto_add_atTop_iff_nat d).mpr (rooted_tendsto hβ (x-y))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
  · filter_upwards [eventually_ge_atTop d,(Filter.tendsto_sub_atTop_nat d).eventually
      (BondMirror.ev_cube (x-y))] with L hL hz
    let z : BoxSite (L-d) := ⟨x-y,hz⟩
    let o : BoxSite (L-d) := ⟨0,by simp [cube]⟩
    change SiteReflection.freePair θ β (L-d) (x-y) 0 ≤ SiteReflection.freePair θ β L x y
    simpa only [z,o,sub_add_cancel,zero_add] using
      shifted_comparison hβ y hy (by omega : L-d+d ≤ L) z o
  · filter_upwards [BondMirror.ev_cube x,BondMirror.ev_cube y] with L hx hyL
    let u : BoxSite L := ⟨x,hx⟩
    let v : BoxSite L := ⟨y,hyL⟩
    change SiteReflection.freePair θ β L x y ≤ SiteReflection.freePair θ β (L+d) (x-y) 0
    simpa only [u,v,add_neg_cancel,←sub_eq_add_neg] using
      shifted_comparison hβ (-y) hneg (le_rfl : L+d≤L+d) u v

private theorem finitePair_le_canonical {T : Type*} [Fintype T] (p : T → Site)
    (hp : Function.Injective p) {β : ℝ} (hβ : 0 ≤ β) (v w : T) :
    finitePair p β v w ≤ canonicalFreePair β (p v-p w) := by
  apply ge_of_tendsto (canonicalFreePair_stationary hβ (p v) (p w))
  have hall : ∀ᶠ L : ℕ in atTop, ∀ i : T, p i ∈ cube L :=
    Filter.eventually_all.mpr (fun i => BondMirror.ev_cube (p i))
  filter_upwards [hall] with L hL
  let e : T ↪ BoxSite L := ⟨fun i => ⟨p i,hL i⟩,fun _ _ h => hp (congrArg Subtype.val h)⟩
  have h := finitePair_embed p Subtype.val e (fun _ _ => rfl) hβ v w
  rw [finitePair_cube] at h
  exact h

/-- Every exhaustion by finite induced free lattices reads the same XY
correlation. A site need only appear eventually; nesting and regular
boundary shape play no role in the comparison. -/
theorem finitePair_tendsto_of_exhaustion {T : ℕ → Type*} [∀ n, Fintype (T n)]
    (p : ∀ n, T n → Site) (hinj : ∀ n, Function.Injective (p n))
    (hex : ∀ z : Site, ∀ᶠ n in atTop, z ∈ Set.range (p n))
    {x y : Site} (v w : ∀ n, T n)
    (hv : ∀ᶠ n in atTop, p n (v n) = x) (hw : ∀ᶠ n in atTop, p n (w n) = y)
    {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun n => finitePair (p n) β (v n) (w n)) atTop (𝓝 (canonicalFreePair β (x-y))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hread := (tendsto_order.mp (canonicalFreePair_stationary hβ x y)).1 a ha
    obtain ⟨L,hX,hY,hh⟩ := ((BondMirror.ev_cube x).and ((BondMirror.ev_cube y).and hread)).exists
    let X : BoxSite L := ⟨x,hX⟩
    let Y : BoxSite L := ⟨y,hY⟩
    have hall : ∀ᶠ n in atTop, ∀ t : BoxSite L, t.val ∈ Set.range (p n) :=
      Filter.eventually_all.mpr (fun t => hex t.val)
    filter_upwards [hall,hv,hw] with n hn hx hy
    choose atSite hsite using hn
    let e : BoxSite L ↪ T n := ⟨atSite,fun u t h => Subtype.ext
      ((hsite u).symm.trans ((congrArg (p n) h).trans (hsite t)))⟩
    have he (t : BoxSite L) : p n (e t) = t.val := hsite t
    have h₁ : e X=v n := hinj n ((he X).trans hx.symm)
    have h₂ : e Y=w n := hinj n ((he Y).trans hy.symm)
    have h := finitePair_embed Subtype.val (p n) e (fun i j => by rw [he,he]) hβ X Y
    rw [finitePair_cube,h₁,h₂] at h
    exact lt_of_lt_of_le hh h
  · intro b hb
    filter_upwards [hv,hw] with n hx hy
    have h := finitePair_le_canonical (p n) (hinj n) hβ (v n) (w n)
    rw [hx,hy] at h
    exact h.trans_lt hb

theorem canonicalFreePair_isotropic {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ModelPackets.VaguePairLimit (canonicalFreePair β) R μ) :
    ModelPackets.IsotropicPairMeasure μ :=
  (canonicalFreePair_stationary hβ).surface_isotropic hβ tendsto_id hR hv

theorem canonicalFreePair_exists_isotropic_tangent {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      ModelPackets.VaguePairLimit (canonicalFreePair β) (R ∘ u) μ ∧ ModelPackets.IsotropicPairMeasure μ :=
  (canonicalFreePair_stationary hβ).surface_exists_isotropic_tangent hβ tendsto_id hR

theorem canonicalFreePair_cube_readout {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ModelPackets.VaguePairLimit (canonicalFreePair β) R μ) :
    μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
      Tendsto (fun j => susceptibility (canonicalFreePair β) (s*R j) / susceptibility (canonicalFreePair β) (R j))
        atTop (𝓝 (μ.real (observationCube s))) :=
  (canonicalFreePair_stationary hβ).surface_cube_readout hβ tendsto_id hR hv

open BondMirror (V P loc)

private def sideIndex (L : ℕ) : P L ⊕ P L ≃ V L where
  toFun := Sum.elim (fun i => (true,i)) (fun i => (false,i))
  invFun v := if v.1 then .inl v.2 else .inr v.2
  left_inv x := by cases x <;> rfl
  right_inv := by rintro ⟨b,i⟩; cases b <;> rfl

private def joinRect {L : ℕ} (z : BondRectangle.Record 2 L) (v : V L) : Spin 2 :=
  if v.1 then z.1 v.2 else z.2 v.2

private theorem joinRect_preserving (L : ℕ) :
    let μ := Measure.pi (fun _ : P L => θ)
    MeasurePreserving joinRect (μ.prod μ) (Measure.pi (fun _ : V L => θ)) := by
  let e := sideIndex L
  let E := MeasurableEquiv.piCongrLeft (fun _ : V L => Spin 2) e
  let split := (MeasurableEquiv.sumPiEquivProdPi (fun _ : P L ⊕ P L => Spin 2)).symm
  have h := (measurePreserving_piCongrLeft (fun _ : V L => θ) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : P L ⊕ P L => θ))
  have he (s : BondRectangle.Record 2 L) (i : P L ⊕ P L) :
      E (split s) (e i) = split s i :=
    MeasurableEquiv.piCongrLeft_apply_apply e _ i
  convert h using 1
  funext s v
  obtain ⟨i,rfl⟩ := e.surjective v
  change joinRect s (e i) = E (split s) (e i)
  rw [he]
  cases i <;> rfl

private theorem finitePair_rectangle {L : ℕ} (β : ℝ) (i j : P L) :
    finitePair loc β (true,i) (false,j) = BondRectangle.crossPair θ β i j := by
  let W (s : V L → Spin 2) := Real.exp (∑ e : V L × V L,
    (if latticeDistance (loc e.1) (loc e.2) = 1 then β/2 else 0) * ⟪(s e.1).val,(s e.2).val⟫_ℝ)
  have hw (z : BondRectangle.Record 2 L) : W (joinRect z) = BondRectangle.weight β z := by
    apply congrArg Real.exp
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    change (if latticeDistance (loc x) (loc y) = 1 then β/2 else 0) *
      ⟪(joinRect z x).val,(joinRect z y).val⟫_ℝ =
      if latticeDistance (loc x) (loc y) = 1 then (β/2) * ⟪(joinRect z x).val,(joinRect z y).val⟫_ℝ else 0
    simp only [ite_mul,zero_mul]
  have hc : Continuous W := by
    apply Continuous.rexp
    apply continuous_finsetSum
    intro e _
    exact continuous_const.mul (by fun_prop)
  have hp : Continuous (fun s => W s * ⟪(s (true,i)).val,(s (false,j)).val⟫_ℝ) :=
    hc.mul (by fun_prop)
  change (∫ s, W s * ⟪(s (true,i)).val,(s (false,j)).val⟫_ℝ ∂(Measure.pi (fun _ : V L => θ))) /
    (∫ s, W s ∂(Measure.pi (fun _ : V L => θ))) = _
  rw [← (joinRect_preserving L).hasLaw.integral_comp hp.aestronglyMeasurable,
    ← (joinRect_preserving L).hasLaw.integral_comp hc.aestronglyMeasurable]
  simp only [Function.comp_apply,hw,BondRectangle.crossPair]
  rfl

/-- The free rectangle whose centre is on the bond plane has the same
limiting cross-pairs as the centred cubes. Its exterior sits between radii L and L+1. -/
theorem crossPair_tendsto {β : ℝ} (hβ : 0 ≤ β) (x y : Site) (hx : 0 < x 0) (hy : 0 < y 0) :
    Tendsto (fun L => BondRectangle.crossPair θ β (BondMirror.port L x) (BondMirror.port L y))
      atTop (𝓝 (canonicalFreePair β (x-BondMirror.reflected y))) := by
  simp_rw [←finitePair_rectangle]
  apply finitePair_tendsto_of_exhaustion (fun L => loc (L:=L)) (fun _ => BondMirror.loc_inj)
    _ (fun L => (true,BondMirror.port L x)) (fun L => (false,BondMirror.port L y)) _ _ hβ
  · intro z
    filter_upwards [BondMirror.ev_cube z] with L hz
    let v : BoxSite L := ⟨z,hz⟩
    exact ⟨BondMirror.place v,BondMirror.place_loc v⟩
  · exact (BondRectangle.port_locations_eventually (radii:=id) tendsto_id x hx).mono fun _ h => h.1
  · exact (BondRectangle.port_locations_eventually (radii:=id) tendsto_id y hy).mono fun _ h => h.2

theorem canonicalFreePair_axialBond_positive {β : ℝ} (hβ : 0 ≤ β) :
    RawLatticeOscillation.AxialBondForm (canonicalFreePair β) :=
  BondRectangle.axialBond_of_crossPair_limit (radii:=id) hβ (crossPair_tendsto hβ)

/-- Pointwise angular comparison at every nonzero spatial point, with
independent lattice roundings and the free XY pair's own susceptibility. -/
theorem canonicalFreePair_raw_angular {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => Packet.normalization (canonicalFreePair β) (R n) *
      (canonicalFreePair β (k n) - canonicalFreePair β (l n))) atTop (𝓝 0) :=
  (canonicalFreePair_stationary hβ).raw_angular_of_bond hβ tendsto_id
    (canonicalFreePair_axialBond_positive hβ) hR O hx hk hl

theorem canonicalFreePair_raw_annulus {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {k l : ℕ → Site} {a B : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => Packet.normalization (canonicalFreePair β) (R n) *
      (canonicalFreePair β (k n) - canonicalFreePair β (l n))) atTop (𝓝 0) :=
  (canonicalFreePair_stationary hβ).raw_angular_annulus_of_crossPair_limit hβ tendsto_id
    (rectR:=id) tendsto_id (crossPair_tendsto hβ) hR ha hk hl hrad

#print axioms canonicalFreePair_stationary
#print axioms canonicalFreePair_isotropic
#print axioms canonicalFreePair_exists_isotropic_tangent
#print axioms canonicalFreePair_cube_readout
#print axioms crossPair_tendsto
#print axioms canonicalFreePair_axialBond_positive
#print axioms canonicalFreePair_raw_angular
#print axioms canonicalFreePair_raw_annulus
#print axioms finitePair_tendsto_of_exhaustion
end IsingScaling.Rotor.XY
