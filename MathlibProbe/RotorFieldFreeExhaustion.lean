import MathlibProbe.RotorFreeUniqueExhaustion
import MathlibProbe.RotorHeisenbergFreeCubeDLR

/-! # Free induced Heisenberg domains in a fixed uniform field

The finite Gibbs density counts only the bonds inside the domain and
the on-site field on its sites. Compactness and the local resampling
equations identify every subsequential limit, including on translated
and bond-centred exhaustions. At a field with a unique Gibbs state this
gives the full exhaustion limit.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace
namespace IsingScaling.Rotor.HeisenbergField.FreeInduced
open PressureSelection LocalGibbs

/-- Internal nearest-neighbour bonds and the source on the finite domain. -/
def energy (β h : ℝ) (D : Finset Site) : C(SpinField 3, ℝ) :=
  FreeExhaustion.freeEnergy 3 β D + windowSource h D

/-- The actual finite free Gibbs measure extended by any fixed exterior fill. -/
def law (β h : ℝ) (D : Finset Site) (fill : SpinField 3) :
    ProbabilityMeasure (SpinField 3) := resample D (energy β h D) fill

private theorem energy_delta (β h : ℝ) {Λ D : Finset Site} (inside : Λ ⊆ D)
    (collar : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D)
    (s t : SpinField 3) (outside : ∀ x ∉ Λ, s x = t x) :
    energy β h D s - energy β h D t = localFieldEnergy β h Λ s - localFieldEnergy β h Λ t := by
  have pair := FreeExhaustion.free_energy_change β Λ D inside collar s t outside
  change FreeExhaustion.freeEnergy 3 β D s - FreeExhaustion.freeEnergy 3 β D t =
    nearestEnergy β Λ s - nearestEnergy β Λ t at pair
  have source : windowSource h D s - windowSource h D t =
      windowSource h Λ s - windowSource h Λ t := by
    change (∑ x : D, siteField h (s x)) - (∑ x : D, siteField h (t x)) =
      (∑ x : Λ, siteField h (s x)) - (∑ x : Λ, siteField h (t x))
    rw [Finset.sum_coe_sort D (fun x => siteField h (s x)),
      Finset.sum_coe_sort D (fun x => siteField h (t x)),
      Finset.sum_coe_sort Λ (fun x => siteField h (s x)),
      Finset.sum_coe_sort Λ (fun x => siteField h (t x)),
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact (Finset.sum_subset (f:=fun x => siteField h (s x)-siteField h (t x)) inside
      fun x _ hx => by rw [outside x hx,sub_self]).symm
  simp only [energy,localFieldEnergy,ContinuousMap.add_apply]
  linarith

/-- Exact field-specification conditional law on any inner window with collar. -/
theorem conditional (β h : ℝ) {Λ D : Finset Site} (inside : Λ ⊆ D)
    (collar : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D)
    (fill : SpinField 3) (F : C(SpinField 3, ℝ)) :
    (∫ s, F s ∂(law β h D fill : Measure _)) =
       ∫ s, readout Λ (localFieldEnergy β h Λ) F s ∂(law β h D fill : Measure _) :=
  FreeExhaustion.resample_subwindow_integral inside _ _ (energy_delta β h inside collar) fill F

/-- Pointwise eventual coverage suffices, without nesting or restrictions on fills. -/
theorem gibbs_of_limit {β h : ℝ} {D : ℕ → Finset Site}
    (covers : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField 3)
    {P : ProbabilityMeasure (SpinField 3)}
    (hP : Tendsto (fun n => law β h (D n) (fill n)) atTop (𝓝 P)) : IsFieldGibbs β h P := by
  intro Λ F
  let T := Λ ∪ Λ.biUnion (fun x => nearestSteps.image (fun z => x+z))
  have ev : ∀ᶠ n in atTop, T ⊆ D n := T.finite_toSet.eventually_all.mpr fun x _ => covers x
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP
  have hG := (ProbabilityMeasure.continuous_integral_continuousMap
    (readout Λ (localFieldEnergy β h Λ) F)).continuousAt.tendsto.comp hP
  apply tendsto_nhds_unique (hF.congr' _) hG
  filter_upwards [ev] with n hn
  exact conditional β h (fun x hx => hn (Finset.mem_union_left _ hx))
    (fun x hx z hz => hn (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x,hx,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩))) (fill n) F

theorem exists_gibbs_subsequence (β h : ℝ) (D : ℕ → Finset Site)
    (covers : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField 3) :
    ∃ (P : ProbabilityMeasure (SpinField 3)) (u : ℕ → ℕ), StrictMono u ∧
      Tendsto (fun n => law β h (D (u n)) (fill (u n))) atTop (𝓝 P) ∧ IsFieldGibbs β h P := by
  obtain ⟨P,u,hu,hP,_⟩ := spinField_subsequence 3 (fun n => law β h (D n) (fill n))
  exact ⟨P,u,hu,hP,gibbs_of_limit (D:=fun n => D (u n))
    (fun x => hu.tendsto_atTop.eventually (covers x)) (fun n => fill (u n)) hP⟩

/-- Under uniqueness every free induced exhaustion tends to the same physical state. -/
theorem tendsto_of_unique {β h : ℝ} (P : ProbabilityMeasure (SpinField 3))
    (unique : ∀ Q, IsFieldGibbs β h Q → Q=P)
    (D : ℕ → Finset Site) (covers : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n)
    (fill : ℕ → SpinField 3) : Tendsto (fun n => law β h (D n) (fill n)) atTop (𝓝 P) := by
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨Q,v,_,hQ,hg⟩ := exists_gibbs_subsequence β h (fun n => D (f n))
    (fun x => hf.eventually (covers x)) (fun n => fill (f n))
  exact ⟨v,unique Q hg ▸ hQ⟩

/-- Sites of a finite injection into the physical lattice. -/
def sites {I : Type*} [Fintype I] (p : I ↪ Site) : Finset Site := univ.map p

private def index {I : Type*} [Fintype I] (p : I ↪ Site) : I ≃ sites p :=
  Equiv.ofBijective (fun i => ⟨p i,mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩) ⟨fun _ _ h =>
    p.injective (congrArg Subtype.val h),fun x => by
      obtain ⟨i,_,hi⟩ := mem_map.mp x.property
      exact ⟨i,Subtype.ext hi⟩⟩

private theorem index_val {I : Type*} [Fintype I] (p : I ↪ Site) (i : I) :
    ((index p i).val : Site) = p i := rfl

private def coords {I : Type*} [Fintype I] (p : I ↪ Site) :=
  MeasurableEquiv.piCongrLeft (fun _ : sites p => Spin 3) (index p)

private def install {I : Type*} [Fintype I] (p : I ↪ Site) (s : I → Spin 3) : SpinField 3 :=
  replace (sites p) (fun _ => firstSpin) (coords p s)

private theorem install_site {I : Type*} [Fintype I] (p : I ↪ Site) (s : I → Spin 3) (i : I) :
    install p s (p i) = s i := by
  change install p s ((index p i).val) = _
  unfold install
  rw [replace_inside _ _ _ (index p i).property]
  exact MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ => Spin 3) (index p) s i

private theorem install_cont {I : Type*} [Fintype I] (p : I ↪ Site) :
    Continuous (install p) := by
  apply ((replace_continuous (sites p)).comp (continuous_const.prodMk ?_))
  apply continuous_pi
  intro x
  obtain ⟨i,rfl⟩ := (index p).surjective x
  simp only [coords,MeasurableEquiv.piCongrLeft_apply_apply]
  exact continuous_apply i

private def interaction {I : Type*} [Fintype I] (p : I → Site) (β : ℝ) (s : I → Spin 3) : ℝ :=
  (∑ i, ∑ k, nearestCoupling β (p k - p i) * ⟪(s i).val,(s k).val⟫_ℝ)/2

private theorem interaction_cont {I : Type*} [Fintype I] (p : I → Site) (β : ℝ) :
    Continuous (interaction p β) := by
  apply Continuous.div_const
  apply continuous_finsetSum
  intro _ _
  apply continuous_finsetSum
  intro _ _
  exact continuous_const.mul (by fun_prop)

private theorem indexed_energy {I : Type*} [Fintype I] (p : I ↪ Site) (β h : ℝ) (s : I → Spin 3) :
    energy β h (sites p) (install p s) = (∑ i, siteField h (s i)) + interaction p β s := by
  let d := sites p
  let B (x y : Site) := nearestCoupling β (y-x) * ⟪(install p s x).val,(install p s y).val⟫_ℝ
  have row (x : Site) : (∑ y ∈ d, B x y) = ∑ i : I, B x (p i) := by
    change (∑ y ∈ univ.map p, B x y) = _
    rw [Finset.sum_map]
  have source : (∑ x : sites p, siteField h (install p s x)) = ∑ i : I, siteField h (s i) := by
    rw [←(index p).sum_comp]
    simp only [index_val,install_site]
  change (∑ x ∈ d, ∑ y ∈ d, B x y)/2 + (∑ x : sites p, siteField h (install p s x)) = _
  rw [source, add_comm]
  congr 1
  simp_rw [row]
  change (∑ x ∈ univ.map p, ∑ i : I, B x (p i))/2 = _
  rw [Finset.sum_map]
  simp only [B,install_site,interaction]

/-- Reindexing an arbitrary finite induced domain gives exactly the product
single-spin field prior tilted by its genuine nearest-neighbour bonds. -/
private theorem indexed_integral {I : Type*} [Fintype I] (p : I ↪ Site) (β h : ℝ)
    (F : C(SpinField 3,ℝ)) :
    (∫ s, F s ∂(law β h (sites p) (fun _ => firstSpin) : Measure _)) =
      ∫ s, F (install p s) ∂((Measure.pi fun _ : I => fieldPrior h).tilted (interaction p β)) := by
  let E := energy β h (sites p)
  let fill : SpinField 3 := fun _ => firstSpin
  let ext := replace (sites p) fill
  let θ := SiteReflection.surfacePrior 3
  have hc : Continuous ext := (replace_continuous _).comp (continuous_const.prodMk continuous_id)
  have pull (A : SpinField 3 → ℝ) (ha : Continuous A) :
      (∫ s, A (ext s) ∂(Measure.pi fun _ : sites p => θ)) =
        ∫ s, A (install p s) ∂(Measure.pi fun _ : I => θ) :=
    ((measurePreserving_piCongrLeft (fun _ : sites p => θ) (index p)).hasLaw.integral_comp
      (ha.comp hc).aestronglyMeasurable).symm
  change (∫ s, F s ∂(resample (sites p) E fill : Measure _)) = _
  rw [resample_integral]
  change ((∫ s, Real.exp (E (ext s)) * F (ext s) ∂(Measure.pi fun _ : sites p => θ)) /
    ∫ s, Real.exp (E (ext s)) ∂(Measure.pi fun _ : sites p => θ)) = _
  rw [pull (fun s => Real.exp (E s)*F s) (E.continuous.rexp.mul F.continuous),
    pull (fun s => Real.exp (E s)) E.continuous.rexp, fieldPrior_product]
  have hs : Continuous (fun s : I → Spin 3 => ∑ i, siteField h (s i)) :=
    continuous_finsetSum _ fun _ _ => by unfold siteField; fun_prop
  rw [tilted_tilted (hs.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_tilted]
  simp only [E,indexed_energy,smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rfl

private def shifted {I : Type*} (p : I ↪ Site) (u : Site) : I ↪ Site where
  toFun i := p i-u
  inj' i j H := p.injective (by
    have H' := congrArg (fun w : Site => w+u) H
    change (p i-u)+u = (p j-u)+u at H'
    simpa only [sub_add_cancel] using H')

private theorem shift_install {I : Type*} [Fintype I] (p : I ↪ Site) (u : Site) (s : I → Spin 3) :
    shiftField u (install p s) = install (shifted p u) s := by
  funext x
  change install p s (x+u) = _
  by_cases hx : x ∈ sites (shifted p u)
  · obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    rw [install_site]
    change install p s ((p i-u)+u) = _
    rw [sub_add_cancel,install_site]
  · have hout : x+u ∉ sites p := by
      rintro hin
      obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hin
      apply hx
      exact mem_map.mpr ⟨i,mem_univ _,by change p i-u=x; rw [hi,add_sub_cancel_right]⟩
    simp only [install,replace,hout,hx,↓reduceDIte]

private theorem shift_integral {I : Type*} [Fintype I] (p : I ↪ Site) (u : Site) (β h : ℝ)
    (F : C(SpinField 3,ℝ)) :
    (∫ s, (F.comp (shiftField u)) s ∂(law β h (sites p) (fun _ => firstSpin) : Measure _)) =
      ∫ s, F s ∂(law β h (sites (shifted p u)) (fun _ => firstSpin) : Measure _) := by
  have he : interaction (shifted p u) β = interaction p β := by
    funext s
    have loc (i : I) : shifted p u i = p i-u := rfl
    simp only [interaction,loc,sub_sub_sub_cancel_right]
  rw [indexed_integral,indexed_integral,he]
  simp only [ContinuousMap.comp_apply,shift_install]

private def cubeIndex (L : ℕ) : BoxSite L ↪ Site := ⟨Subtype.val,Subtype.val_injective⟩

private theorem cover_cubeIndex (x : Site) : ∀ᶠ n : ℕ in atTop, x ∈ sites (cubeIndex n) := by
  filter_upwards [BondMirror.ev_cube x] with n hn
  exact mem_map.mpr ⟨⟨x,hn⟩,mem_univ _,rfl⟩

/-- Translating a bulk site of the physical spins leaves the unique
field Gibbs law invariant. Apply convergence to the two exhaustions
before removing the coordinate shift in the finite integrals. -/
theorem stationary_of_unique {β h : ℝ} (P : ProbabilityMeasure (SpinField 3))
    (unique : ∀ Q, IsFieldGibbs β h Q → Q=P) : ShiftInvariant P := by
  intro u
  refine ⟨(shiftField u).continuous.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (shiftField u).continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  let lift : ℕ → SpinField 3 := fun _ _ => firstSpin
  let f := F.toContinuousMap
  have hc (x : Site) : ∀ᶠ n : ℕ in atTop, x ∈ sites (shifted (cubeIndex n) u) := by
    filter_upwards [BondMirror.ev_cube (x+u)] with n hn
    exact mem_map.mpr ⟨⟨x+u,hn⟩,mem_univ _,by change x+u-u=x; abel⟩
  have a := (ProbabilityMeasure.continuous_integral_continuousMap (f.comp (shiftField u))).continuousAt.tendsto.comp
    (tendsto_of_unique P unique (fun n => sites (cubeIndex n)) cover_cubeIndex lift)
  have b := (ProbabilityMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp
    (tendsto_of_unique P unique (fun n => sites (shifted (cubeIndex n) u)) hc lift)
  exact tendsto_nhds_unique (a.congr' (Eventually.of_forall
    fun n => shift_integral (cubeIndex n) u β h f)) b

/-- Actual lattice placement of the two halves of the bond-centred rectangle. -/
def rectIndex (L : ℕ) : BondMirror.V L ↪ Site :=
  ⟨BondMirror.loc,BondMirror.loc_inj⟩

private def halfIndex (L : ℕ) : BondMirror.P L ⊕ BondMirror.P L ≃ BondMirror.V L where
  toFun := Sum.elim (fun i => (true,i)) (fun i => (false,i))
  invFun v := if v.1 then .inl v.2 else .inr v.2
  left_inv x := by cases x <;> rfl
  right_inv := by rintro ⟨b,i⟩; cases b <;> rfl

private def joinRect {L : ℕ} (z : BondRectangle.Record 3 L) (v : BondMirror.V L) : Spin 3 :=
  if v.1 then z.1 v.2 else z.2 v.2

private theorem joinRect_preserving (L : ℕ) (θ : Measure (Spin 3)) [IsProbabilityMeasure θ] :
    let μ := Measure.pi (fun _ : BondMirror.P L => θ)
    MeasurePreserving joinRect (μ.prod μ) (Measure.pi (fun _ : BondMirror.V L => θ)) := by
  let e := halfIndex L
  let E := MeasurableEquiv.piCongrLeft (fun _ : BondMirror.V L => Spin 3) e
  let split := (MeasurableEquiv.sumPiEquivProdPi (fun _ : BondMirror.P L ⊕ BondMirror.P L => Spin 3)).symm
  have H := (measurePreserving_piCongrLeft (fun _ : BondMirror.V L => θ) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : BondMirror.P L ⊕ BondMirror.P L => θ))
  have he (s : BondRectangle.Record 3 L) (i : BondMirror.P L ⊕ BondMirror.P L) :
      E (split s) (e i) = split s i :=
    MeasurableEquiv.piCongrLeft_apply_apply e _ i
  convert H using 1
  funext s v
  obtain ⟨i,rfl⟩ := e.surjective v
  change joinRect s (e i) = E (split s) (e i)
  rw [he]
  cases i <;> rfl

/-- Identity of the induced field marginal with the actual two-half,
positive-field free-rectangle integral used by the bond mirror. -/
theorem rect_pair_integral (β h : ℝ) (L : ℕ) (i j : BondMirror.P L) :
    (∫ s, fieldDot 3 (BondMirror.loc (true,i)) (BondMirror.loc (false,j)) s
      ∂(law β h (sites (rectIndex L)) (fun _ => firstSpin) : Measure _)) =
    BondRectangle.crossPair (fieldPrior h) β i j := by
  let p := rectIndex L
  let W (s : BondMirror.V L → Spin 3) := Real.exp (interaction p β s)
  have hw (z : BondRectangle.Record 3 L) : W (joinRect z) = BondRectangle.weight β z := by
    apply congrArg Real.exp
    change (∑ x : BondMirror.V L, ∑ y : BondMirror.V L, nearestCoupling β (p y-p x) *
      ⟪(joinRect z x).val,(joinRect z y).val⟫_ℝ)/2 =
        ∑ x : BondMirror.V L, ∑ y : BondMirror.V L, if latticeDistance (p x) (p y)=1 then
          (β/2)*⟪(joinRect z x).val,(joinRect z y).val⟫_ℝ else 0
    simp only [Finset.sum_div,nearestCoupling_at_pair,ite_mul,zero_mul]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    split_ifs <;> ring
  have hc : Continuous W := (interaction_cont p β).rexp
  have hp : Continuous (fun s => W s * ⟪(s (true,i)).val,(s (false,j)).val⟫_ℝ) :=
    hc.mul (by fun_prop)
  rw [indexed_integral,integral_tilted]
  change ((∫ s, (W s / _) • ⟪(install p s (p (true,i))).val,(install p s (p (false,j))).val⟫_ℝ
    ∂(Measure.pi fun _ : BondMirror.V L => fieldPrior h))) = _
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div,install_site]
  rw [←(joinRect_preserving L (fieldPrior h)).hasLaw.integral_comp hp.aestronglyMeasurable,
      ←(joinRect_preserving L (fieldPrior h)).hasLaw.integral_comp hc.aestronglyMeasurable]
  simp only [Function.comp_apply,hw,BondRectangle.crossPair]
  rfl

theorem crossPair_tendsto_of_unique {β h : ℝ} (P : ProbabilityMeasure (SpinField 3))
    (unique : ∀ Q, IsFieldGibbs β h Q → Q=P) (x y : Site) (hx : 0 < x 0) (hy : 0 < y 0) :
    Tendsto (fun L => BondRectangle.crossPair (fieldPrior h) β (BondMirror.port L x) (BondMirror.port L y))
      atTop (𝓝 (fieldPair P (x-BondMirror.reflected y))) := by
  have hc (z : Site) : ∀ᶠ n : ℕ in atTop, z ∈ sites (rectIndex n) := by
    filter_upwards [BondMirror.ev_cube z] with n hn
    exact mem_map.mpr ⟨BondMirror.place ⟨z,hn⟩,mem_univ _,BondMirror.place_loc _⟩
  have a := (ProbabilityMeasure.continuous_integral_continuousMap
    (fieldDot 3 x (BondMirror.reflected y))).continuousAt.tendsto.comp
    (tendsto_of_unique P unique (fun n => sites (rectIndex n)) hc (fun _ _ => firstSpin))
  rw [stationary_dot_integral (stationary_of_unique P unique)] at a
  apply a.congr'
  filter_upwards [BondRectangle.port_locations_eventually (radii:=id) tendsto_id x hx,
    BondRectangle.port_locations_eventually (radii:=id) tendsto_id y hy] with L hL hR
  have h1 : BondMirror.loc (true,BondMirror.port L x)=x := hL.1
  have h2 : BondMirror.loc (false,BondMirror.port L y)=BondMirror.reflected y := hR.2
  change (∫ s, fieldDot 3 x (BondMirror.reflected y) s
    ∂(law β h (sites (rectIndex L)) (fun _ => firstSpin) : Measure _)) = _
  calc
    _ = ∫ s, fieldDot 3 (BondMirror.loc (true,BondMirror.port L x))
        (BondMirror.loc (false,BondMirror.port L y)) s
        ∂(law β h (sites (rectIndex L)) (fun _ => firstSpin) : Measure _) := by rw [h1,h2]
    _ = _ := rect_pair_integral β h L (BondMirror.port L x) (BondMirror.port L y)

/-- At any fixed field admitting a unique Gibbs law, the prescribed
centred free cubes, the bond-centred rectangles, and fixed translates
all use that same stationary state. -/
theorem commonFreeLimit_of_unique {β h : ℝ} (P : ProbabilityMeasure (SpinField 3))
    (unique : ∀ Q, IsFieldGibbs β h Q → Q=P) : CommonFreeLimit β h P := by
  refine ⟨?_,stationary_of_unique P unique,crossPair_tendsto_of_unique P unique⟩
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨Q,v,hv,hQ,_⟩ := spinField_subsequence 3 (fun n => cubeLaw β h (f n))
  have hg := field_gibbs_of_free_cube_limit (L:=fun n => f (v n)) (hf.comp hv.tendsto_atTop) hQ
  exact ⟨v,unique Q hg ▸ hQ⟩

/-- The exact scalar density on any finite list of distinct physical sites.
Both bond endpoints and both dot-product sites use the same injection. -/
theorem indexed_dot_integral {I : Type*} [Fintype I] (p : I ↪ Site) (β h : ℝ) (i j : I) :
    (∫ s, fieldDot 3 (p i) (p j) s
      ∂(law β h (sites p) (fun _ => firstSpin) : Measure _)) =
      ∫ s : I → Spin 3, ⟪(s i).val,(s j).val⟫_ℝ
        ∂((Measure.pi fun _ : I => fieldPrior h).tilted
          (PressureSelection.energy fun a b => nearestCoupling β (p b-p a))) := by
  rw [indexed_integral]
  simp only [fieldDot,ContinuousMap.coe_mk,install_site] <;> rfl

#print axioms gibbs_of_limit
#print axioms exists_gibbs_subsequence
#print axioms tendsto_of_unique
#print axioms stationary_of_unique
#print axioms rect_pair_integral
#print axioms indexed_dot_integral
#print axioms commonFreeLimit_of_unique
end IsingScaling.Rotor.HeisenbergField.FreeInduced
