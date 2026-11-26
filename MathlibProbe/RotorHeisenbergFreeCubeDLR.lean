import MathlibProbe.RotorVanishingFieldDLR
import MathlibProbe.RotorHeisenbergVanishingField

/-! # Local Gibbs equations of the positive-field free Heisenberg state

When a finite window and all six nearest neighbours of its sites lie inside
the free cube, replacing its spins changes the finite-volume energy by
exactly the change of its local specification. Splitting the product sphere
law into window and complement and integrating the window first proves the
conditional expectation identity for the complete finite-cube measure.
The identity passes to any weak cube limit. The uniform local field bound
then gives the zero-field DLR equations at every vanishing-field limit.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped InnerProductSpace Topology
namespace IsingScaling.Rotor.HeisenbergField
open PressureSelection LocalGibbs

private def pairBond (β : ℝ) (s : SpinField 3) (x y : Site) : ℝ :=
  nearestCoupling β (y-x) * ⟪(s x).val, (s y).val⟫_ℝ

private theorem pairBond_comm (β : ℝ) (s : SpinField 3) (x y : Site) :
    pairBond β s y x = pairBond β s x y := by
  simp only [pairBond, show x-y = -(y-x) by abel, nearestCoupling_even, real_inner_comm (s y).val]

private def active (Λ : Finset Site) (x y : Site) : ℝ :=
  if x ∈ Λ then (if y ∈ Λ then 1/2 else 1) else 0

/-- Count within-window bonds with two half weights and incident exterior
bonds once, on any finite domain containing the interaction collar. -/
private theorem local_pair_sum (β : ℝ) (Λ D : Finset Site) (hΛ : Λ ⊆ D)
    (collar : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D) (s : SpinField 3) :
    nearestEnergy β Λ s = ∑ x ∈ D, ∑ y ∈ D, active Λ x y * pairBond β s x y := by
  let B (x y : Site) := active Λ x y * pairBond β s x y
  have row (x : Λ) : (∑' z : Site, nearestCoupling β z *
      ((if x.val+z ∈ Λ then (1:ℝ)/2 else 1) * ⟪(s x.val).val, (s (x.val+z)).val⟫_ℝ)) =
        ∑ y ∈ D, B x.val y := by
    calc
      _ = ∑' z, B x.val (x.val+z) := by
        apply tsum_congr
        intro z
        simp only [B, active, pairBond, x.property, ite_true, add_sub_cancel_left]
        ring
      _ = ∑' y, B x.val y := (Equiv.addLeft x.val).tsum_eq (B x.val)
      _ = _ := tsum_eq_sum fun y hy => by
        have hstep : y-x.val ∉ nearestSteps := fun h => hy (by simpa using collar x.val x.property _ h)
        simp [B, pairBond, nearestCoupling, hstep]
  change (∑ x : Λ, ∑' z : Site, nearestCoupling β z *
    ((if x.val+z ∈ Λ then (1:ℝ)/2 else 1) * ⟪(s x.val).val, (s (x.val+z)).val⟫_ℝ)) = _
  simp only [row]
  rw [Finset.sum_coe_sort Λ (fun x => ∑ y ∈ D, B x y)]
  exact Finset.sum_subset hΛ (fun x _ hx => by simp [B, active, hx])

private def domainEnergy (β h : ℝ) (D : Finset Site) (s : SpinField 3) : ℝ :=
  (∑ x ∈ D, ∑ y ∈ D, pairBond β s x y)/2 + ∑ x ∈ D, siteField h (s x)

set_option maxHeartbeats 600000 in
private theorem energy_change (β h : ℝ) (Λ D : Finset Site) (hΛ : Λ ⊆ D)
    (collar : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D) (s t : SpinField 3)
    (outside : ∀ x ∉ Λ, s x = t x) :
    domainEnergy β h D s - domainEnergy β h D t =
      localFieldEnergy β h Λ s - localFieldEnergy β h Λ t := by
  let d (x y : Site) := pairBond β s x y - pairBond β t x y
  have ds (x y : Site) : d y x = d x y := by simp only [d, pairBond_comm β s y x, pairBond_comm β t y x]
  have split (x y : Site) : d x y = active Λ x y * d x y + active Λ y x * d y x := by
    rw [ds]
    by_cases hx : x ∈ Λ <;> by_cases hy : y ∈ Λ
    · simp [active, hx, hy]; ring
    · simp [active, hx, hy]
    · simp [active, hx, hy]
    · simp [active, hx, hy, d, pairBond, outside x hx, outside y hy]
  have hh := Finset.sum_congr (s₁ := D) rfl (fun x _ => Finset.sum_congr (s₁ := D) rfl (fun y _ => split x y))
  simp only [Finset.sum_add_distrib] at hh
  rw [Finset.sum_comm (f := fun x y => active Λ y x * d y x)] at hh
  have hfull : (∑ x ∈ D, ∑ y ∈ D, pairBond β s x y)/2 -
      (∑ x ∈ D, ∑ y ∈ D, pairBond β t x y)/2 = (∑ x ∈ D, ∑ y ∈ D, d x y)/2 := by
    simp only [d, Finset.sum_sub_distrib, sub_div]
  have hlocal : nearestEnergy β Λ s - nearestEnergy β Λ t =
      ∑ x ∈ D, ∑ y ∈ D, active Λ x y * d x y := by
    rw [local_pair_sum β Λ D hΛ collar, local_pair_sum β Λ D hΛ collar]
    simp only [d, mul_sub, Finset.sum_sub_distrib]
  have hsrc : (∑ x ∈ D, siteField h (s x)) - ∑ x ∈ D, siteField h (t x) =
      windowSource h Λ s - windowSource h Λ t := by
    change _ = (∑ x : Λ, siteField h (s x.val)) - ∑ x : Λ, siteField h (t x.val)
    rw [Finset.sum_coe_sort Λ (fun x => siteField h (s x)), Finset.sum_coe_sort Λ (fun x => siteField h (t x)),
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact (Finset.sum_subset hΛ fun x _ hx => by rw [outside x hx,sub_self]).symm
  simp only [domainEnergy, localFieldEnergy, ContinuousMap.add_apply]
  linarith

private abbrev Rest (L : ℕ) (Λ : Finset Site) := {x : BoxSite L // x.val ∉ Λ}

private def classify (L : ℕ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L) : BoxSite L ≃ Λ ⊕ Rest L Λ where
  toFun x := if h : x.val ∈ Λ then .inl ⟨x.val,h⟩ else .inr ⟨x,h⟩
  invFun := Sum.elim (fun x => ⟨x.val, hΛ x.property⟩) Subtype.val
  left_inv x := by by_cases hx : x.val ∈ Λ <;> simp [hx]
  right_inv x := by cases x with
    | inl a => simp [a.property]
    | inr b => simp [b.property]

private def paste (L : ℕ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L)
    (p : WindowSpin 3 Λ × (Rest L Λ → Spin 3)) : SiteReflection.Config 3 L :=
  fun x => Sum.elim p.1 p.2 (classify L Λ hΛ x)

private theorem paste_cont (L : ℕ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L) : Continuous (paste L Λ hΛ) := by
  apply continuous_pi
  intro x
  unfold paste
  cases classify L Λ hΛ x <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

private abbrev prior (A : Type*) [Fintype A] : Measure (A → Spin 3) :=
  Measure.pi (fun _ : A => SiteReflection.surfacePrior 3)

private theorem paste_preserving (L : ℕ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L) :
    MeasurePreserving (paste L Λ hΛ) ((prior Λ).prod (prior (Rest L Λ))) (prior (BoxSite L)) := by
  let e := classify L Λ hΛ
  let A := fun _ : Λ ⊕ Rest L Λ => SiteReflection.surfacePrior 3
  have h1 := measurePreserving_sumPiEquivProdPi_symm A
  have h2 := (measurePreserving_piCongrLeft A e).symm
  convert h2.comp h1 using 1
  funext p x
  change Sum.elim p.1 p.2 (e x) =
    (Equiv.piCongrLeft (fun _ => Spin 3) e).symm _ x
  rw [Equiv.piCongrLeft_symm_apply]
  cases e x <;> rfl

private theorem full_at (L : ℕ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L)
    (p : WindowSpin 3 Λ × (Rest L Λ → Spin 3)) (x : Site) :
    extendCube L (paste L Λ hΛ p) x = if h : x ∈ Λ then p.1 ⟨x,h⟩ else
      if hD : x ∈ cube L then p.2 ⟨⟨x,hD⟩,h⟩ else firstSpin := by
  by_cases h : x ∈ Λ
  · simp [extendCube, paste, classify, h, hΛ h]
  · by_cases hD : x ∈ cube L <;> simp [extendCube, paste, classify, h, hD]

private theorem full_replace (L : ℕ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L)
    (p : WindowSpin 3 Λ × (Rest L Λ → Spin 3)) (a : WindowSpin 3 Λ) :
    replace Λ (extendCube L (paste L Λ hΛ p)) a = extendCube L (paste L Λ hΛ (a,p.2)) := by
  funext x
  by_cases hx : x ∈ Λ <;> simp [replace, full_at, hx]

private def finiteEnergy (L : ℕ) (β h : ℝ) : C(SiteReflection.Config 3 L, ℝ) where
  toFun s := (∑ x : BoxSite L, siteField h (s x)) + β * SiteReflection.energy s
  continuous_toFun := by
    apply Continuous.add (continuous_finsetSum _ fun x _ => by unfold siteField; fun_prop)
    change Continuous (fun s : SiteReflection.Config 3 L => β * ((∑ x : BoxSite L, ∑ y : BoxSite L,
      if latticeDistance x y = 1 then ⟪(s x).val,(s y).val⟫_ℝ else 0)/2))
    apply continuous_const.mul
    apply Continuous.div_const
    apply continuous_finsetSum
    intro x _
    apply continuous_finsetSum
    intro y _
    by_cases he : latticeDistance x y = 1 <;> simp only [he, ↓reduceIte] <;> fun_prop

private theorem finiteEnergy_eq (L : ℕ) (β h : ℝ) (s : SiteReflection.Config 3 L) :
    finiteEnergy L β h s = domainEnergy β h (cube L) (extendCube L s) := by
  let f := extendCube L s
  have atSite (x : BoxSite L) : f x.val = s x := by simp [f,extendCube,x.property]
  let b (x y : Site) := pairBond β f x y
  have row (x : Site) : (∑ y : BoxSite L, b x y.val) = ∑ y ∈ cube L, b x y := Finset.sum_coe_sort _ _
  have pair : (∑ x : BoxSite L, ∑ y : BoxSite L, b x.val y.val) = ∑ x ∈ cube L, ∑ y ∈ cube L, b x y := by
    simp only [row]
    exact Finset.sum_coe_sort (cube L) (fun x => ∑ y ∈ cube L, b x y)
  have src : (∑ x : BoxSite L, siteField h (s x)) = ∑ x ∈ cube L, siteField h (f x) := by
    simp_rw [← atSite]
    exact Finset.sum_coe_sort (cube L) (fun x => siteField h (f x))
  change (∑ x : BoxSite L, siteField h (s x)) + β * ((∑ x : BoxSite L, ∑ y : BoxSite L,
      if latticeDistance x y = 1 then ⟪(s x).val,(s y).val⟫_ℝ else 0)/2) =
    (∑ x ∈ cube L, ∑ y ∈ cube L, b x y)/2 + ∑ x ∈ cube L, siteField h (f x)
  rw [src, add_comm, ← pair, ← mul_div_assoc]
  congr 2
  simp only [Finset.mul_sum, b, pairBond, nearestCoupling_at_pair, atSite, ite_mul, mul_ite, zero_mul, mul_zero]

private theorem combined_cube_integral (L : ℕ) (β h : ℝ) (F : C(SpinField 3, ℝ)) :
    (∫ s, F s ∂(cubeLaw β h L : Measure _)) =
      ∫ s, F (extendCube L s) ∂(prior (BoxSite L)).tilted (finiteEnergy L β h) := by
  rw [cubeLaw_integral, fieldPrior_product]
  have hc : Continuous (fun s : SiteReflection.Config 3 L => ∑ x, siteField h (s x)) :=
    continuous_finsetSum _ fun x _ => by unfold siteField; fun_prop
  rw [tilted_tilted (hc.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

set_option maxHeartbeats 800000 in
/-- Exact window invariance for every finite free cube containing the
window and its nearest-neighbour collar. The observable may depend on
the whole extended configuration. -/
theorem free_cube_field_conditional (L : ℕ) (β h : ℝ) (Λ : Finset Site) (hΛ : Λ ⊆ cube L)
    (collar : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ cube L) (F : C(SpinField 3, ℝ)) :
    (∫ s, F s ∂(cubeLaw β h L : Measure _)) =
      ∫ s, readout Λ (localFieldEnergy β h Λ) F s ∂(cubeLaw β h L : Measure _) := by
  let X := WindowSpin 3 Λ
  let Y := Rest L Λ → Spin 3
  let η := (prior Λ).prod (prior (Rest L Λ))
  let join := paste L Λ hΛ
  let full (p : X × Y) := extendCube L (join p)
  let H (p : X × Y) := finiteEnergy L β h (join p)
  let E := localFieldEnergy β h Λ
  let G (p : X × Y) := F (full p)
  let R (p : X × Y) := readout Λ E F (full p)
  let V (y : Y) := (∫ a : X, Real.exp (H (a,y)) * G (a,y) ∂prior Λ) /
    ∫ a : X, Real.exp (H (a,y)) ∂prior Λ
  have contFull : Continuous full := (extendCube L).continuous.comp (paste_cont L Λ hΛ)
  have contH : Continuous H := (finiteEnergy L β h).continuous.comp (paste_cont L Λ hΛ)
  have contG : Continuous G := F.continuous.comp contFull
  have contR : Continuous R := (readout Λ E F).continuous.comp contFull
  have value (a : X) (y : Y) : R (a,y) = V y := by
    let ref : X := fun _ => firstSpin
    let c := H (ref,y) - E (full (ref,y))
    have split (b : X) : H (b,y) = c + E (full (b,y)) := by
      have out (x : Site) (hx : x ∉ Λ) : full (b,y) x = full (ref,y) x := by
        simp [full,join,full_at,hx]
      have step := energy_change β h Λ (cube L) hΛ collar (full (b,y)) (full (ref,y)) out
      have h1 := finiteEnergy_eq L β h (join (b,y))
      have h2 := finiteEnergy_eq L β h (join (ref,y))
      change H (b,y) = domainEnergy β h (cube L) (full (b,y)) at h1
      change H (ref,y) = domainEnergy β h (cube L) (full (ref,y)) at h2
      change _ = E _ - E _ at step
      dsimp only [c]
      linarith
    have repl (b : X) : replace Λ (full (a,y)) b = full (b,y) := full_replace L Λ hΛ (a,y) b
    change (∫ t, F t ∂(resample Λ E (full (a,y)) : Measure _)) = V y
    rw [resample_integral]
    change ((∫ b : X, Real.exp (E (replace Λ (full (a,y)) b))*F (replace Λ (full (a,y)) b) ∂prior Λ) /
      ∫ b : X, Real.exp (E (replace Λ (full (a,y)) b)) ∂prior Λ) = _
    simp_rw [repl]
    unfold V
    simp_rw [split, Real.exp_add, mul_assoc]
    rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ (Real.exp_pos c).ne']
  have equal : (∫ p : X × Y, Real.exp (H p)*G p ∂η) = ∫ p : X × Y, Real.exp (H p)*R p ∂η := by
    dsimp only [η]
    rw [integral_prod_symm (fun p : X × Y => Real.exp (H p) * G p)
        ((contH.rexp.mul contG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_prod_symm (fun p : X × Y => Real.exp (H p) * R p)
        ((contH.rexp.mul contR).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change (∫ a : X, Real.exp (H (a,y))*G (a,y) ∂prior Λ) =
      ∫ a : X, Real.exp (H (a,y))*R (a,y) ∂prior Λ
    simp_rw [value]
    rw [integral_mul_const]
    have hi : Integrable (fun a : X => Real.exp (H (a,y))) (prior Λ) :=
      (contH.comp (continuous_id.prodMk continuous_const)).rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    let Z := ∫ a : X, Real.exp (H (a,y)) ∂prior Λ
    let I := ∫ a : X, Real.exp (H (a,y))*G (a,y) ∂prior Λ
    change I = Z * (I / Z)
    have hZ : Z ≠ 0 := (integral_exp_pos hi).ne'
    field_simp [hZ]
  rw [combined_cube_integral,combined_cube_integral,integral_tilted,integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div]
  congr 1
  have pack (f : SiteReflection.Config 3 L → ℝ) (hc : Continuous f) :
      (∫ s, f s ∂prior (BoxSite L)) = ∫ p, f (join p) ∂η :=
    ((paste_preserving L Λ hΛ).hasLaw.integral_comp hc.aestronglyMeasurable).symm
  rw [pack (fun s => Real.exp (finiteEnergy L β h s) * F (extendCube L s))
      ((finiteEnergy L β h).continuous.rexp.mul (F.continuous.comp (extendCube L).continuous)),
    pack (fun s => Real.exp (finiteEnergy L β h s) * readout Λ E F (extendCube L s))
      ((finiteEnergy L β h).continuous.rexp.mul ((readout Λ E F).continuous.comp (extendCube L).continuous))]
  exact equal

private theorem eventual_cube_window (β : ℝ) (h : ℕ → ℝ) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (Λ : Finset Site) (F : C(SpinField 3, ℝ)) :
    ∀ᶠ n in atTop, (∫ s, F s ∂(cubeLaw β (h n) (L n) : Measure _)) =
      ∫ s, readout Λ (localFieldEnergy β (h n) Λ) F s ∂(cubeLaw β (h n) (L n) : Measure _) := by
  let T := Λ ∪ Λ.biUnion (fun x => nearestSteps.image (fun z => x+z))
  have hin : ∀ᶠ n : ℕ in atTop, ∀ x ∈ T, x ∈ cube (L n) :=
    T.finite_toSet.eventually_all.mpr fun x _ => hL.eventually (BondMirror.ev_cube x)
  filter_upwards [hin] with n hn
  exact free_cube_field_conditional (L n) β (h n) Λ (fun x hx => hn x (Finset.mem_union_left _ hx))
    (fun x hx z hz => hn (x+z) (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x,hx,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩))) F

/-- Every weak limit of the actual positive-field finite free-cube laws
satisfies the local field specification. -/
theorem field_gibbs_of_free_cube_limit {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)}
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hP : Tendsto (fun n => cubeLaw β h (L n)) atTop (𝓝 P)) : IsFieldGibbs β h P := by
  intro Λ F
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP
  have hR := (ProbabilityMeasure.continuous_integral_continuousMap (readout Λ (localFieldEnergy β h Λ) F)).continuousAt.tendsto.comp hP
  exact tendsto_nhds_unique (hF.congr' (eventual_cube_window β (fun _ => h) hL Λ F)) hR

/-- Every weak limit of actual free cubes along simultaneous schedules
of growing volumes and vanishing fields satisfies the zero-field DLR equations. -/
theorem gibbs_of_joint_free_cube_limit {β : ℝ} {h : ℕ → ℝ} {L : ℕ → ℕ}
    {Q : ProbabilityMeasure (SpinField 3)} (hL : Tendsto L atTop atTop)
    (hz : Tendsto h atTop (𝓝 0))
    (hQ : Tendsto (fun n => cubeLaw β (h n) (L n)) atTop (𝓝 Q)) : IsNearestGibbs 3 β Q :=
  nearest_gibbs_of_eventual_field_windows hz hQ (eventual_cube_window β h hL)

/-- The same zero-field law whose dot pair has the rotation readouts is
a genuine nearest-neighbour Heisenberg DLR state. -/
theorem VanishingFieldOrigin.gibbs {β : ℝ} {Q : ProbabilityMeasure (SpinField 3)}
    (origin : VanishingFieldOrigin β Q) : IsNearestGibbs 3 β Q := by
  obtain ⟨h,P,_,hz,hP,hQ⟩ := origin
  exact nearest_gibbs_of_vanishing_field hz hQ fun n =>
    field_gibbs_of_free_cube_limit (L := id) tendsto_id (hP n).centered

#print axioms free_cube_field_conditional
#print axioms field_gibbs_of_free_cube_limit
#print axioms VanishingFieldOrigin.gibbs

end IsingScaling.Rotor.HeisenbergField

