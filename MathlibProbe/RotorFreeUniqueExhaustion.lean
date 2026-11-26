import MathlibProbe.RotorNearestWindowRealization
import MathlibProbe.ModelPacketCubeReadout

/-! # Free induced domains at a unique sphere-spin Gibbs state

The finite energy counts each nearest-neighbour bond internal to the
domain once. Filling sites outside the domain embeds the finite sample
in the full spin-field space. Once a window and its neighbours are
inside, the change of finite energy under a window update equals the
change of the infinite-lattice window energy. Disintegration of the
finite product sphere law gives the exact local conditional identity.
Every local weak limit on an exhaustion is therefore Gibbs. Uniqueness
identifies the weak limit of the entire sequence, including sequences of
irregular domains and varying exterior fills.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace ProbabilityTheory
namespace IsingScaling.Rotor.PressureSelection.FreeExhaustion
open LocalGibbs

variable {N : ℕ}

private def bond (β : ℝ) (s : SpinField N) (x y : Site) : ℝ :=
  nearestCoupling β (y-x) * ⟪(s x).val,(s y).val⟫_ℝ

private theorem bond_comm (β : ℝ) (s : SpinField N) (x y : Site) : bond β s y x = bond β s x y := by
  simp only [bond,show x-y= -(y-x) by abel,nearestCoupling_even,real_inner_comm (s y).val]

/-- Open-boundary Hamiltonian, using the ordinary six lattice neighbours. -/
def freeEnergy (N : ℕ) (β : ℝ) (D : Finset Site) : C(SpinField N,ℝ) where
  toFun s := (∑ x ∈ D, ∑ y ∈ D, bond β s x y)/2
  continuous_toFun := (continuous_finsetSum _ (fun x _ => continuous_finsetSum _ (fun y _ =>
    continuous_const.mul (by fun_prop)))).div_const _

private abbrev localEnergy (N : ℕ) (β : ℝ) (Λ : Finset Site) :=
  windowEnergy N Λ (nearestCoupling β) (summable_abs_nearest β)

private def incidence (Λ : Finset Site) (x y : Site) : ℝ :=
  if x ∈ Λ then (if y ∈ Λ then 1/2 else 1) else 0

private theorem sum_window (β : ℝ) (Λ D : Finset Site) (hΛ : Λ ⊆ D)
    (hc : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D) (s : SpinField N) :
    localEnergy N β Λ s = ∑ x ∈ D, ∑ y ∈ D, incidence Λ x y * bond β s x y := by
  let B (x y : Site) := incidence Λ x y * bond β s x y
  have row (x : Λ) : (∑' z : Site, nearestCoupling β z *
      ((if x.val+z ∈ Λ then (1:ℝ)/2 else 1) * ⟪(s x.val).val,(s (x.val+z)).val⟫_ℝ)) =
      ∑ y ∈ D, B x.val y := by
    calc
      _ = ∑' z, B x.val (x.val+z) := by
        apply tsum_congr
        intro z
        simp only [B,incidence,bond,x.property,ite_true,add_sub_cancel_left]
        ring
      _ = ∑' y, B x.val y := (Equiv.addLeft x.val).tsum_eq _
      _ = _ := tsum_eq_sum fun y hy => by
        have hz : y-x.val ∉ nearestSteps := fun h => hy (by simpa using hc x.val x.property _ h)
        simp [B,bond,nearestCoupling,hz]
  change (∑ x : Λ, ∑' z : Site, nearestCoupling β z *
    ((if x.val+z ∈ Λ then (1:ℝ)/2 else 1) * ⟪(s x.val).val,(s (x.val+z)).val⟫_ℝ)) = _
  simp only [row]
  rw [Finset.sum_coe_sort Λ (fun x => ∑ y ∈ D, B x y)]
  exact Finset.sum_subset hΛ (fun x _ hx => by simp [B,incidence,hx])

/-- On an induced domain containing the interaction collar, replacing the
window changes the finite energy by exactly the specification energy change. -/
theorem free_energy_change (β : ℝ) (Λ D : Finset Site) (hΛ : Λ ⊆ D)
    (hc : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D) (s t : SpinField N)
    (out : ∀ x ∉ Λ, s x = t x) :
    freeEnergy N β D s-freeEnergy N β D t = localEnergy N β Λ s-localEnergy N β Λ t := by
  let d (x y : Site) := bond β s x y-bond β t x y
  have ds (x y : Site) : d y x=d x y := by simp only [d,bond_comm β s y x,bond_comm β t y x]
  have split (x y : Site) : d x y = incidence Λ x y*d x y + incidence Λ y x*d y x := by
    rw [ds]
    by_cases hx : x ∈ Λ <;> by_cases hy : y ∈ Λ
    · simp [incidence,hx,hy]; ring
    · simp [incidence,hx,hy]
    · simp [incidence,hx,hy]
    · simp [incidence,hx,hy,d,bond,out x hx,out y hy]
  have eq := Finset.sum_congr (s₁:=D) rfl (fun x _ => Finset.sum_congr (s₁:=D) rfl (fun y _ => split x y))
  simp only [Finset.sum_add_distrib] at eq
  rw [Finset.sum_comm (f:=fun x y => incidence Λ y x * d y x)] at eq
  have hf : freeEnergy N β D s - freeEnergy N β D t = (∑ x ∈ D, ∑ y ∈ D, d x y)/2 := by
    change (∑ x ∈ D, ∑ y ∈ D, bond β s x y)/2 - (∑ x ∈ D, ∑ y ∈ D, bond β t x y)/2 = _
    simp only [d,Finset.sum_sub_distrib,sub_div]
  rw [hf,sum_window β Λ D hΛ hc s,sum_window β Λ D hΛ hc t]
  simp only [←Finset.sum_sub_distrib,←mul_sub]
  linarith

private abbrev Outside (D Λ : Finset Site) := {x : D // x.val ∉ Λ}

private def splitIndex (D Λ : Finset Site) (hΛ : Λ ⊆ D) : D ≃ Λ ⊕ Outside D Λ where
  toFun x := if h : x.val ∈ Λ then .inl ⟨x.val,h⟩ else .inr ⟨x,h⟩
  invFun := Sum.elim (fun x => ⟨x.val,hΛ x.property⟩) Subtype.val
  left_inv x := by by_cases hx : x.val ∈ Λ <;> simp [hx]
  right_inv x := by cases x with
    | inl a => simp [a.property]
    | inr b => simp [b.property]

private def join (D Λ : Finset Site) (hΛ : Λ ⊆ D)
    (p : WindowSpin N Λ × (Outside D Λ → Spin N)) : WindowSpin N D :=
  fun x => Sum.elim p.1 p.2 (splitIndex D Λ hΛ x)

private theorem join_continuous (D Λ : Finset Site) (hΛ : Λ ⊆ D) : Continuous (join (N:=N) D Λ hΛ) := by
  apply continuous_pi
  intro x
  unfold join
  cases splitIndex D Λ hΛ x <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop

private abbrev prior (N : ℕ) (T : Type*) [Fintype T] : Measure (T → Spin N) :=
  Measure.pi (fun _ => SiteReflection.surfacePrior N)

private theorem join_preserving (N : ℕ) [NeZero N] (D Λ : Finset Site) (hΛ : Λ ⊆ D) :
    MeasurePreserving (join D Λ hΛ) ((prior N Λ).prod (prior N (Outside D Λ))) (prior N D) := by
  let e := splitIndex D Λ hΛ
  let A := fun _ : Λ ⊕ Outside D Λ => SiteReflection.surfacePrior N
  have h1 := measurePreserving_sumPiEquivProdPi_symm A
  have h2 := (measurePreserving_piCongrLeft A e).symm
  convert h2.comp h1 using 1
  funext p x
  change Sum.elim p.1 p.2 (e x) = (Equiv.piCongrLeft (fun _ => Spin N) e).symm _ x
  rw [Equiv.piCongrLeft_symm_apply]
  cases e x <;> rfl

private theorem atSite (D Λ : Finset Site) (hΛ : Λ ⊆ D) (fill : SpinField N)
    (p : WindowSpin N Λ × (Outside D Λ → Spin N)) (x : Site) :
    replace D fill (join D Λ hΛ p) x = if h : x ∈ Λ then p.1 ⟨x,h⟩ else
      if hD : x ∈ D then p.2 ⟨⟨x,hD⟩,h⟩ else fill x := by
  by_cases hx : x ∈ Λ
  · simp [replace,join,splitIndex,hx,hΛ hx]
  · by_cases hd : x ∈ D <;> simp [replace,join,splitIndex,hx,hd]

/-- Tower identity for a finite product Gibbs integral. The two energies
may differ by an arbitrary function of the complement of the inner window. -/
theorem resample_subwindow_integral [NeZero N] {D Λ : Finset Site} (hΛ : Λ ⊆ D)
    (H E : C(SpinField N,ℝ))
    (delta : ∀ s t : SpinField N, (∀ x ∉ Λ, s x=t x) → H s-H t=E s-E t)
    (fill : SpinField N) (F : C(SpinField N,ℝ)) :
    (∫ t, F t ∂(resample D H fill : Measure _)) =
      ∫ t, readout Λ E F t ∂(resample D H fill : Measure _) := by
  let X := WindowSpin N Λ
  let Y := Outside D Λ → Spin N
  let η := (prior N Λ).prod (prior N (Outside D Λ))
  let extend := replace D fill
  let full (p : X × Y) := extend (join D Λ hΛ p)
  let A (p : X × Y) := H (full p)
  let G (p : X × Y) := F (full p)
  let R (p : X × Y) := readout Λ E F (full p)
  let V (y : Y) := (∫ a : X, Real.exp (A (a,y))*G (a,y) ∂prior N Λ) /
    ∫ a : X, Real.exp (A (a,y)) ∂prior N Λ
  have hExt : Continuous extend := (replace_continuous D).comp (continuous_const.prodMk continuous_id)
  have hfull : Continuous full := hExt.comp (join_continuous D Λ hΛ)
  have hA : Continuous A := H.continuous.comp hfull
  have hG : Continuous G := F.continuous.comp hfull
  have hR : Continuous R := (readout Λ E F).continuous.comp hfull
  have read (a : X) (y : Y) : R (a,y) = V y := by
    let c := A (a,y)-E (full (a,y))
    have split (b : X) : A (b,y) = c+E (full (b,y)) := by
      have out (x : Site) (hx : x ∉ Λ) : full (b,y) x = full (a,y) x := by
        simp only [full,extend,atSite,hx,dite_false]
      have h := delta (full (b,y)) (full (a,y)) out
      change A (b,y)-A (a,y) = _ at h
      dsimp only [c]
      linarith
    have update (b : X) : replace Λ (full (a,y)) b = full (b,y) := by
      funext x
      by_cases hx : x ∈ Λ <;> simp [full,extend,replace,atSite,hx]
    change (∫ t, F t ∂(resample Λ E (full (a,y)) : Measure _)) = V y
    rw [resample_integral]
    change ((∫ b : X, Real.exp (E (replace Λ (full (a,y)) b))*F (replace Λ (full (a,y)) b) ∂prior N Λ) /
      ∫ b : X, Real.exp (E (replace Λ (full (a,y)) b)) ∂prior N Λ) = _
    simp_rw [update]
    have den : (∫ b : X, Real.exp (A (b,y)) ∂prior N Λ) =
        Real.exp c * ∫ b : X, Real.exp (E (full (b,y))) ∂prior N Λ := by
      simp only [split,Real.exp_add]
      exact integral_const_mul _ _
    have num : (∫ b : X, Real.exp (A (b,y))*G (b,y) ∂prior N Λ) =
        Real.exp c * ∫ b : X, Real.exp (E (full (b,y)))*G (b,y) ∂prior N Λ := by
      simp only [split,Real.exp_add,mul_assoc]
      exact integral_const_mul _ _
    unfold V
    rw [num,den,mul_div_mul_left _ _ (Real.exp_pos c).ne']
  have equal : (∫ p : X × Y, Real.exp (A p)*G p ∂η) = ∫ p : X × Y, Real.exp (A p)*R p ∂η := by
    rw [integral_prod_symm (fun p : X × Y => Real.exp (A p)*G p)
        ((hA.rexp.mul hG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_prod_symm (fun p : X × Y => Real.exp (A p)*R p)
        ((hA.rexp.mul hR).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change (∫ a : X, Real.exp (A (a,y))*G (a,y) ∂prior N Λ) =
      ∫ a : X, Real.exp (A (a,y))*R (a,y) ∂prior N Λ
    simp_rw [read]
    rw [integral_mul_const]
    have hi : Integrable (fun a : X => Real.exp (A (a,y))) (prior N Λ) :=
      (hA.comp (continuous_id.prodMk continuous_const)).rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    unfold V
    field_simp [(integral_exp_pos hi).ne'] <;> rfl
  rw [resample_integral,resample_integral]
  apply congrArg (fun t : ℝ => t / ∫ a, Real.exp (H (extend a)) ∂prior N D)
  have pack (B : SpinField N → ℝ) (hc : Continuous B) :
      (∫ s : WindowSpin N D, B (extend s) ∂prior N D) = ∫ p, B (full p) ∂η :=
    ((join_preserving N D Λ hΛ).hasLaw.integral_comp (hc.comp hExt).aestronglyMeasurable).symm
  exact (pack (fun s => Real.exp (H s)*F s) (H.continuous.rexp.mul F.continuous)).trans
    (equal.trans (pack (fun s => Real.exp (H s)*readout Λ E F s)
      (H.continuous.rexp.mul (readout Λ E F).continuous)).symm)

/-- The induced finite free Gibbs sample, with arbitrary unused exterior
coordinates supplied by fill. Its density involves only bonds internal to D. -/
def freeDomainLaw (N : ℕ) [NeZero N] (β : ℝ) (D : Finset Site) (fill : SpinField N) :
    ProbabilityMeasure (SpinField N) := resample D (freeEnergy N β D) fill

theorem freeDomain_conditional [NeZero N] {D Λ : Finset Site} (hΛ : Λ ⊆ D)
    (hc : ∀ x ∈ Λ, ∀ z ∈ nearestSteps, x+z ∈ D) (β : ℝ) (fill : SpinField N) (F : C(SpinField N,ℝ)) :
    (∫ s, F s ∂(freeDomainLaw N β D fill : Measure _)) =
      ∫ s, readout Λ (localEnergy N β Λ) F s ∂(freeDomainLaw N β D fill : Measure _) :=
  resample_subwindow_integral hΛ _ _ (free_energy_change β Λ D hΛ hc) fill F

/-- Every weak limit is a nearest-neighbour DLR state. Neither nesting of
the domains nor any consistency of the exterior coordinate fills is required. -/
theorem gibbs_of_free_exhaustion [NeZero N] {β : ℝ} {D : ℕ → Finset Site}
    (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField N)
    {P : ProbabilityMeasure (SpinField N)}
    (hP : Tendsto (fun n => freeDomainLaw N β (D n) (fill n)) atTop (𝓝 P)) : IsNearestGibbs N β P := by
  intro Λ F
  let T := Λ ∪ Λ.biUnion (fun x => nearestSteps.image (fun z => x+z))
  have hT : ∀ᶠ n in atTop, ∀ x ∈ T, x ∈ D n := T.finite_toSet.eventually_all.mpr (fun x _ => hex x)
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP
  have hR := (ProbabilityMeasure.continuous_integral_continuousMap (readout Λ (localEnergy N β Λ) F)).continuousAt.tendsto.comp hP
  apply tendsto_nhds_unique (hF.congr' _) hR
  filter_upwards [hT] with n hn
  exact freeDomain_conditional (fun x hx => hn x (Finset.mem_union_left _ hx))
    (fun x hx z hz => hn (x+z) (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x,hx,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩))) β (fill n) F

/-- Under uniqueness, the entire sequence of actual finite free laws on
any exhausting induced domains has the same weak limit. -/
theorem freeDomain_tendsto_of_unique (N : ℕ) [NeZero N] {β : ℝ} (P : ProbabilityMeasure (SpinField N))
    (unique : ∀ Q : ProbabilityMeasure (SpinField N), IsNearestGibbs N β Q → Q=P)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField N) :
    Tendsto (fun n => freeDomainLaw N β (D n) (fill n)) atTop (𝓝 P) := by
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨Q,v,hv,hQ,_⟩ := spinField_subsequence N (fun n => freeDomainLaw N β (D (f n)) (fill (f n)))
  have hidx := hf.comp hv.tendsto_atTop
  have hg := gibbs_of_free_exhaustion (D:=fun n => D (f (v n))) (fun x => hidx.eventually (hex x))
    (fun n => fill (f (v n))) hQ
  exact ⟨v,unique Q hg ▸ hQ⟩

/-- Even when there are several Gibbs states, actual free finite induced
domains along any given exhaustion have a full DLR accumulation point. -/
theorem exists_free_gibbs_subsequence (N : ℕ) [NeZero N] (β : ℝ)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField N) :
    ∃ (P : ProbabilityMeasure (SpinField N)) (u : ℕ → ℕ), StrictMono u ∧
      Tendsto (fun n => freeDomainLaw N β (D (u n)) (fill (u n))) atTop (𝓝 P) ∧ IsNearestGibbs N β P := by
  obtain ⟨P,u,hu,hP,_⟩ := spinField_subsequence N (fun n => freeDomainLaw N β (D n) (fill n))
  exact ⟨P,u,hu,hP,gibbs_of_free_exhaustion (D:=fun n => D (u n))
    (fun x => hu.tendsto_atTop.eventually (hex x)) (fun n => fill (u n)) hP⟩

/-- The physical fixed-boundary specification is consistent under *any*
nested window update, including windows touching the finite domain boundary. -/
theorem nearest_subwindow_integral [NeZero N] {D Λ : Finset Site} (hΛ : Λ ⊆ D)
    (β : ℝ) (boundary : SpinField N) (F : C(SpinField N,ℝ)) :
    (∫ s, F s ∂(nearestResample N D β boundary : Measure _)) =
      ∫ s, readout Λ (localEnergy N β Λ) F s ∂(nearestResample N D β boundary : Measure _) := by
  apply resample_subwindow_integral hΛ
  intro s t hst
  let T := D ∪ D.biUnion (fun x => nearestSteps.image (fun z => x+z))
  have hD : D ⊆ T := Finset.subset_union_left
  have hc (x : Site) (hx : x ∈ D) (z : Site) (hz : z ∈ nearestSteps) : x+z ∈ T :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩)
  have h1 := free_energy_change β D T hD hc s t (fun x hx => hst x fun h => hx (hΛ h))
  have h2 := free_energy_change β Λ T (hΛ.trans hD) (fun x hx => hc x (hΛ hx)) s t hst
  exact h1.symm.trans h2

private theorem boundary_integral [NeZero N] (β : ℝ) (D : Finset Site)
    (B : ProbabilityMeasure (SpinField N)) (F : C(SpinField N,ℝ)) :
    (∫ s, F s ∂(NearestWindowRealization.boxLaw β D B : Measure _)) =
      ∫ s, readout D (localEnergy N β D) F s ∂(B : Measure _) := by
  change (∫ s, F s ∂(kernel D (localEnergy N β D) ∘ₘ (B : Measure _))) = _
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.Kernel.integral_comp
    (F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

/-- Random exterior laws B can vary with the volume. Here all crossing
bonds act with their physical nearest-neighbour strength. -/
theorem gibbs_of_boundary_exhaustion [NeZero N] {β : ℝ} {D : ℕ → Finset Site}
    (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (B : ℕ → ProbabilityMeasure (SpinField N))
    {P : ProbabilityMeasure (SpinField N)}
    (hP : Tendsto (fun n => NearestWindowRealization.boxLaw β (D n) (B n)) atTop (𝓝 P)) :
    IsNearestGibbs N β P := by
  intro Λ F
  let G := readout Λ (localEnergy N β Λ) F
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP
  have hG := (ProbabilityMeasure.continuous_integral_continuousMap G).continuousAt.tendsto.comp hP
  apply tendsto_nhds_unique (hF.congr' _) hG
  have hΛ : ∀ᶠ n in atTop, Λ ⊆ D n := Λ.finite_toSet.eventually_all.mpr (fun x _ => hex x)
  filter_upwards [hΛ] with n hn
  change (∫ s, F s ∂(NearestWindowRealization.boxLaw β (D n) (B n) : Measure _)) =
    ∫ s, G s ∂(NearestWindowRealization.boxLaw β (D n) (B n) : Measure _)
  rw [boundary_integral,boundary_integral]
  exact integral_congr_ae (Eventually.of_forall fun s => nearest_subwindow_integral hn β s F)

theorem boundary_tendsto_of_unique (N : ℕ) [NeZero N] {β : ℝ} (P : ProbabilityMeasure (SpinField N))
    (unique : ∀ Q : ProbabilityMeasure (SpinField N), IsNearestGibbs N β Q → Q=P)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n)
    (B : ℕ → ProbabilityMeasure (SpinField N)) :
    Tendsto (fun n => NearestWindowRealization.boxLaw β (D n) (B n)) atTop (𝓝 P) := by
  apply tendsto_of_subseq_tendsto
  intro f hf
  obtain ⟨Q,v,hv,hQ,_⟩ := spinField_subsequence N (fun n => NearestWindowRealization.boxLaw β (D (f n)) (B (f n)))
  have hidx := hf.comp hv.tendsto_atTop
  have hg := gibbs_of_boundary_exhaustion (D:=fun n => D (f (v n))) (fun x => hidx.eventually (hex x))
    (fun n => B (f (v n))) hQ
  exact ⟨v,unique Q hg ▸ hQ⟩

/-- Restricting the field to D recovers exactly the finite surface-product
Gibbs law with couplings β on induced nearest-neighbour edges. -/
theorem freeDomain_marginal (N : ℕ) [NeZero N] (β : ℝ) (D : Finset Site) (fill : SpinField N) :
    (freeDomainLaw N β D fill : Measure _).map (D.restrict : SpinField N → WindowSpin N D) =
      (sphereGibbs N (fun x y : D => nearestCoupling β (y.val-x.val)) : Measure (WindowSpin N D)) := by
  have hc : Continuous (D.restrict : SpinField N → WindowSpin N D) := continuous_pi fun i => continuous_apply i.val
  have hr : Continuous (replace D fill) := (replace_continuous D).comp (continuous_const.prodMk continuous_id)
  change (Measure.map (replace D fill) _).map D.restrict = _
  rw [Measure.map_map hc.measurable hr.measurable]
  have hid : D.restrict ∘ replace D fill = id := funext fun a => funext fun i => replace_inside D fill a i.property
  rw [hid,Measure.map_id]
  change (prior N D).tilted (fun s => freeEnergy N β D (replace D fill s)) = (prior N D).tilted _
  congr 1
  funext s
  change (∑ x ∈ D, ∑ y ∈ D, bond β (replace D fill s) x y)/2 =
    (∑ x : D, ∑ y : D, nearestCoupling β (y.val-x.val)*⟪(s x).val,(s y).val⟫_ℝ)/2
  have innerSum (x : D) : (∑ y ∈ D, bond β (replace D fill s) x.val y) =
      ∑ y : D, nearestCoupling β (y.val-x.val) * ⟪(s x).val,(s y).val⟫_ℝ := by
    rw [← Finset.sum_coe_sort D (fun y => bond β (replace D fill s) x.val y)]
    simp only [bond,replace_inside D fill s x.property]
    exact Finset.sum_congr rfl fun y _ => by rw [replace_inside D fill s y.property]
  rw [← Finset.sum_coe_sort D (fun x => ∑ y ∈ D, bond β (replace D fill s) x y)]
  simp only [innerSum]

/-- Finite-volume pair read, extended by zero when a tested site lies outside D. -/
def freePair (N : ℕ) [NeZero N] (β : ℝ) (D : Finset Site) (x y : Site) : ℝ :=
  if hx : x ∈ D then if hy : y ∈ D then
    dotPair N (fun a b : D => nearestCoupling β (b.val-a.val)) ⟨x,hx⟩ ⟨y,hy⟩ else 0 else 0

theorem freeDomain_pair (N : ℕ) [NeZero N] (β : ℝ) (D : Finset Site) (fill : SpinField N)
    {x y : Site} (hx : x ∈ D) (hy : y ∈ D) :
    (∫ s, fieldDot N x y s ∂(freeDomainLaw N β D fill : Measure _)) = freePair N β D x y := by
  let X : D := ⟨x,hx⟩
  let Y : D := ⟨y,hy⟩
  let A (s : D → Spin N) := ⟪(s X).val,(s Y).val⟫_ℝ
  have ha : Continuous A := by unfold A; fun_prop
  have hr : Continuous (D.restrict : SpinField N → WindowSpin N D) := continuous_pi fun i => continuous_apply i.val
  have H := gibbs_integral_dot N (fun a b : D => nearestCoupling β (b.val-a.val)) X Y
  change (∫ s, A s ∂(sphereGibbs N (fun a b : D => nearestCoupling β (b.val-a.val)) :
    Measure (WindowSpin N D))) = _ at H
  rw [←freeDomain_marginal N β D fill,integral_map hr.measurable.aemeasurable ha.aestronglyMeasurable] at H
  change (∫ s, fieldDot N x y s ∂(freeDomainLaw N β D fill : Measure _)) =
    dotPair N (fun a b : D => nearestCoupling β (b.val-a.val)) X Y at H
  simpa only [freePair,hx,hy,dite_true] using H

theorem freePair_cube (N : ℕ) [NeZero N] (β : ℝ) (L : ℕ) (x y : Site) :
    freePair N β (cube L) x y = SiteReflection.freePair (SiteReflection.surfacePrior N) β L x y := by
  by_cases hx : x ∈ cube L <;> by_cases hy : y ∈ cube L
  all_goals simp only [freePair,SiteReflection.freePair,hx,hy,↓reduceDIte]
  let H (a b : BoxSite L) := nearestCoupling β (b.val-a.val)
  have he (s : SiteReflection.Config N L) : energy H s = β*SiteReflection.energy s := by
    change (∑ a : BoxSite L, ∑ b : BoxSite L, H a b * ⟪(s a).val,(s b).val⟫_ℝ)/2 =
      β * ((∑ a : BoxSite L, ∑ b : BoxSite L,
        if latticeDistance a b=1 then ⟪(s a).val,(s b).val⟫_ℝ else 0)/2)
    rw [←mul_div_assoc]
    simp only [H,nearestCoupling_at_pair,Finset.mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
  let μ := prior N (BoxSite L)
  change ((∫ s : SiteReflection.Config N L, Real.exp (energy H s) *
    ⟪(s ⟨x,hx⟩).val,(s ⟨y,hy⟩).val⟫_ℝ ∂μ) / ∫ s, Real.exp (energy H s) ∂μ) = _
  simp only [he,SiteReflection.boxCorrelation,SiteReflection.partition]
  rfl

/-- The zero extensions of the original finite integrals have a common
stationary limit at all pairs along every free exhaustion in the uniqueness regime. -/
theorem freePair_tendsto_of_unique (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (P : ProbabilityMeasure (SpinField N)) (unique : ∀ Q, IsNearestGibbs N β Q → Q=P)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (x y : Site) :
    Tendsto (fun n => freePair N β (D n) x y) atTop (𝓝 (fieldPair P (x-y))) := by
  obtain ⟨Q,hQ⟩ := PhysicalMirrorSelection.exists_state N hβ
  have hstat : ShiftInvariant P := unique Q hQ.gibbs ▸ hQ.stationary
  let fill : SpinField N := fun _ => ⟨EuclideanSpace.single (0 : Fin N) 1,by simp⟩
  have h := (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot N x y)).continuousAt.tendsto.comp
    (freeDomain_tendsto_of_unique N P unique D hex (fun _ => fill))
  rw [stationary_dot_integral hstat] at h
  apply h.congr'
  filter_upwards [hex x,hex y] with n hx hy
  exact freeDomain_pair N β (D n) fill hx hy

theorem stationary_freeCubePair_of_unique (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (P : ProbabilityMeasure (SpinField N)) (unique : ∀ Q, IsNearestGibbs N β Q → Q=P) :
    IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β id (fieldPair P) := by
  intro x y
  simpa only [freePair_cube,id_eq] using freePair_tendsto_of_unique N hβ P unique cube BondMirror.ev_cube x y

#print axioms resample_subwindow_integral
#print axioms freeDomain_conditional
#print axioms gibbs_of_free_exhaustion
#print axioms freeDomain_tendsto_of_unique
#print axioms exists_free_gibbs_subsequence
#print axioms nearest_subwindow_integral
#print axioms gibbs_of_boundary_exhaustion
#print axioms boundary_tendsto_of_unique
#print axioms freeDomain_marginal
#print axioms freeDomain_pair
#print axioms freePair_cube
#print axioms freePair_tendsto_of_unique
#print axioms stationary_freeCubePair_of_unique
end IsingScaling.Rotor.PressureSelection.FreeExhaustion
