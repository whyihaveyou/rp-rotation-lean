import MathlibProbe.RotorPeriodicStateRealization

/-! # Exact nearest-neighbour Gibbs boxes with a finite random boundary

Draw the exterior spins from an actual finite periodic sphere-spin law.
With these spins fixed, draw new spins in a finite box from the product
surface measure tilted by the original nearest-neighbour interaction at β.
The effective boundary of that interaction consists of the spins in the
adjacent lattice layer. The exterior sample itself uses only finitely many
spin variables. The resulting field has precisely that exterior law and
is invariant under a second Gibbs update of the box.

At fixed box size this update is weakly continuous and fixes every
nearest-neighbour DLR state. Apply it to the finite-torus approximants of
the physical mirror-selected state, then increase the box sizes. Choosing
large enough tori along one subsequence gives the same full spin-state
limit. The auxiliary pair interaction occurs only in the external sample.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology InnerProductSpace

namespace IsingScaling.Rotor.PressureSelection.NearestWindowRealization
open PeriodicStateRealization LocalGibbs PhysicalMirrorSelection IsingRotation Packet

private abbrev localEnergy (N : ℕ) (β : ℝ) (Λ : Finset Site) :=
  windowEnergy N Λ (nearestCoupling β) (summable_abs_nearest β)

/-- Sample the outside from B; inside Λ use the ordinary nearest-neighbour
Gibbs density, with the sampled exterior held fixed. -/
def boxLaw {N : ℕ} [NeZero N] (β : ℝ) (Λ : Finset Site) (B : ProbabilityMeasure (SpinField N)) :
    ProbabilityMeasure (SpinField N) :=
  ⟨kernel Λ (localEnergy N β Λ) ∘ₘ (B : Measure _), inferInstance⟩

/-- Exterior sites incident on a nearest-neighbour edge from the window. -/
def exteriorLayer (Λ : Finset Site) : Finset Site :=
  (Λ.biUnion fun x => nearestSteps.image (fun z => x+z)) \ Λ

/-- Conditional on a supplied boundary, the restriction to the box is
exactly the finite product surface law tilted by the nearest-neighbour
energy of all bonds incident on the box. -/
theorem nearestResample_inside (N : ℕ) [NeZero N] (β : ℝ) (Λ : Finset Site) (s : SpinField N) :
    (nearestResample N Λ β s : Measure (SpinField N)).map Λ.restrict =
      (windowPrior N Λ : Measure _).tilted (fun a => localEnergy N β Λ (replace Λ s a)) := by
  have hc : Continuous (Λ.restrict : SpinField N → WindowSpin N Λ) :=
    continuous_pi fun i => continuous_apply i.val
  have hr : Continuous (replace Λ s) :=
    (replace_continuous Λ).comp (continuous_const.prodMk continuous_id)
  change (Measure.map (replace Λ s) _).map Λ.restrict = _
  rw [Measure.map_map hc.measurable hr.measurable]
  have he : Λ.restrict ∘ replace Λ s = id := funext fun a => funext fun i => replace_inside Λ s a i.property
  rw [he, Measure.map_id]
  rfl

/-- Agreement just on the finite outer layer determines the complete
Borel distribution of the replacement spins in the window. -/
theorem nearestResample_inside_of_layer (N : ℕ) [NeZero N] (β : ℝ) (Λ : Finset Site)
    {s t : SpinField N} (h : ∀ x ∈ exteriorLayer Λ, s x = t x) :
    (nearestResample N Λ β s : Measure (SpinField N)).map Λ.restrict =
      (nearestResample N Λ β t : Measure (SpinField N)).map Λ.restrict := by
  rw [nearestResample_inside, nearestResample_inside]
  congr 1
  funext a
  let r := replace Λ s a
  let q := replace Λ t a
  have inside (x : Site) (hx : x ∈ Λ) : r x = q x :=
    (replace_inside Λ s a hx).trans (replace_inside Λ t a hx).symm
  have neighbour (x : Λ) (z : Site) (hz : z ∈ nearestSteps) : r (x.val+z) = q (x.val+z) := by
    by_cases hy : x.val+z ∈ Λ
    · exact inside _ hy
    · have hm : x.val+z ∈ exteriorLayer Λ := Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨x.val, x.property, Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩, hy⟩
      exact (replace_outside Λ s a hy).trans ((h _ hm).trans (replace_outside Λ t a hy).symm)
  change (∑ x : Λ, ∑' z : Site, nearestCoupling β z * ((if x.val+z ∈ Λ then (1:ℝ)/2 else 1) *
      ⟪(r x.val).val, (r (x.val+z)).val⟫_ℝ)) =
    ∑ x : Λ, ∑' z : Site, nearestCoupling β z * ((if x.val+z ∈ Λ then (1:ℝ)/2 else 1) *
      ⟪(q x.val).val, (q (x.val+z)).val⟫_ℝ)
  apply Finset.sum_congr rfl
  intro x _
  apply tsum_congr
  intro z
  by_cases hz : z ∈ nearestSteps
  · rw [inside _ x.property, neighbour x z hz]
  · simp [nearestCoupling, hz]

private theorem box_integral {N : ℕ} [NeZero N] (β : ℝ) (Λ : Finset Site)
    (B : ProbabilityMeasure (SpinField N)) (F : C(SpinField N, ℝ)) :
    (∫ s, F s ∂(boxLaw β Λ B : Measure _)) =
      ∫ s, readout Λ (localEnergy N β Λ) F s ∂(B : Measure _) := by
  change (∫ s, F s ∂(kernel Λ (localEnergy N β Λ) ∘ₘ (B : Measure _))) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp
    (F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

theorem boxLaw_continuous (N : ℕ) [NeZero N] (β : ℝ) (Λ : Finset Site) :
    Continuous (boxLaw (N := N) β Λ) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro F
  simp only [box_integral]
  exact ProbabilityMeasure.continuous_integral_continuousMap _

private theorem read_outside {N : ℕ} [NeZero N] (Λ : Finset Site) (E F : C(SpinField N, ℝ))
    (outside : ∀ s t : SpinField N, (∀ x ∉ Λ, s x = t x) → F s = F t) (s : SpinField N) :
    readout Λ E F s = F s := by
  have one : readout Λ E 1 s = 1 := by
    change (∫ _ : SpinField N, (1 : ℝ) ∂(resample Λ E s : Measure _)) = 1
    simp
  simpa only [mul_one, one] using (readout_outside_factor Λ E F 1 outside s)

/-- All continuous exterior tests have exactly their original boundary
expectation after sampling the finite Gibbs box. -/
theorem boxLaw_outside {N : ℕ} [NeZero N] (β : ℝ) (Λ : Finset Site)
    (B : ProbabilityMeasure (SpinField N)) (F : C(SpinField N, ℝ))
    (outside : ∀ s t : SpinField N, (∀ x ∉ Λ, s x = t x) → F s = F t) :
    (∫ s, F s ∂(boxLaw β Λ B : Measure _)) = ∫ s, F s ∂(B : Measure _) := by
  simp only [box_integral, read_outside Λ _ F outside]

/-- A second complete Gibbs resampling, at the same fixed exterior,
reproduces the entire field law of the finite box. -/
theorem boxLaw_idempotent {N : ℕ} [NeZero N] (β : ℝ) (Λ : Finset Site)
    (B : ProbabilityMeasure (SpinField N)) : boxLaw β Λ (boxLaw β Λ B) = boxLaw β Λ B := by
  let E := localEnergy N β Λ
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ s, F.toContinuousMap s ∂(boxLaw β Λ (boxLaw β Λ B) : Measure _)) = _
  rw [box_integral]
  change (∫ s, readout Λ E F.toContinuousMap s ∂(boxLaw β Λ B : Measure _)) =
    ∫ s, F.toContinuousMap s ∂(boxLaw β Λ B : Measure _)
  rw [box_integral, box_integral]
  refine integral_congr_ae (Eventually.of_forall fun s => read_outside Λ E _ ?_ s)
  intro f g he
  change (∫ t, F t ∂(resample Λ E f : Measure _)) = ∫ t, F t ∂(resample Λ E g : Measure _)
  rw [resample_eq_of_outside Λ E he]

theorem boxLaw_fixed {N : ℕ} [NeZero N] {β : ℝ} {Q : ProbabilityMeasure (SpinField N)}
    (h : IsNearestGibbs N β Q) (Λ : Finset Site) : boxLaw β Λ Q = Q :=
  ProbabilityMeasure.toMeasure_injective ((isGibbs_iff_kernel N _ _ Q).mp h Λ)

/-- At every spin dimension and ferromagnetic inverse temperature, one
common mirror-selected state can be obtained using any prescribed growing
boxes with the exact nearest-neighbour Gibbs interaction in their interiors.
Each random exterior is supplied by a larger explicitly specified finite
periodic law at a vanishing positive auxiliary strength. The limiting
state is chosen before the box schedule. -/
theorem exists_selected_nearest_boxes (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hzero : Tendsto δ atTop (𝓝 0)) :
    ∃ Q : ProbabilityMeasure (SpinField N), Selected N β Q ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), PeriodicHorizontal.FixedBy Q (signedPerm p s)) ∧
      InternalOrthogonal.AllInternalInvariant Q ∧
      ∀ L : ℕ → ℕ, ∃ u m : ℕ → ℕ, StrictMono u ∧ StrictMono m ∧ (∀ n, L n < m n) ∧
        Tendsto (fun n => evenLaw N β (δ (u n)) (m n)) atTop (𝓝 Q) ∧
        Tendsto (fun n => boxLaw β (cube (L n)) (evenLaw N β (δ (u n)) (m n))) atTop (𝓝 Q) := by
  let : PseudoMetricSpace (ProbabilityMeasure (SpinField N)) :=
    pseudoMetrizableSpacePseudoMetric _
  obtain ⟨Q, u, m, hu, hm, _, hfinite, selected, hs, hi⟩ :=
    exists_selected_periodic_sequence N hβ δ hδ hzero id
  refine ⟨Q, selected, hs, hi, ?_⟩
  intro L
  let A (k : ℕ) := evenLaw N β (δ (u k)) (m k)
  have row (n : ℕ) : Tendsto (fun k => boxLaw β (cube (L n)) (A k)) atTop (𝓝 Q) := by
    have h := (boxLaw_continuous N β (cube (L n))).continuousAt.tendsto.comp hfinite
    rwa [boxLaw_fixed selected.gibbs] at h
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have chooseSize (n : ℕ) : ∀ᶠ k : ℕ in atTop,
      L n < m k ∧ dist (boxLaw β (cube (L n)) (A k)) Q < ε n :=
    (hm.tendsto_atTop.eventually (eventually_gt_atTop (L n))).and (Metric.tendsto_nhds.mp (row n) (ε n) (hε n))
  obtain ⟨v, hv, hv'⟩ := extraction_forall_of_eventually chooseSize
  refine ⟨u ∘ v, m ∘ v, hu.comp hv, hm.comp hv, fun n => (hv' n).1, hfinite.comp hv.tendsto_atTop, ?_⟩
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun n => (hv' n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat)

#print axioms boxLaw_outside
#print axioms boxLaw_idempotent
#print axioms nearestResample_inside
#print axioms nearestResample_inside_of_layer
#print axioms exists_selected_nearest_boxes

end IsingScaling.Rotor.PressureSelection.NearestWindowRealization
