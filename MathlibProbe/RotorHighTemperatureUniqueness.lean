import MathlibProbe.RotorDobrushinComparison
import MathlibProbe.RotorDobrushinSite
import MathlibProbe.RotorFreeUniqueExhaustion
import MathlibProbe.ModelPacketCubeReadout

/-! # The unique high-temperature sphere-spin law and its two-point tangents

For `6 * (exp (4*β) - 1) < 1` the actual single-site update contracts
the sum of coordinate oscillations. Invariance under this update follows
from the singleton case of the nearest-neighbour Gibbs equations. Thus
all finite free induced-domain exhaustions and all finite boxes with
prescribed exterior laws converge to the same Gibbs probability. Its
dot correlation has the rotational two-point theorem with the original
sharp susceptibility.
-/

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology CompactlySupported
namespace IsingScaling.Rotor.PressureSelection.HighTemperature
open LocalGibbs Dobrushin ModelPackets

/-- The signed axial neighbours, translated to the update site. -/
def neighbors (i : Site) : Finset Site := nearestSteps.image fun z => i+z

theorem mem_neighbors {i j : Site} : j ∈ neighbors i ↔ j-i ∈ nearestSteps := by
  constructor
  · rintro hj
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hj
    simpa using hz
  · intro h
    exact Finset.mem_image.mpr ⟨j-i, h, by abel⟩

theorem mem_neighbors_iff_distance {i j : Site} : j ∈ neighbors i ↔ latticeDistance i j = 1 := by
  rw [mem_neighbors, mem_nearestSteps_iff_latticeDistance]
  have hd : latticeDistance 0 (j-i) = latticeDistance i j := by
    apply Finset.sum_congr rfl
    intro k _
    simp [Pi.sub_apply]
  rw [hd]

theorem card_neighbors (i : Site) : (neighbors i).card = 6 := by
  rw [neighbors, Finset.card_image_of_injective _ (add_right_injective i)]
  let v (p : Fin 3 × Bool) : Site := Pi.single p.1 (if p.2 then (1 : ℤ) else -1)
  have hv : Function.Injective v := by
    rintro ⟨a,b⟩ ⟨a',b'⟩ he
    have haa : a = a' := by
      by_contra hn
      have h := congrFun he a
      cases b <;> simp [v, Pi.single_eq_of_ne hn] at h
    subst a'
    have h := congrFun he a
    cases b <;> cases b' <;> simp_all [v]
  change (Finset.univ.image v).card = 6
  rw [Finset.card_image_of_injective _ hv]
  decide

private theorem nearest_gibbs_eq_of_influence {N : ℕ} [NeZero N] {β d : ℝ} (hd : 0 ≤ d)
    (hsmall : 6*d < 1)
    (hother : ∀ {i j : Site}, j ≠ i → ∀ {F : C(SpinField N, ℝ)} {ai aj : ℝ},
      OscBound F i ai → OscBound F j aj →
        OscBound (update β i F) j (aj + if j-i ∈ nearestSteps then d*ai else 0))
    {P Q : ProbabilityMeasure (SpinField N)}
    (hP : IsNearestGibbs N β P) (hQ : IsNearestGibbs N β Q) : P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  apply DobrushinComparison.measure_eq_of_site_bounds neighbors 6 (fun i => (card_neighbors i).le)
    d hd hsmall (update β)
    (fun i F => update_self β i F)
    (fun i j F ai aj hij hi hj s t h => by
      have bound := hother hij (F := F) hi hj s t h
      by_cases hnear : j ∈ neighbors i
      · simpa only [ite_eq_left hnear, ite_eq_left (mem_neighbors.mp hnear)] using bound
      · simpa only [ite_eq_right hnear, ite_eq_right (mt mem_neighbors.mpr hnear)] using bound)
    (P : Measure (SpinField N)) (Q : Measure (SpinField N))
  · exact fun i F => (hP {i} F).symm
  · exact fun i F => (hQ {i} F).symm

/-- Dobrushin uniqueness with the normalized likelihood cap. -/
theorem nearest_gibbs_eq {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β) - 1) < 1) {P Q : ProbabilityMeasure (SpinField N)}
    (hP : IsNearestGibbs N β P) (hQ : IsNearestGibbs N β Q) : P = Q :=
  nearest_gibbs_eq_of_influence (sub_nonneg.mpr (Real.one_le_exp (by positivity))) hsmall
    (by intro i j hij F ai aj hi hj; exact update_other hβ hij hi hj) hP hQ

/-- The sharper single-neighbour comparison gives the physical six-neighbour
criterion for all finite internal dimensions, including the Heisenberg rotor. -/
theorem nearest_gibbs_eq_tanh {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * Real.tanh β < 1) {P Q : ProbabilityMeasure (SpinField N)}
    (hP : IsNearestGibbs N β P) (hQ : IsNearestGibbs N β Q) : P = Q := by
  have hd : 0 ≤ Real.tanh β := by
    rw [← tanh_exp_ratio]
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (by positivity)
  exact nearest_gibbs_eq_of_influence hd hsmall
    (by intro i j hij F ai aj hi hj; exact update_other_tanh hβ hij hi hj) hP hQ

theorem exists_unique_nearest_gibbs_tanh (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * Real.tanh β < 1) :
    ∃! P : ProbabilityMeasure (SpinField N), IsNearestGibbs N β P := by
  obtain ⟨P,hP⟩ := PhysicalMirrorSelection.exists_state N hβ
  exact ⟨P,hP.gibbs,fun Q hQ => nearest_gibbs_eq_tanh hβ hsmall hQ hP.gibbs⟩

theorem exists_unique_nearest_gibbs (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β)-1) < 1) :
    ∃! P : ProbabilityMeasure (SpinField N), IsNearestGibbs N β P := by
  obtain ⟨P, h⟩ := PhysicalMirrorSelection.exists_state N hβ
  exact ⟨P, h.gibbs, fun Q hQ => nearest_gibbs_eq hβ hsmall hQ h.gibbs⟩

def state (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6 * (Real.exp (4*β)-1) < 1) :
    ProbabilityMeasure (SpinField N) := (exists_unique_nearest_gibbs N hβ hsmall).exists.choose

theorem state_gibbs (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6 * (Real.exp (4*β)-1) < 1) :
    IsNearestGibbs N β (state N hβ hsmall) := (exists_unique_nearest_gibbs N hβ hsmall).exists.choose_spec

theorem eq_state (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    (Q : ProbabilityMeasure (SpinField N)) (hQ : IsNearestGibbs N β Q) : Q = state N hβ hsmall :=
  nearest_gibbs_eq hβ hsmall hQ (state_gibbs N hβ hsmall)

private theorem selected (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β)-1) < 1) :
    PhysicalMirrorSelection.Selected N β (state N hβ hsmall) := by
  obtain ⟨Q,hQ⟩ := PhysicalMirrorSelection.exists_state N hβ
  exact eq_state N hβ hsmall Q hQ.gibbs ▸ hQ

/-- The domains may be nonnested and the exterior fill may change at every
volume. The finite free law uses only the induced nearest-neighbour bonds. -/
theorem freeDomain_tendsto (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField N) :
    Tendsto (fun n => FreeExhaustion.freeDomainLaw N β (D n) (fill n)) atTop (𝓝 (state N hβ hsmall)) :=
  FreeExhaustion.freeDomain_tendsto_of_unique N _ (eq_state N hβ hsmall) D hex fill

/-- Arbitrary exterior spin laws, now with the true crossing bonds, give
the same bulk probability. -/
theorem boundary_tendsto (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n)
    (B : ℕ → ProbabilityMeasure (SpinField N)) :
    Tendsto (fun n => NearestWindowRealization.boxLaw β (D n) (B n)) atTop (𝓝 (state N hβ hsmall)) :=
  FreeExhaustion.boundary_tendsto_of_unique N _ (eq_state N hβ hsmall) D hex B

theorem freePair_tendsto (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (x y : Site) :
    Tendsto (fun n => FreeExhaustion.freePair N β (D n) x y) atTop
      (𝓝 (fieldPair (state N hβ hsmall) (x-y))) :=
  FreeExhaustion.freePair_tendsto_of_unique N hβ _ (eq_state N hβ hsmall) D hex x y

theorem stationary_free_cube (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * (Real.exp (4*β)-1) < 1) :
    IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β id (fieldPair (state N hβ hsmall)) :=
  FreeExhaustion.stationary_freeCubePair_of_unique N hβ _ (eq_state N hβ hsmall)

/-- Every tangent of the dot product of the unique state keeps its contact
mass and sharp unit cube, with susceptibility ratios on its whole realizing
sequence. -/
theorem state_tangent (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit (fieldPair (state N hβ hsmall)) R μ) :
    IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
      Tendsto (fun j => susceptibility (fieldPair (state N hβ hsmall)) (s * R j) /
        susceptibility (fieldPair (state N hβ hsmall)) (R j)) atTop (𝓝 (μ.real (observationCube s))) := by
  have h := stationary_free_cube N hβ hsmall
  exact ⟨h.surface_isotropic hβ tendsto_id hR hv, h.surface_cube_readout hβ tendsto_id hR hv⟩

theorem state_exists_tangent (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (fieldPair (state N hβ hsmall)) (R ∘ u) μ ∧ IsotropicPairMeasure μ ∧
      μ.real (observationCube 1) = 1 := by
  obtain ⟨u, μ, hu, hlocal, hv, hμ⟩ := (selected N hβ hsmall).exists_tangent hR
  let := hlocal
  exact ⟨u, μ, hu, hlocal, hv, hμ, (state_tangent N hβ hsmall (hR.comp hu.tendsto_atTop) hv).2.1⟩

/-- The independent lattice roundings use the full dot correlation of the
same bulk law selected by all finite free exhaustions. -/
theorem state_raw_angular (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6 * (Real.exp (4*β)-1) < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0)
    {k l : ℕ → Site}
    (hk : Tendsto (fun j => scaledSite (R j) (k j)) atTop (𝓝 x))
    (hl : Tendsto (fun j => scaledSite (R j) (l j)) atTop (𝓝 (O x))) :
    Tendsto (fun j => ((R j : ℝ)^3 / susceptibility (fieldPair (state N hβ hsmall)) (R j)) *
      (fieldPair (state N hβ hsmall) (k j) - fieldPair (state N hβ hsmall) (l j))) atTop (𝓝 0) :=
  (selected N hβ hsmall).raw_angular hR O hx hk hl

#print axioms nearest_gibbs_eq
#print axioms nearest_gibbs_eq_tanh
#print axioms exists_unique_nearest_gibbs_tanh
#print axioms exists_unique_nearest_gibbs
#print axioms freeDomain_tendsto
#print axioms boundary_tendsto
#print axioms freePair_tendsto
#print axioms state_tangent
#print axioms state_exists_tangent
#print axioms state_raw_angular
end IsingScaling.Rotor.PressureSelection.HighTemperature
