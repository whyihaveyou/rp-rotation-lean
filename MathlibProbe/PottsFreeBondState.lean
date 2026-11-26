import MathlibProbe.PottsFiniteBondLaw
import MathlibProbe.PottsBondPathLimit
import MathlibProbe.PottsBondLawConvergence

/-! # The infinite free FK bond law and its spatial two-point theorem

Increasing finite all-open cylinder probabilities determine the weak limit
of the physical free cubes. In a fixed cube a connecting-path event is
clopen, so its probability converges under this same law. Domain monotonicity
and inclusion between windows sandwich the probability of the increasing
union of these events between the finite-volume connection limits. This
identifies the probability of a finite open path anywhere on the lattice
with the Potts simplex kernel at every displacement.
-/

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology CompactlySupported
namespace IsingScaling.Potts.FreeBond
open SiteBox ModelPackets

/-- Every subsequential weak limit of the actual free bond laws assigns the
same probability to each full-lattice connection event. -/
theorem connection_of_freeCubeLaw_limit {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {Φ : ProbabilityMeasure Field} {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hΦ : Tendsto (fun j => freeCubeLaw hq h0 h1 (k j)) atTop (𝓝 Φ)) (x y : Site) :
    (Φ (connection x y) : ℝ) = freeConnectivity q p (x - y) := by
  apply connection_eq_of_subseq hk hΦ x y
  · refine (latticeConnectivity_tendsto hq h0 h1 x y).congr' ?_
    filter_upwards [eventually_mem_cube x, eventually_mem_cube y] with L hx hy
    simpa [latticeConnectivity, hx, hy] using
      (freeCubeLaw_within hq h0 h1 (⟨x,hx⟩ : BoxSite L) ⟨y,hy⟩).symm
  · intro M L hML
    exact freeCubeLaw_mono hq h0 h1 hML (within M x y) (fun h => within_mono_field h)

/-- One probability law on configurations of all unoriented nearest-neighbour
bonds realizes the full free-box exhaustion and all two-site path events. -/
theorem exists_free_bond_law {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    ∃ Φ : ProbabilityMeasure Field, Tendsto (freeCubeLaw hq h0 h1) atTop (𝓝 Φ) ∧
      ∀ x y : Site, (Φ (connection x y) : ℝ) = freeConnectivity q p (x - y) := by
  obtain ⟨Φ, hΦ⟩ := exists_weak_limit_of_allOpen_mono (freeCubeLaw hq h0 h1)
    (fun F _ _ hML => freeCubeLaw_mono hq h0 h1 hML (allOpen F)
      (fun h hω e he => h e (hω e he)))
  exact ⟨Φ, hΦ, connection_of_freeCubeLaw_limit hq h0 h1 (k := id) tendsto_id hΦ⟩

def freeLaw {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    ProbabilityMeasure Field :=
  (exists_free_bond_law hq h0 h1).choose

theorem tendsto_freeLaw {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    Tendsto (freeCubeLaw hq h0 h1) atTop (𝓝 (freeLaw hq h0 h1)) :=
  (exists_free_bond_law hq h0 h1).choose_spec.1

theorem freeLaw_connection {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (x y : Site) : (freeLaw hq h0 h1 (connection x y) : ℝ) = freeConnectivity q p (x - y) :=
  (exists_free_bond_law hq h0 h1).choose_spec.2 x y

def connectionPair (Φ : ProbabilityMeasure Field) (z : Site) : ℝ := Φ (connection 0 z)

theorem freeLaw_pair_eq {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    connectionPair (freeLaw hq h0 h1) = freeConnectivity q p := by
  funext z
  have hs : connection 0 z = connection z 0 := Set.ext fun _ =>
    ⟨fun h => Relation.EqvGen.symm _ _ h, fun h => Relation.EqvGen.symm _ _ h⟩
  rw [connectionPair, hs, freeLaw_connection, sub_zero]

/-- Every diverging scale sequence has a single strictly increasing
subsequence for every test of the true infinite-volume path probabilities. -/
theorem freeLaw_exists_tangent {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (connectionPair (freeLaw hq h0 h1)) (R ∘ u) μ ∧ IsotropicPairMeasure μ ∧
      μ.real (observationCube 1) = 1 := by
  rw [freeLaw_pair_eq]
  exact freeConnectivity_exists_tangent hq h0 h1 hR

/-- Radiality, contact, all spatial orthogonal pushforwards, and sharp
susceptibility readouts apply to every tangent of this very bond law. -/
theorem freeLaw_tangent {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit (connectionPair (freeLaw hq h0 h1)) R μ) :
    IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
      Tendsto (fun j => susceptibility (connectionPair (freeLaw hq h0 h1)) (s * R j) /
        susceptibility (connectionPair (freeLaw hq h0 h1)) (R j)) atTop (𝓝 (μ.real (observationCube s))) := by
  rw [freeLaw_pair_eq] at hv ⊢
  exact freeConnectivity_tangent hq h0 h1 hR hv

/-- Full-sequence angular defect for independently approximated sites of
the original free-lattice bond paths. -/
theorem freeLaw_raw_angular {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun j => scaledSite (R j) (k j)) atTop (𝓝 x))
    (hl : Tendsto (fun j => scaledSite (R j) (l j)) atTop (𝓝 (O x))) :
    Tendsto (fun j => ((R j : ℝ)^3 / susceptibility (connectionPair (freeLaw hq h0 h1)) (R j)) *
      (connectionPair (freeLaw hq h0 h1) (k j) - connectionPair (freeLaw hq h0 h1) (l j)))
      atTop (𝓝 0) := by
  rw [freeLaw_pair_eq]
  exact freeConnectivity_raw_angular hq h0 h1 hR O hx hk hl

#print axioms exists_free_bond_law
#print axioms freeLaw_connection
#print axioms freeLaw_exists_tangent
#print axioms freeLaw_tangent
#print axioms freeLaw_raw_angular
end IsingScaling.Potts.FreeBond
