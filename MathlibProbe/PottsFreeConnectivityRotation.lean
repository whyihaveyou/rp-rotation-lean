import MathlibProbe.ModelPacketCubeReadout
import MathlibProbe.RawLatticeAngularReadout

/-! # Spatial rotations for the free FK connectivity in the bond parameter

The free connectivity in Section 4 of the standalone proof is the limit of
finite free-cube connection probabilities. On a cube with bond set `K`, the
probability weight at `p = 1 - exp (-β)` is `exp (-β) ^ K.card` times its
Edwards–Sokal activity weight. Cancel this configuration-independent factor
in the restricted and unrestricted partition sums. The resulting identity
holds at every volume, so the full thermodynamic limit, its sharp
susceptibility and all its original lattice measures have the same kernel.
-/

noncomputable section
open Filter Finset MeasureTheory
open scoped Classical Topology CompactlySupported
namespace IsingScaling.Potts.SiteBox
open EdwardsSokal ModelPackets

/-- Free random-cluster weight of the open subset `F` of the available
bonds `K`. The component count includes isolated vertices. -/
def bondProbabilityWeight {V : Type*} [Fintype V] (q : ℕ) (p : ℝ)
    (K F : Finset (V × V)) : ℝ :=
  p ^ F.card * (1 - p) ^ (K.card - F.card) * (q : ℝ) ^ Fintype.card (Component F)

theorem bondProbabilityWeight_eq_activity {V : Type*} [Fintype V] (q : ℕ) (β : ℝ)
    {K F : Finset (V × V)} (hF : F ⊆ K) :
    bondProbabilityWeight q (1 - Real.exp (-β)) K F =
      Real.exp (-β) ^ K.card * fkWeight q (fun _ => β) F := by
  have hp : Real.exp (-β) * (Real.exp β - 1) = 1 - Real.exp (-β) := by
    rw [mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  simp only [bondProbabilityWeight, sub_sub_cancel, fkWeight, activity, prod_const]
  rw [← hp, mul_pow]
  calc
    _ = (Real.exp (-β) ^ F.card * Real.exp (-β) ^ (K.card - F.card)) *
        ((Real.exp β - 1) ^ F.card * (q : ℝ) ^ Fintype.card (Component F)) := by ring
    _ = _ := by rw [← pow_add, add_tsub_cancel_of_le (card_le_card hF)]

/-- The probability that the two sites belong to the same open cluster
in a free cube with one bond for each unordered nearest-neighbour pair. -/
def boxConnectivity (q : ℕ) (p : ℝ) {L : ℕ} (x y : BoxSite L) : ℝ :=
  (∑ F ∈ (cubeBonds L).powerset, if port F x = port F y
    then bondProbabilityWeight q p (cubeBonds L) F else 0) /
  ∑ F ∈ (cubeBonds L).powerset, bondProbabilityWeight q p (cubeBonds L) F

/-- The Bernoulli closed-bond factors cancel from the physical connection
probability, including at zero bond probability. -/
theorem boxConnectivity_eq_boxPair {q : ℕ} (hq : 2 ≤ q) (β : ℝ) {L : ℕ} (x y : BoxSite L) :
    boxConnectivity q (1 - Real.exp (-β)) x y = boxPair q β x y := by
  let K := cubeBonds L
  let a := Real.exp (-β) ^ K.card
  have scaledSum (S : Finset (Finset (BoxSite L × BoxSite L))) (hS : S ⊆ K.powerset) :
      (∑ F ∈ S, bondProbabilityWeight q (1 - Real.exp (-β)) K F) =
        a * ∑ F ∈ S, fkWeight q (fun _ => β) F := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun F hF =>
      bondProbabilityWeight_eq_activity q β (mem_powerset.mp (hS hF))
  rw [boxPair_eq_freeFKPair hq]
  unfold boxConnectivity freeFKPair
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [scaledSum _ (filter_subset _ _), scaledSum _ (Subset.refl _)]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Real.exp_pos _).ne')

/-- Zero extension outside the finite cube permits fixed lattice sites as
the volume grows. -/
def latticeConnectivity (q : ℕ) (p : ℝ) (L : ℕ) (x y : Site) : ℝ :=
  if hx : x ∈ cube L then
    if hy : y ∈ cube L then boxConnectivity q p ⟨x,hx⟩ ⟨y,hy⟩ else 0
  else 0

theorem latticeConnectivity_eq_latticePair {q : ℕ} (hq : 2 ≤ q) (β : ℝ) (L : ℕ) (x y : Site) :
    latticeConnectivity q (1 - Real.exp (-β)) L x y = latticePair q β L x y := by
  simp only [latticeConnectivity, latticePair, boxConnectivity_eq_boxPair hq]

/-- Infinite-volume rooted connectivity defined entirely by the free bond
sums. The full cube exhaustion converges to it for every fixed pair. -/
def freeConnectivity (q : ℕ) (p : ℝ) (z : Site) : ℝ :=
  ⨆ L : ℕ, latticeConnectivity q p L z 0

private theorem bondParameter {p : ℝ} (hp : p < 1) :
    1 - Real.exp (-(-Real.log (1 - p))) = p := by
  rw [neg_neg, Real.exp_log (sub_pos.mpr hp), sub_sub_cancel]

private theorem inverseTemperature_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    0 ≤ -Real.log (1 - p) :=
  neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr h1).le (sub_le_self _ h0))

theorem freeConnectivity_eq_canonicalFreePair {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp : p < 1) :
    freeConnectivity q p = canonicalFreePair q (-Real.log (1 - p)) := by
  funext z
  unfold freeConnectivity canonicalFreePair
  apply congrArg iSup
  funext L
  simpa only [bondParameter hp] using latticeConnectivity_eq_latticePair hq (-Real.log (1-p)) L z 0

theorem latticeConnectivity_tendsto {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p)
    (h1 : p < 1) (x y : Site) :
    Tendsto (fun L => latticeConnectivity q p L x y) atTop (𝓝 (freeConnectivity q p (x-y))) := by
  have heq (L : ℕ) : latticeConnectivity q p L x y = latticePair q (-Real.log (1-p)) L x y := by
    simpa only [bondParameter h1] using latticeConnectivity_eq_latticePair hq (-Real.log (1-p)) L x y
  simp only [heq, freeConnectivity_eq_canonicalFreePair hq h1]
  exact canonicalFreePair_stationary hq (inverseTemperature_nonneg h0 h1) x y

/-- Every tangent of the original free FK connectivity has its own radial
density, contact mass and sharp-cube susceptibility ratios along the whole
sequence realizing that measure. -/
theorem freeConnectivity_tangent {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit (freeConnectivity q p) R μ) :
    IsotropicPairMeasure μ ∧ μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
      Tendsto (fun j => susceptibility (freeConnectivity q p) (s * R j) /
        susceptibility (freeConnectivity q p) (R j)) atTop (𝓝 (μ.real (observationCube s))) := by
  rw [freeConnectivity_eq_canonicalFreePair hq h1] at hv ⊢
  have hβ := inverseTemperature_nonneg h0 h1
  exact ⟨canonicalFreePair_isotropic hq hβ hR hv, canonicalFreePair_cube_readout hq hβ hR hv⟩

/-- One strictly increasing subsequence works for every compactly supported
continuous test and every spatial orthogonal map. -/
theorem freeConnectivity_exists_tangent {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (freeConnectivity q p) (R ∘ u) μ ∧ IsotropicPairMeasure μ ∧
      μ.real (observationCube 1) = 1 := by
  rw [freeConnectivity_eq_canonicalFreePair hq h1]
  have hβ := inverseTemperature_nonneg h0 h1
  obtain ⟨u, μ, hu, hlocal, hv, hiso⟩ := canonicalFreePair_exists_isotropic_tangent hq hβ hR
  let := hlocal
  have hcube := canonicalFreePair_cube_readout hq hβ (hR.comp hu.tendsto_atTop) hv
  exact ⟨u, μ, hu, hlocal, hv, hiso, hcube.1⟩

/-- The full-sequence angular comparison uses the original FK displacements
and the sharp susceptibility of the same free FK kernel. -/
theorem freeConnectivity_raw_angular {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun j => scaledSite (R j) (k j)) atTop (𝓝 x))
    (hl : Tendsto (fun j => scaledSite (R j) (l j)) atTop (𝓝 (O x))) :
    Tendsto (fun j => ((R j : ℝ)^3 / susceptibility (freeConnectivity q p) (R j)) *
      (freeConnectivity q p (k j) - freeConnectivity q p (l j))) atTop (𝓝 0) := by
  rw [freeConnectivity_eq_canonicalFreePair hq h1]
  exact canonicalFreePair_raw_angular hq (inverseTemperature_nonneg h0 h1) hR O hx hk hl

#print axioms boxConnectivity_eq_boxPair
#print axioms latticeConnectivity_tendsto
#print axioms freeConnectivity_tangent
#print axioms freeConnectivity_exists_tangent
#print axioms freeConnectivity_raw_angular
end IsingScaling.Potts.SiteBox
