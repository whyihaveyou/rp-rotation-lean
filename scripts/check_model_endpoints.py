"""Typecheck physical packet spectra, finite-volume origins and sharp-cube readouts."""

from pathlib import Path
import re
import subprocess
import sys


PROJECT = Path(__file__).resolve().parents[1]

PROBE = r"""
import MathlibProbe.IsingTwoPointRotation
import MathlibProbe.ReflectedLatticePacket
import MathlibProbe.PottsPhysicalSiteReflection
import MathlibProbe.PottsCanonicalFreePair
import MathlibProbe.PottsCanonicalShiftedMirror
import MathlibProbe.PottsFreeConnectivityRotation
import MathlibProbe.PottsFreeBondState
import MathlibProbe.PottsFreeBondExhaustion
import MathlibProbe.RotorThermodynamicPacket
import MathlibProbe.RotorStationaryRawAngular
import MathlibProbe.RotorPhysicalMirrorSelection
import MathlibProbe.RotorPhysicalStateSymmetries
import MathlibProbe.RotorPeriodicStateRealization
import MathlibProbe.RotorNearestWindowRealization
import MathlibProbe.RotorFreeUniqueExhaustion
import MathlibProbe.RotorHighTemperatureUniqueness
import MathlibProbe.RotorXYCanonicalFreePair
import MathlibProbe.RotorHeisenbergFreeCubeDLR
import MathlibProbe.RotorHeisenbergCorrelationInput
import MathlibProbe.RotorHeisenbergFreeFieldLimit
import MathlibProbe.RotorDotPositiveFieldContinuation
import MathlibProbe.HeisenbergFerromagneticLeeYang
import MathlibProbe.RotorHeisenbergPhysicalRotation
import MathlibProbe.ModelPacketCubeReadout
import MathlibProbe.ModelPacketPhysicalRotation
open MeasureTheory Filter
open scoped Topology CompactlySupported InnerProductSpace
open IsingScaling
namespace PacketAlignment

theorem sameIsingGrid {β : ℝ} (hβ : 0 ≤ β) (diagonal : Bool) {ι : Type} [Fintype ι]
    (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
          Packet.gridPacket diagonal (thermodynamicTwoPoint β) c x y n := by
  have hp := thermodynamicTwoPoint_stationary hβ
  apply Packet.gridPacket_spectrum_of_site_reflection
  · intro z
    simpa only [sub_zero] using hp.abs_le_one z 0
  · intro ι _ s hs u
    exact hp.axis_reflected_positive s hs u
  · intro ι _ s hs u
    exact hp.diagonal_reflected_positive s hs u

theorem IsingTangent {β : ℝ} (hβ : 0 ≤ β) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (O : Space ≃ₗᵢ[ℝ] Space) :
    μ.map O = μ := ht.rotation_invariant hβ O

theorem PottsGrid {q : ℕ} (hq : 2 ≤ q) {β : ℝ} {L : ℕ → ℕ} {g : Site → ℝ}
    (hg : Potts.SiteBox.StationaryPairLimit q β L g) (hL : Tendsto L atTop atTop)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (diagonal : Bool)
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => g (signedPerm p s z)) c x y n :=
  hg.gridPacket_signedPerm_spectrum hq hL p s diagonal c x y

theorem sphereGrid (N : ℕ) [NeZero N] {β : ℝ} {L : ℕ → ℕ} {g : Site → ℝ}
    (hg : Rotor.IsStationaryFreeCubePairLimit (Rotor.SiteReflection.surfacePrior N) β L g)
    (hL : Tendsto L atTop atTop) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => g ((signedPerm p s).symm z)) c x y n :=
  Rotor.surfacePrior_gridPacket_spectrum N hg hL p s diagonal c x y

theorem canonicalPottsGrid {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (diagonal : Bool)
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => Potts.SiteBox.canonicalFreePair q β (signedPerm p s z))
          c x y n :=
  Potts.SiteBox.canonicalFreePair_gridPacket_orbit_spectrum hq hβ p s diagonal c x y

theorem canonicalPottsShiftedMirrors {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    Packet.SiteReflectedPositive (Potts.SiteBox.canonicalFreePair q β) (fun z => z 0 - 1)
        (fun z => ![1 - z 0, z 1, z 2]) ∧
    Packet.SiteReflectedPositive (Potts.SiteBox.canonicalFreePair q β) (fun z => z 0)
        (fun z => ![-z 0 - 1, z 1, z 2]) ∧
    Packet.SiteReflectedPositive (Potts.SiteBox.canonicalFreePair q β) (fun z => z 0 - z 1 + 1)
        (fun z => ![z 1 - 1, z 0 + 1, z 2]) :=
  ⟨Potts.SiteBox.canonicalFreePair_axialBond_positive hq hβ,
   Potts.SiteBox.canonicalFreePair_axialShift_positive hq hβ,
   Potts.SiteBox.canonicalFreePair_diagonalShift_positive hq hβ⟩

theorem rotorEvenPoints (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    {L R : ℕ → ℕ} {g : Site → ℝ}
    (hg : Rotor.IsStationaryFreeCubePairLimit (Rotor.SiteReflection.surfacePrior N) β L g)
    (hL : Tendsto L atTop atTop) (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (fun i => 2 * k n i)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (fun i => 2 * l n i)) atTop (𝓝 (O x))) :
    Tendsto (fun n => ((R n : ℝ)^3 / susceptibility g (R n)) *
      (g (fun i => 2 * k n i) - g (fun i => 2 * l n i))) atTop (𝓝 0) :=
  hg.raw_angular_even_lattice hβ hL hR O hx (k:=k) (l:=l) hk hl

theorem rotorCommonRectangleAnnulus (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    {L T R : ℕ → ℕ} {g : Site → ℝ}
    (hg : Rotor.IsStationaryFreeCubePairLimit (Rotor.SiteReflection.surfacePrior N) β L g)
    (hL : Tendsto L atTop atTop) (hT : Tendsto T atTop atTop)
    (hrect : ∀ u v : Site, 0 < u 0 → 0 < v 0 →
      Tendsto (fun m => Rotor.BondRectangle.crossPair (Rotor.SiteReflection.surfacePrior N) β
        (BondMirror.port (T m) u) (BondMirror.port (T m) v)) atTop
        (𝓝 (g (u - ![1-v 0,v 1,v 2]))))
    (hR : Tendsto R atTop atTop) {k l : ℕ → Site} {a b : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ b)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ b)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => ((R n : ℝ)^3 / susceptibility g (R n)) *
      (g (k n) - g (l n))) atTop (𝓝 0) :=
  hg.raw_angular_annulus_of_crossPair_limit hβ hL hT hrect hR ha hk hl hrad

theorem canonicalPottsTangent {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ]
    (hv : ∀ f : C_c(Space, ℝ), Tendsto
      (fun n => ∫ x, f x ∂twoPointMeasure (Potts.SiteBox.canonicalFreePair q β) (R n))
      atTop (𝓝 (∫ x, f x ∂μ))) (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ :=
  (Potts.SiteBox.canonicalFreePair_isotropic hq hβ hR hv).map_eq O

theorem sphereTangent (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    {L R : ℕ → ℕ} {g : Site → ℝ}
    (hg : Rotor.IsStationaryFreeCubePairLimit (Rotor.SiteReflection.surfacePrior N) β L g)
    (hL : Tendsto L atTop atTop) (hR : Tendsto R atTop atTop) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (hv : ∀ f : C_c(Space, ℝ), Tendsto
      (fun n => ∫ x, f x ∂twoPointMeasure g (R n)) atTop (𝓝 (∫ x, f x ∂μ)))
    (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ :=
  (hg.surface_isotropic hβ hL hR hv).map_eq O

theorem physicalMeasureWeights (g : Site → ℝ) (R : ℕ) :
    twoPointMeasure g R =
      Measure.sum (fun z : Site => ENNReal.ofReal (g z / ∑ w ∈ cube R, g w) •
        Measure.dirac (WithLp.toLp 2 (fun i => (z i : ℝ) / (R : ℝ)))) := rfl

-- The same subsequence serves all tests. Every tangent on its given sequence
-- retains its own contact mass, radial density and sharp-cube ratios.
private def OriginalMeasureLimits (g : Site → ℝ) : Prop :=
  ∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
    (∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
      ∀ f : C_c(Space, ℝ), Tendsto (fun j => ∫ x, f x ∂twoPointMeasure g (R (u j)))
        atTop (𝓝 (∫ x, f x ∂μ))) ∧
    ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
      (∀ f : C_c(Space, ℝ), Tendsto (fun j => ∫ x, f x ∂twoPointMeasure g (R j))
        atTop (𝓝 (∫ x, f x ∂μ))) →
      μ ≠ 0 ∧ (∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ) ∧
      (∃ f : Space → ℝ, (∀ x, 0 ≤ f x) ∧ ContinuousOn f {0}ᶜ ∧ LocallyIntegrable f ∧
        μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ x y : Space, x ≠ 0 → y ≠ 0 → ‖x‖ = ‖y‖ → f x = f y) ∧
      μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
        Tendsto (fun j => susceptibility g (s * R j) / susceptibility g (R j))
          atTop (𝓝 (μ.real (observationCube s)))

private def OriginalSiteAngular (g : Site → ℝ) : Prop :=
  ∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x ≠ 0 →
    ∀ k l : ℕ → Site, Tendsto (fun j => scaledSite (R j) (k j)) atTop (𝓝 x) →
      Tendsto (fun j => scaledSite (R j) (l j)) atTop (𝓝 (O x)) →
      Tendsto (fun j => ((R j : ℝ)^3 / susceptibility g (R j)) * (g (k j) - g (l j)))
        atTop (𝓝 0)

private theorem originalMeasureLimits_of_tangents {g : Site → ℝ}
    (hex : ∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
      ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
        ModelPackets.VaguePairLimit g (R ∘ u) μ ∧ ModelPackets.IsotropicPairMeasure μ)
    (hall : ∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
      ModelPackets.VaguePairLimit g R μ → ModelPackets.IsotropicPairMeasure μ ∧
        μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
          Tendsto (fun j => susceptibility g (s * R j) / susceptibility g (R j))
            atTop (𝓝 (μ.real (observationCube s)))) : OriginalMeasureLimits g := by
  intro R hR
  obtain ⟨u, μ, hu, hlocal, hv, hiso⟩ := hex R hR
  refine ⟨⟨u, μ, hu, hlocal, hiso.nonzero, hv⟩, ?_⟩
  intro ν _ hν
  obtain ⟨hrot, hunit, hratio⟩ := hall R hR ν hν
  exact ⟨hrot.nonzero, hrot.map_eq, hrot.radial_density, hunit, hratio⟩

open Potts.SiteBox Potts.EdwardsSokal in
open scoped Classical in
theorem freePottsBondSum {q L : ℕ} (hq : 2 ≤ q) (β : ℝ) (x y : BoxSite L) :
    let p := 1 - Real.exp (-β)
    let K := cubeBonds L
    let w := fun F : Finset (BoxSite L × BoxSite L) =>
      p ^ F.card * (1 - p) ^ (K.card - F.card) * (q : ℝ) ^ Fintype.card (Component F)
    (∑ F ∈ K.powerset, if port F x = port F y then w F else 0) / (∑ F ∈ K.powerset, w F) =
      (∑ σ : Config q L, weight equalColour β σ *
        (((q : ℝ) * (if σ x = σ y then 1 else 0) - 1) / ((q : ℝ) - 1))) /
        ∑ σ : Config q L, weight equalColour β σ :=
  boxConnectivity_eq_boxPair hq β x y

open Potts.SiteBox in
theorem canonicalPottsCubeLimits {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    (∀ x y : Site, Tendsto (fun L => latticePair q β L x y) atTop
      (𝓝 (canonicalFreePair q β (x - y)))) ∧
    ∀ (L : ℕ → ℕ), Tendsto L atTop atTop → ∀ g : Site → ℝ,
      (∀ x y, Tendsto (fun j => latticePair q β (L j) x y) atTop (𝓝 (g (x - y)))) →
      g = canonicalFreePair q β :=
  ⟨canonicalFreePair_stationary hq hβ, fun _ hL _ hg =>
    StationaryPairLimit.eq_canonicalFreePair hq hβ hg hL⟩

open Potts.SiteBox in
theorem canonicalPottsOriginalReadouts {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    OriginalMeasureLimits (canonicalFreePair q β) ∧ OriginalSiteAngular (canonicalFreePair q β) := by
  refine ⟨originalMeasureLimits_of_tangents (fun _ hR =>
    canonicalFreePair_exists_isotropic_tangent hq hβ hR) ?_,
    fun _ hR O _ hx _ _ hk hl => canonicalFreePair_raw_angular hq hβ hR O hx hk hl⟩
  exact fun _ hR _ _ hv => ⟨canonicalFreePair_isotropic hq hβ hR hv,
    canonicalFreePair_cube_readout hq hβ hR hv⟩

open Potts.SiteBox in
theorem freeFKCubeLimits {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    freeConnectivity q p = canonicalFreePair q (-Real.log (1 - p)) ∧
    ∀ x y : Site, Tendsto (fun L => latticeConnectivity q p L x y) atTop
      (𝓝 (freeConnectivity q p (x - y))) :=
  ⟨freeConnectivity_eq_canonicalFreePair hq h1, latticeConnectivity_tendsto hq h0 h1⟩

open Potts.SiteBox in
theorem freeFKOriginalReadouts {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    OriginalMeasureLimits (freeConnectivity q p) ∧ OriginalSiteAngular (freeConnectivity q p) := by
  refine ⟨originalMeasureLimits_of_tangents ?_ (fun _ hR _ _ hv => freeConnectivity_tangent hq h0 h1 hR hv),
    fun _ hR O _ hx _ _ hk hl => freeConnectivity_raw_angular hq h0 h1 hR O hx hk hl⟩
  intro R hR
  obtain ⟨u, μ, hu, hlocal, hv, hiso, _⟩ := freeConnectivity_exists_tangent hq h0 h1 hR
  exact ⟨u, μ, hu, hlocal, hv, hiso⟩

open Potts.SiteBox Potts.EdwardsSokal Potts.FreeBond in
open scoped Classical in
theorem finiteFKBondEvents {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (L : ℕ) (A : Set (Bond → Bool)) :
    let K := cubeBonds L
    let w := fun F : Finset (BoxSite L × BoxSite L) =>
      p ^ F.card * (1 - p) ^ (K.card - F.card) * (q : ℝ) ^ Fintype.card (Component F)
    let state := fun (F : Finset (BoxSite L × BoxSite L)) (e : Bond) =>
      decide (e.val ∈ F.image (fun t => s(t.1.val, t.2.val)))
    (freeCubeLaw hq h0 h1 L A : ℝ) =
      (∑ F ∈ K.powerset, if state F ∈ A then w F else 0) / (∑ F ∈ K.powerset, w F) :=
  freeCubeLaw_real hq h0 h1 L A

open Potts.FreeBond in
theorem freeFKBondField {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    let path := fun x y : Site => {ω : Bond → Bool |
      Relation.EqvGen (fun a b : Site => ∃ e : Bond, e.val = s(a, b) ∧ ω e = true) x y}
    ∃ Φ : ProbabilityMeasure (Bond → Bool), Tendsto (freeCubeLaw hq h0 h1) atTop (𝓝 Φ) ∧
      (∀ x y : Site, (Φ (path x y) : ℝ) = Potts.SiteBox.canonicalFreePair q (-Real.log (1 - p)) (x - y)) ∧
      OriginalMeasureLimits (fun z => (Φ (path 0 z) : ℝ)) ∧
      OriginalSiteAngular (fun z => (Φ (path 0 z) : ℝ)) := by
  refine ⟨freeLaw hq h0 h1, tendsto_freeLaw hq h0 h1, ?_, ?_,
    fun _ hR O _ hx _ _ hk hl => freeLaw_raw_angular hq h0 h1 hR O hx hk hl⟩
  · intro x y
    exact (freeLaw_connection hq h0 h1 x y).trans
      (congrFun (Potts.SiteBox.freeConnectivity_eq_canonicalFreePair hq h1) (x - y))
  · apply originalMeasureLimits_of_tangents (g := connectionPair (freeLaw hq h0 h1)) ?_
      (fun _ hR _ _ hv => freeLaw_tangent hq h0 h1 hR hv)
    intro R hR
    obtain ⟨u, μ, hu, hlocal, hv, hiso, _⟩ := freeLaw_exists_tangent hq h0 h1 hR
    exact ⟨u, μ, hu, hlocal, hv, hiso⟩

open Potts.EdwardsSokal Potts.FreeBond in
open scoped Classical in
theorem finiteFKInducedPaths {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (U : Finset Site) (x y : ↥U) :
    let K := (Finset.univ : Finset (↥U × ↥U)).filter (fun e =>
      Fintype.equivFin (↥U) e.1 < Fintype.equivFin (↥U) e.2 ∧ latticeDistance e.1.val e.2.val = 1)
    let w := fun F : Finset (↥U × ↥U) =>
      p ^ F.card * (1 - p) ^ (K.card - F.card) * (q : ℝ) ^ Fintype.card (Component F)
    (freeDomainLaw hq h0 h1 U {ω : Bond → Bool |
      Relation.EqvGen (fun a b : Site => ∃ e : Bond, e.val = s(a, b) ∧ ω e = true) x.val y.val} : ℝ) =
        (∑ F ∈ K.powerset, if port F x = port F y then w F else 0) / (∑ F ∈ K.powerset, w F) :=
  freeDomainLaw_connection_eq_finite hq h0 h1 x y

-- The limit law depends only on q and p, for any index type, filter and
-- family of finite sets eventually containing each fixed lattice site.
open Potts.FreeBond in
theorem freeFKInducedExhaustion {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {ι : Type*} {l : Filter ι} (U : ι → Finset Site) (hU : ∀ x : Site, ∀ᶠ n in l, x ∈ U n) :
    Tendsto (fun n => freeDomainLaw hq h0 h1 (U n)) l (𝓝 (freeLaw hq h0 h1)) ∧
    ∀ x y : Site, Tendsto (fun n => (freeDomainLaw hq h0 h1 (U n) (connection x y) : ℝ)) l
      (𝓝 (freeLaw hq h0 h1 (connection x y) : ℝ)) ∧
      (freeLaw hq h0 h1 (connection x y) : ℝ) = Potts.SiteBox.canonicalFreePair q (-Real.log (1 - p)) (x - y) := by
  refine ⟨exhaustion_tendsto_freeLaw hq h0 h1 hU, ?_⟩
  intro x y
  constructor
  · rw [freeLaw_connection]
    exact exhaustion_connection_tendsto hq h0 h1 hU x y
  · exact (freeLaw_connection hq h0 h1 x y).trans
      (congrFun (Potts.SiteBox.freeConnectivity_eq_canonicalFreePair hq h1) (x - y))

open Rotor.SiteReflection in
theorem freeSphereGibbsPair (N : ℕ) [NeZero N] (β : ℝ) {L : ℕ} (x y : BoxSite L) :
    let area := (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
    let prior := Measure.pi (fun _ : BoxSite L => (area Set.univ)⁻¹ • area)
    freePair (surfacePrior N) β L x y =
      (∫ σ : Config N L, Real.exp (β * energy σ) * ⟪(σ x).val, (σ y).val⟫_ℝ ∂prior) /
        ∫ σ : Config N L, Real.exp (β * energy σ) ∂prior :=
  freePair_inside (surfacePrior N) β x y

-- The two-site limits use one prescribed g and one sequence L for all pairs.
theorem prescribedRotorCubeLimits (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    {L : ℕ → ℕ} {g : Site → ℝ} (hL : Tendsto L atTop atTop)
    (hpair : ∀ x y : Site,
      Tendsto (fun j => Rotor.SiteReflection.freePair (Rotor.SiteReflection.surfacePrior N) β (L j) x y)
        atTop (𝓝 (g (x - y)))) : OriginalMeasureLimits g := by
  have hg : Rotor.IsStationaryFreeCubePairLimit (Rotor.SiteReflection.surfacePrior N) β L g := hpair
  exact originalMeasureLimits_of_tangents (fun _ hR => hg.surface_exists_isotropic_tangent hβ hL hR)
    (fun _ hR _ _ hv => ⟨hg.surface_isotropic hβ hL hR hv, hg.surface_cube_readout hβ hL hR hv⟩)

theorem xyFiniteGibbsMonotone {V : Type*} [Fintype V] {J K : V × V → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (hJK : ∀ e, J e ≤ K e) (v w : V) :
    let prior := Measure.pi (fun _ : V => Rotor.SiteReflection.surfacePrior 2)
    let pair := fun B : V × V → ℝ =>
      let W := fun σ : V → Rotor.Spin 2 => Real.exp (∑ e : V × V, B e * ⟪(σ e.1).val, (σ e.2).val⟫_ℝ)
      (∫ σ, W σ * ⟪(σ v).val, (σ w).val⟫_ℝ ∂prior) / (∫ σ, W σ ∂prior)
    pair J ≤ pair K :=
  Rotor.XY.graphPair_mono hJ hJK v w

open Rotor.XY in
theorem xyFreeCubeAndRectangle {β : ℝ} (hβ : 0 ≤ β) :
    (∀ x y : Site, Tendsto (fun L => Rotor.SiteReflection.freePair
      (Rotor.SiteReflection.surfacePrior 2) β L x y) atTop (𝓝 (canonicalFreePair β (x - y)))) ∧
    (∀ x y : Site, 0 < x 0 → 0 < y 0 →
      Tendsto (fun L => Rotor.BondRectangle.crossPair (Rotor.SiteReflection.surfacePrior 2) β
        (BondMirror.port L x) (BondMirror.port L y)) atTop
          (𝓝 (canonicalFreePair β (x - ![1 - y 0, y 1, y 2])))) ∧
    Packet.SiteReflectedPositive (canonicalFreePair β) (fun z => z 0 - 1)
      (fun z => ![1 - z 0, z 1, z 2]) :=
  ⟨canonicalFreePair_stationary hβ, crossPair_tendsto hβ, canonicalFreePair_axialBond_positive hβ⟩

open Rotor.XY in
theorem xyFreeInducedExhaustion {T : ℕ → Type*} [∀ n, Fintype (T n)]
    (p : ∀ n, T n → Site) (hinj : ∀ n, Function.Injective (p n))
    (hex : ∀ z : Site, ∀ᶠ n in atTop, z ∈ Set.range (p n))
    {x y : Site} (v w : ∀ n, T n)
    (hv : ∀ᶠ n in atTop, p n (v n) = x) (hw : ∀ᶠ n in atTop, p n (w n) = y)
    {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun n => graphPair (fun e : T n × T n =>
      if latticeDistance (p n e.1) (p n e.2) = 1 then β / 2 else 0) (v n) (w n))
      atTop (𝓝 (canonicalFreePair β (x - y))) :=
  finitePair_tendsto_of_exhaustion p hinj hex v w hv hw hβ

open Rotor.XY in
theorem xyFreeOriginalReadouts {β : ℝ} (hβ : 0 ≤ β) :
    OriginalMeasureLimits (canonicalFreePair β) ∧ OriginalSiteAngular (canonicalFreePair β) := by
  refine ⟨originalMeasureLimits_of_tangents (fun _ hR => canonicalFreePair_exists_isotropic_tangent hβ hR) ?_,
    fun _ hR O _ hx _ _ hk hl => canonicalFreePair_raw_angular hβ hR O hx hk hl⟩
  exact fun _ hR _ _ hv => ⟨canonicalFreePair_isotropic hβ hR hv, canonicalFreePair_cube_readout hβ hR hv⟩

open Rotor.XY in
theorem xyFreeAnnulus {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {k l : ℕ → Site} {a b : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ b)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ b)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => ((R n : ℝ)^3 / susceptibility (canonicalFreePair β) (R n)) *
      (canonicalFreePair β (k n) - canonicalFreePair β (l n))) atTop (𝓝 0) :=
  canonicalFreePair_raw_annulus hβ hR ha hk hl hrad

open Rotor.PressureSelection

open Rotor.HeisenbergField in
theorem heisenbergFiniteFieldLaw (β h : ℝ) (L : ℕ) (F : C(SpinField 3, ℝ)) :
    let θ := Rotor.SiteReflection.surfacePrior 3
    let tiltedSite := θ.tilted (fun s : Rotor.Spin 3 => h * s.val 0)
    (Measure.pi (fun _ : BoxSite L => fieldPrior h) =
      (Measure.pi (fun _ : BoxSite L => θ)).tilted (fun σ => ∑ x : BoxSite L, h * (σ x).val 0)) ∧
    ((∫ σ, F σ ∂(cubeLaw β h L : Measure _)) =
      ∫ σ : Rotor.SiteReflection.Config 3 L, F (extendCube L σ) ∂
        ((Measure.pi (fun _ : BoxSite L => tiltedSite)).tilted (fun σ => β * Rotor.SiteReflection.energy σ))) ∧
    ∀ x y : BoxSite L, (∫ σ : SpinField 3, ⟪(σ x).val, (σ y).val⟫_ℝ ∂(cubeLaw β h L : Measure _)) =
      Rotor.SiteReflection.freePair tiltedSite β L x y :=
  ⟨fieldPrior_product (BoxSite L) h, cubeLaw_integral β h L F,
    fun x y => cubeLaw_pair β h L x.property y.property⟩

open Rotor.HeisenbergField in
theorem heisenbergFixedFieldDLR {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)} {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) (hP : Tendsto (fun j => cubeLaw β h (L j)) atTop (𝓝 P)) :
    (∀ (Λ : Finset Site) (σ : SpinField 3), windowSource h Λ σ = ∑ x : Λ, h * (σ x).val 0) ∧
    ∀ (Λ : Finset Site) (F : C(SpinField 3, ℝ)), (∫ σ, F σ ∂(P : Measure _)) =
      ∫ σ, LocalGibbs.readout Λ (LocalGibbs.windowEnergy 3 Λ (LocalGibbs.nearestCoupling β)
        (LocalGibbs.summable_abs_nearest β) + windowSource h Λ) F σ ∂(P : Measure _) :=
  ⟨fun _ _ => rfl, field_gibbs_of_free_cube_limit hL hP⟩

-- Both shapes refer to this one free infinite-volume probability law at h > 0.
-- The positive-field physical readout below establishes its existence and uniqueness.
private def HeisenbergCubeAndRectangle (β h : ℝ) (P : ProbabilityMeasure (SpinField 3)) : Prop :=
  Tendsto (Rotor.HeisenbergField.cubeLaw β h) atTop (𝓝 P) ∧ ShiftInvariant P ∧
  ∀ x y : Site, 0 < x 0 → 0 < y 0 →
    Tendsto (fun L => Rotor.BondRectangle.crossPair
      ((Rotor.SiteReflection.surfacePrior 3).tilted (fun s : Rotor.Spin 3 => h * s.val 0)) β
        (BondMirror.port L x) (BondMirror.port L y)) atTop
      (𝓝 (∫ σ : SpinField 3, ⟪(σ 0).val, (σ (x - ![1 - y 0, y 1, y 2])).val⟫_ℝ ∂(P : Measure _)))

private theorem heisenbergCommonFreeLimit_iff {β h : ℝ} {P : ProbabilityMeasure (SpinField 3)} :
    HeisenbergCubeAndRectangle β h P ↔ Rotor.HeisenbergField.CommonFreeLimit β h P :=
  ⟨fun H => ⟨H.1, H.2.1, H.2.2⟩, fun H => ⟨H.centered, H.stationary, H.rectangle⟩⟩

open Rotor.HeisenbergField in
theorem heisenbergScalarFieldInput (β : ℝ) :
    (∀ (d : (Site × Fin 3) →₀ ℕ) (σ : SpinField 3),
      spinMoment d σ = ∏ i ∈ d.support, ((σ i.1).val i.2) ^ d i) ∧
    ((∀ h : ℝ, 0 < h → ∃ P : ProbabilityMeasure (SpinField 3), HeisenbergCubeAndRectangle β h P) ↔
      ∀ h : ℝ, 0 < h →
        (∀ d : (Site × Fin 3) →₀ ℕ, ∃ a : ℝ,
          Tendsto (fun L => ∫ σ, spinMoment d σ ∂(cubeLaw β h L : Measure _)) atTop (𝓝 a)) ∧
        (∀ (u : Site) (d : (Site × Fin 3) →₀ ℕ), Tendsto (fun L =>
          (∫ σ : SpinField 3, spinMoment d (fun x => σ (x + u)) ∂(cubeLaw β h L : Measure _)) -
          ∫ σ, spinMoment d σ ∂(cubeLaw β h L : Measure _)) atTop (𝓝 0)) ∧
        ∀ x y : Site, 0 < x 0 → 0 < y 0 →
          Tendsto (fun L => Rotor.BondRectangle.crossPair (fieldPrior h) β
            (BondMirror.port L x) (BondMirror.port L y) -
              ∫ σ : SpinField 3, ⟪(σ x).val, (σ (![1 - y 0, y 1, y 2] : Site)).val⟫_ℝ
                ∂(cubeLaw β h L : Measure _)) atTop (𝓝 0)) := by
  refine ⟨spinMoment_apply, ?_⟩
  constructor
  · intro fr h hh
    obtain ⟨P, hP⟩ := fr h hh
    have H := (heisenbergCommonFreeLimit_iff.mp hP).scalarThermodynamicLimit
    exact ⟨H.moments, H.translates, H.rectangles⟩
  · intro fr h hh
    obtain ⟨hm, ht, hr⟩ := fr h hh
    have H : ScalarThermodynamicLimit β h := ⟨hm, ht, hr⟩
    obtain ⟨P, hP⟩ := H.exists_commonFreeLimit
    exact ⟨P, heisenbergCommonFreeLimit_iff.mpr hP⟩

private def HeisenbergZeroFieldReadouts (β : ℝ) (Q : ProbabilityMeasure (SpinField 3)) : Prop :=
  let g := fun z : Site => ∫ σ : SpinField 3, ⟪(σ 0).val, (σ z).val⟫_ℝ ∂(Q : Measure _)
  (∀ (Λ : Finset Site) (F : C(SpinField 3, ℝ)), (∫ σ, F σ ∂(Q : Measure _)) =
    ∫ σ, LocalGibbs.readout Λ (LocalGibbs.windowEnergy 3 Λ (LocalGibbs.nearestCoupling β)
      (LocalGibbs.summable_abs_nearest β)) F σ ∂(Q : Measure _)) ∧
  ShiftInvariant Q ∧ (∀ z, 0 ≤ g z) ∧ OriginalMeasureLimits g ∧ OriginalSiteAngular g ∧
  ∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (k l : ℕ → Site) (a b : ℝ), 0 < a →
    (∀ j, a ≤ ‖scaledSite (R j) (k j)‖ ∧ ‖scaledSite (R j) (k j)‖ ≤ b) →
    (∀ j, ‖scaledSite (R j) (l j)‖ ≤ b) →
    Tendsto (fun j => ‖scaledSite (R j) (k j)‖ - ‖scaledSite (R j) (l j)‖) atTop (𝓝 0) →
    Tendsto (fun j => ((R j : ℝ)^3 / susceptibility g (R j)) * (g (k j) - g (l j)))
      atTop (𝓝 0)

open Rotor.HeisenbergField in
theorem heisenbergEveryFieldAccumulation {β : ℝ} (hβ : 0 ≤ β)
    (h : ℕ → ℝ) (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    (P : ℕ → ProbabilityMeasure (SpinField 3)) (hc : ∀ j, HeisenbergCubeAndRectangle β (h j) (P j))
    {u : ℕ → ℕ} (hu : Tendsto u atTop atTop) {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto (P ∘ u) atTop (𝓝 Q)) : HeisenbergZeroFieldReadouts β Q := by
  have H : VanishingFieldOrigin β Q := ⟨h ∘ u, P ∘ u, fun j => hp (u j), hz.comp hu,
    fun j => heisenbergCommonFreeLimit_iff.mp (hc (u j)), hQ⟩
  have forms := H.forms hβ
  refine ⟨H.gibbs, forms.stationary, forms.nonnegative, ?_,
    fun _ hR O _ hx _ _ hk hl => H.angular hβ hR O hx hk hl,
    fun _ hR _ _ _ _ ha hk hl hd => H.angular_annulus hβ hR ha hk hl hd⟩
  exact originalMeasureLimits_of_tangents (fun _ hR => H.exists_isotropic_tangent hβ hR)
    (fun _ hR _ _ hv => ⟨H.isotropic hβ hR hv, H.unit_cube hβ hR hv,
      fun _ hs => H.cube_readout hβ hR hv hs⟩)

open Rotor.HeisenbergField in
theorem heisenbergExistsFieldAccumulation {β : ℝ} (hβ : 0 ≤ β)
    (fr : ∀ t : ℝ, 0 < t → ∃ P : ProbabilityMeasure (SpinField 3), HeisenbergCubeAndRectangle β t P)
    (h : ℕ → ℝ) (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (Q : ProbabilityMeasure (SpinField 3)) (u : ℕ → ℕ) (P : ℕ → ProbabilityMeasure (SpinField 3)),
      StrictMono u ∧ (∀ j, HeisenbergCubeAndRectangle β (h j) (P j)) ∧
      Tendsto (P ∘ u) atTop (𝓝 Q) ∧ HeisenbergZeroFieldReadouts β Q := by
  have input : PositiveFieldThermodynamicInput β := by
    intro t ht
    obtain ⟨P, hP⟩ := fr t ht
    exact ⟨P, heisenbergCommonFreeLimit_iff.mp hP⟩
  obtain ⟨Q, u, hu, _, P, hP, hQ⟩ := exists_vanishing_field_origin input h hp hz
  have hc := fun j => heisenbergCommonFreeLimit_iff.mpr (hP j)
  exact ⟨Q, u, P, hu, hc, hQ, heisenbergEveryFieldAccumulation hβ h hp hz P hc hu.tendsto_atTop hQ⟩

-- One nearest-neighbour Gibbs law precedes every scale, orthogonal map
-- and pair of independently chosen lattice approximations.
theorem selectedRotorOriginalReadouts (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField N), ShiftInvariant P ∧ LocalGibbs.IsNearestGibbs N β P ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
          ∀ f : C_c(Space, ℝ), Tendsto (fun j => ∫ x, f x ∂twoPointMeasure (fieldPair P) (R (u j)))
            atTop (𝓝 (∫ x, f x ∂μ))) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
        (∀ f : C_c(Space, ℝ), Tendsto (fun n => ∫ x, f x ∂twoPointMeasure (fieldPair P) (R n))
          atTop (𝓝 (∫ x, f x ∂μ))) → ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ) ∧
      (∀ (ψ : C_c(Space, ℝ)) (O : Space ≃ₗᵢ[ℝ] Space),
        Tendsto (fun n : ℕ => (∫ x, ψ (O x) ∂twoPointMeasure (fieldPair P) n) -
          ∫ x, ψ x ∂twoPointMeasure (fieldPair P) n) atTop (𝓝 0)) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space),
        x ≠ 0 → ∀ k l : ℕ → Site,
        Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
        Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
        Tendsto (fun n => ((R n : ℝ)^3 / susceptibility (fieldPair P) (R n)) *
          (fieldPair P (k n) - fieldPair P (l n))) atTop (𝓝 0)) := by
  obtain ⟨P,hstat,hg,_,_,hex,hv,hr⟩ :=
    PhysicalMirrorSelection.exists_nearest_with_rotational_two_point N hβ
  refine ⟨P,hstat,hg,?_,?_,?_,hr⟩
  · intro R hR
    obtain ⟨u,μ,hu,hlocal,hweak,hiso⟩ := hex R hR
    exact ⟨u,μ,hu,hlocal,hiso.nonzero,hweak⟩
  · intro R hR μ _ hweak O
    exact (hv R hR μ hweak).map_eq O
  · intro ψ O
    apply tendsto_of_subseq_tendsto
    intro R hR
    obtain ⟨u,μ,_,_,hweak,hiso⟩ := hex R hR
    let ψO := ψ.comp O.toHomeomorph.toCocompactMap
    have heq : (∫ x, ψ (O x) ∂μ) = ∫ x, ψ x ∂μ := by
      calc _ = ∫ x, ψ x ∂μ.map O :=
          (integral_map O.continuous.aemeasurable ψ.continuous.aestronglyMeasurable).symm
           _ = _ := by rw [hiso.map_eq O]
    have hO := hweak ψO
    change Tendsto (fun n => ∫ x, ψ (O x) ∂twoPointMeasure (fieldPair P) (R (u n)))
      atTop (𝓝 (∫ x, ψ (O x) ∂μ)) at hO
    refine ⟨u,?_⟩
    have hd := hO.sub (hweak ψ)
    simpa only [heq,sub_self,Function.comp_apply] using hd

-- The spatial permutation acts on sites, the internal orthogonal map acts
-- on the spin at each site, and the sharp-cube tangent is built from the
-- two-point function of that same probability law.
theorem selectedRotorWholeState (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β) :
    ∃ P : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β P ∧ ShiftInvariant P ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
        (P : Measure _).map (fun σ : SpinField N => σ ∘ signedPerm p s) = (P : Measure _)) ∧
      (∀ U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N),
        (P : Measure _).map (fun (σ : SpinField N) x => Rotor.SiteReflection.SphereSign.sphereMap U (σ x))
          = (P : Measure _)) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
        (∀ f : C_c(Space, ℝ), Tendsto (fun n => ∫ x, f x ∂twoPointMeasure (fieldPair P) (R n))
          atTop (𝓝 (∫ x, f x ∂μ))) →
        μ.real (observationCube 1) = 1 ∧ ModelPackets.IsotropicPairMeasure μ) ∧
      ∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x ≠ 0 →
        ∀ k l : ℕ → Site, Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
        Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
        Tendsto (fun n => ((R n : ℝ)^3 / susceptibility (fieldPair P) (R n)) *
          (fieldPair P (k n) - fieldPair P (l n))) atTop (𝓝 0) := by
  obtain ⟨P,h,hspace,hspin⟩ := PhysicalStateSymmetries.exists_symmetric_state N hβ
  refine ⟨P,h.gibbs,h.stationary,fun p s => (hspace p s).map_eq,fun U => (hspin U).map_eq,?_,
    fun R hR O x hx k l hk hl => h.raw_angular hR O hx hk hl⟩
  intro R hR μ _ hweak
  have hiso := h.isotropic hR hweak
  exact ⟨hiso.real_unit_cube_eq_one h.ferromagnetic (by rw [fieldPair_zero]; norm_num) hR hweak,hiso⟩

private theorem selectedRotorScaleReadouts {N : ℕ} [NeZero N] {β : ℝ}
    {P : ProbabilityMeasure (SpinField N)} (h : PhysicalMirrorSelection.Selected N β P) :
    OriginalMeasureLimits (fieldPair P) ∧ OriginalSiteAngular (fieldPair P) := by
  refine ⟨originalMeasureLimits_of_tangents (fun _ hR => h.exists_tangent hR) ?_,
    fun _ hR O _ hx _ _ hk hl => h.raw_angular hR O hx hk hl⟩
  intro R hR ν _ hν
  have hrot := h.isotropic hR hν
  exact ⟨hrot, hrot.real_unit_cube_eq_one h.ferromagnetic (by rw [fieldPair_zero]; norm_num) hR hν,
    fun _ hs => hrot.susceptibility_ratio_tendsto h.ferromagnetic hR hν hs⟩

open FreeExhaustion in
open scoped ProbabilityTheory in
theorem uniqueRotorDomainLaws (N : ℕ) [NeZero N] {β : ℝ} (P : ProbabilityMeasure (SpinField N))
    (unique : ∀ Q : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β Q → Q = P)
    (D : ℕ → Finset Site) (hD : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n)
    (fill : ℕ → SpinField N) (B : ℕ → ProbabilityMeasure (SpinField N)) :
    (∀ n, (freeDomainLaw N β (D n) (fill n) : Measure (SpinField N)).map
      (fun (σ : SpinField N) (x : ↥(D n)) => σ x.val) =
      (Measure.pi (fun _ : ↥(D n) => Rotor.SiteReflection.surfacePrior N)).tilted
        (fun σ => (∑ x : ↥(D n), ∑ y : ↥(D n), LocalGibbs.nearestCoupling β (y.val - x.val) *
          ⟪(σ x).val, (σ y).val⟫_ℝ) / 2)) ∧
    (∀ n, (NearestWindowRealization.boxLaw β (D n) (B n) : Measure _) =
      LocalGibbs.kernel (D n) (LocalGibbs.windowEnergy N (D n) (LocalGibbs.nearestCoupling β)
        (LocalGibbs.summable_abs_nearest β)) ∘ₘ (B n : Measure _)) ∧
    Tendsto (fun n => freeDomainLaw N β (D n) (fill n)) atTop (𝓝 P) ∧
    Tendsto (fun n => NearestWindowRealization.boxLaw β (D n) (B n)) atTop (𝓝 P) :=
  ⟨fun n => freeDomain_marginal N β (D n) (fill n), fun _ => rfl,
    freeDomain_tendsto_of_unique N P unique D hD fill, boundary_tendsto_of_unique N P unique D hD B⟩

open FreeExhaustion in
theorem uniqueRotorDomainPairs (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (P : ProbabilityMeasure (SpinField N)) (unique : ∀ Q, LocalGibbs.IsNearestGibbs N β Q → Q = P)
    (D : ℕ → Finset Site) (hD : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) :
    let g := fun z : Site => ∫ σ : SpinField N, ⟪(σ 0).val, (σ z).val⟫_ℝ ∂(P : Measure _)
    (∀ x y : Site, Tendsto (fun n =>
      if hx : x ∈ D n then if hy : y ∈ D n then
        dotPair N (fun a b : ↥(D n) => LocalGibbs.nearestCoupling β (b.val - a.val))
          ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0) atTop (𝓝 (g (x - y)))) ∧
    (∀ x y : Site, Tendsto (fun L => Rotor.SiteReflection.freePair (Rotor.SiteReflection.surfacePrior N)
      β L x y) atTop (𝓝 (g (x - y)))) ∧ OriginalMeasureLimits g ∧ OriginalSiteAngular g := by
  obtain ⟨Q, hQ⟩ := PhysicalMirrorSelection.exists_state N hβ
  have hP : PhysicalMirrorSelection.Selected N β P := by
    rw [← unique Q hQ.gibbs]
    exact hQ
  exact ⟨freePair_tendsto_of_unique N hβ P unique D hD, stationary_freeCubePair_of_unique N hβ P unique,
    selectedRotorScaleReadouts hP⟩

-- The limits and the independent moving sites below refer to the dot integral
-- of the same law realized by the ordinary finite torus Gibbs probabilities.
theorem selectedRotorPeriodicOrigin (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hzero : Tendsto δ atTop (𝓝 0)) (lower : ℕ → ℕ) :
    ∃ (P : ProbabilityMeasure (SpinField N)) (u m : ℕ → ℕ),
      let g := fun z : Site => ∫ σ : SpinField N, ⟪(σ 0).val, (σ z).val⟫_ℝ ∂(P : Measure _)
      StrictMono u ∧ StrictMono m ∧ (∀ n, lower n ≤ m n) ∧
      Tendsto (fun n => rootedLaw N Seam.baseMove
        (Seam.ordinarySeries (2 * (m n + 1)) (PhysicalVariations.J β (δ (u n))))) atTop (𝓝 P) ∧
      (∀ z : Site, Tendsto (fun n => cubicPair N (2 * (m n + 1))
        (PhysicalVariations.J β (δ (u n))) z) atTop (𝓝 (g z))) ∧
      (∀ (Λ : Finset Site) (F : C(SpinField N, ℝ)), (∫ σ, F σ ∂(P : Measure _)) =
        ∫ σ, LocalGibbs.readout Λ (LocalGibbs.windowEnergy N Λ
          (LocalGibbs.nearestCoupling β) (LocalGibbs.summable_abs_nearest β)) F σ ∂(P : Measure _)) ∧
      ShiftInvariant P ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
        (P : Measure _).map (fun σ : SpinField N => σ ∘ signedPerm p s) = (P : Measure _)) ∧
      (∀ U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N),
        (P : Measure _).map (fun (σ : SpinField N) x => Rotor.SiteReflection.SphereSign.sphereMap U (σ x))
          = (P : Measure _)) ∧
      PhysicalMirrorSelection.ThreeMirrors g ∧ OriginalMeasureLimits g ∧ OriginalSiteAngular g := by
  obtain ⟨P, u, m, hu, hm, hmin, hweak, h, hs, hi⟩ :=
    PeriodicStateRealization.exists_selected_periodic_sequence N hβ δ hδ hzero lower
  exact ⟨P, u, m, hu, hm, hmin, hweak, PeriodicStateRealization.finite_pair_tendsto hweak,
    h.gibbs, h.stationary, fun p s => (hs p s).map_eq, fun U => (hi U).map_eq, h.mirrors,
    selectedRotorScaleReadouts h⟩

theorem rotorPeriodicLimitOfUniqueness (N : ℕ) [NeZero N] {β : ℝ}
    (P : ProbabilityMeasure (SpinField N))
    (unique : ∀ Q : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β Q → Q = P)
    (side : ℕ → ℕ) [∀ n, NeZero (side n)] (hside : Tendsto side atTop atTop)
    (K : ℕ → Site → ℝ) (hK : ∀ n, Summable fun z => |K n z|)
    (hclose : Tendsto (fun n => ∑' z, |K n z - LocalGibbs.nearestCoupling β z|) atTop (𝓝 0)) :
    Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n) (K n))) atTop (𝓝 P) :=
  PeriodicStateRealization.periodic_tendsto_of_unique N P unique side hside K hK hclose

open LocalGibbs NearestWindowRealization in
theorem rotorNearestBoxBoundary (N : ℕ) [NeZero N] (β : ℝ) (Λ : Finset Site) (s : SpinField N) :
    ((nearestResample N Λ β s : Measure (SpinField N)).map Λ.restrict =
      (Measure.pi (fun _ : Λ => Rotor.SiteReflection.surfacePrior N)).tilted
        (fun a => windowEnergy N Λ (nearestCoupling β) (summable_abs_nearest β) (replace Λ s a))) ∧
    ∀ t : SpinField N, (∀ x ∈ (Λ.biUnion fun y => nearestSteps.image (fun z => y + z)) \ Λ, s x = t x) →
      (nearestResample N Λ β s : Measure (SpinField N)).map Λ.restrict =
        (nearestResample N Λ β t : Measure (SpinField N)).map Λ.restrict :=
  ⟨nearestResample_inside N β Λ s, fun _ hlayer => nearestResample_inside_of_layer N β Λ hlayer⟩

open NearestWindowRealization in
theorem selectedRotorNearestBoxes (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hzero : Tendsto δ atTop (𝓝 0)) :
    ∃ Q : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β Q ∧ ShiftInvariant Q ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
        (Q : Measure _).map (fun σ : SpinField N => σ ∘ signedPerm p s) = (Q : Measure _)) ∧
      (∀ U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N),
        (Q : Measure _).map (fun (σ : SpinField N) x => Rotor.SiteReflection.SphereSign.sphereMap U (σ x))
          = (Q : Measure _)) ∧
      PhysicalMirrorSelection.ThreeMirrors (fieldPair Q) ∧
      (OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q)) ∧
      ∀ L : ℕ → ℕ, ∃ u m : ℕ → ℕ,
        let B := fun n => rootedLaw N Seam.baseMove
          (Seam.ordinarySeries (2 * (m n + 1)) (PhysicalVariations.J β (δ (u n))))
        StrictMono u ∧ StrictMono m ∧ (∀ n, L n < m n) ∧ Tendsto B atTop (𝓝 Q) ∧
          Tendsto (fun n => boxLaw β (cube (L n)) (B n)) atTop (𝓝 Q) := by
  obtain ⟨Q, h, hs, hi, hbox⟩ := exists_selected_nearest_boxes N hβ δ hδ hzero
  exact ⟨Q, h.gibbs, h.stationary, fun p s => (hs p s).map_eq, fun U => (hi U).map_eq,
    h.mirrors, selectedRotorScaleReadouts h, hbox⟩

theorem rotorLimitOfUniqueTemperatures (N : ℕ) [NeZero N] {b : ℕ → ℝ} {β : ℝ}
    (hb : ∀ n, 0 ≤ b n) (ht : Tendsto b atTop (𝓝 β))
    (P : ℕ → ProbabilityMeasure (SpinField N)) {Q : ProbabilityMeasure (SpinField N)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (unique : ∀ n W, LocalGibbs.IsNearestGibbs N (b n) W → W = P n) :
    LocalGibbs.IsNearestGibbs N β Q ∧ ShiftInvariant Q ∧
    (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
      (Q : Measure _).map (fun σ : SpinField N => σ ∘ signedPerm p s) = (Q : Measure _)) ∧
    (∀ U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N),
      (Q : Measure _).map (fun (σ : SpinField N) x => Rotor.SiteReflection.SphereSign.sphereMap U (σ x))
        = (Q : Measure _)) ∧ PhysicalMirrorSelection.ThreeMirrors (fieldPair Q) ∧
    OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q) := by
  obtain ⟨h, hs, hi⟩ :=
    PeriodicStateRealization.selected_of_unique_temperature_limit N hb ht P hQ unique
  exact ⟨h.gibbs, h.stationary, fun p s => (hs p s).map_eq, fun U => (hi U).map_eq,
    h.mirrors, selectedRotorScaleReadouts h⟩

theorem zeroRotorProduct (N : ℕ) [NeZero N] :
    let P : ProbabilityMeasure (SpinField N) :=
      ⟨Measure.infinitePi (fun _ : Site => Rotor.SiteReflection.surfacePrior N), inferInstance⟩
    LocalGibbs.IsNearestGibbs N 0 P ∧
    (∀ Q : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N 0 Q → Q = P) ∧
    ∀ (side : ℕ → ℕ) [∀ n, NeZero (side n)], Tendsto side atTop atTop →
      Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (side n)
        (LocalGibbs.nearestCoupling 0))) atTop (𝓝 P) := by
  have unique := PeriodicStateRealization.zero_gibbs_eq_product N
  obtain ⟨W, hW⟩ := PhysicalMirrorSelection.exists_state (β := 0) N (by norm_num)
  have hproduct : LocalGibbs.IsNearestGibbs N 0 (PeriodicStateRealization.independentLaw N) := by
    rw [← unique W hW.gibbs]
    exact hW.gibbs
  refine ⟨hproduct, unique, ?_⟩
  intro side _ hside
  apply PeriodicStateRealization.periodic_tendsto_of_unique N _ unique side hside
    (fun _ => LocalGibbs.nearestCoupling 0) (fun _ => LocalGibbs.summable_abs_nearest 0)
  simp

theorem highTemperatureFreeRotor (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 6 * Real.tanh β < 1) :
    ∃ P : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β P ∧
      (∀ Q : ProbabilityMeasure (SpinField N), LocalGibbs.IsNearestGibbs N β Q → Q = P) ∧
      (∀ D : ℕ → Finset Site, (∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) →
        ∀ fill : ℕ → SpinField N, ∀ B : ℕ → ProbabilityMeasure (SpinField N),
          Tendsto (fun n => FreeExhaustion.freeDomainLaw N β (D n) (fill n)) atTop (𝓝 P) ∧
          Tendsto (fun n => NearestWindowRealization.boxLaw β (D n) (B n)) atTop (𝓝 P)) ∧
      (let g := fun z : Site => ∫ σ : SpinField N, ⟪(σ 0).val, (σ z).val⟫_ℝ ∂(P : Measure _)
       OriginalMeasureLimits g ∧ OriginalSiteAngular g) := by
  obtain ⟨P,hP⟩ := PhysicalMirrorSelection.exists_state N hβ
  have unique (Q : ProbabilityMeasure (SpinField N)) (hQ : LocalGibbs.IsNearestGibbs N β Q) : Q = P :=
    HighTemperature.nearest_gibbs_eq_tanh hβ hsmall hQ hP.gibbs
  exact ⟨P,hP.gibbs,unique,fun D hD fill B =>
    ⟨FreeExhaustion.freeDomain_tendsto_of_unique N P unique D hD fill,
     FreeExhaustion.boundary_tendsto_of_unique N P unique D hD B⟩,selectedRotorScaleReadouts hP⟩

open Rotor.HeisenbergField in
theorem heisenbergPairComparisonReadout {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 ≤ h j) (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (inner : ∀ j, ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j)) ∧
      (∀ x y : Site, Tendsto (fun n =>
        (∫ s, fieldDot 3 x y s ∂(cubeLaw β (h j) (L n) : Measure _)) -
         ∫ s, fieldDot 3 0 (x-y) s ∂(cubeLaw β (h j) (L n) : Measure _)) atTop (𝓝 0)) ∧
      ∀ x y : Site, 0 < x 0 → 0 < y 0 →
        Tendsto (fun n => Rotor.BondRectangle.crossPair (fieldPrior (h j)) β
          (BondMirror.port (L n) x) (BondMirror.port (L n) y) -
          ∫ s, fieldDot 3 x (BondMirror.reflected y) s
            ∂(cubeLaw β (h j) (L n) : Measure _)) atTop (𝓝 0)) :
    LocalGibbs.IsNearestGibbs 3 β Q ∧
      OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q) := by
  obtain ⟨hg,H⟩ := gibbs_dotForms_of_free_field_limits hβ hp hz hQ (fun j => by
    obtain ⟨L,hL,hP,ht,hr⟩ := inner j
    exact ⟨L,hL,hP,⟨ht,hr⟩⟩)
  exact ⟨hg, originalMeasureLimits_of_tangents (fun _ hR => H.exists_isotropic_tangent hR)
    (fun _ hR _ _ hv => H.tangent_readout hR hv),
    fun _ hR O _ hx _ _ hk hl => H.angular hR O hx hk hl⟩

open Rotor.HeisenbergField in
theorem heisenbergJointScheduleTanh {β : ℝ} (hβ : 0 ≤ β) (hsmall : 6*Real.tanh β < 1) :
    ∃ Q : ProbabilityMeasure (SpinField 3), LocalGibbs.IsNearestGibbs 3 β Q ∧
      (∀ (L : ℕ → ℕ) (h : ℕ → ℝ), Tendsto L atTop atTop → Tendsto h atTop (𝓝 0) →
        Tendsto (fun j => cubeLaw β (h j) (L j)) atTop (𝓝 Q)) ∧
      OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q) := by
  obtain ⟨Q,hQ⟩ := PhysicalMirrorSelection.exists_state 3 hβ
  exact ⟨Q,hQ.gibbs,fun _ _ hL hz => joint_free_cube_tendsto_of_unique
    (fun P hP => HighTemperature.nearest_gibbs_eq_tanh hβ hsmall hP hQ.gibbs) hL hz,
    selectedRotorScaleReadouts hQ⟩

open Rotor.HeisenbergField Rotor.HeisenbergField.PositiveFieldContinuation in
theorem heisenbergAnalyticFreeReadout {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => ComplexPartition.cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    {h : ℕ → ℝ} (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q)) (inner : ∀ j, ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) :
    LocalGibbs.IsNearestGibbs 3 β Q ∧ OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q) := by
  obtain ⟨gibbs,H⟩ := gibbs_dotForms_of_complex_control hβ C D hp hz hQ inner
  exact ⟨gibbs,originalMeasureLimits_of_tangents (fun _ hR => H.exists_isotropic_tangent hR)
    (fun _ hR _ _ hv => H.tangent_readout hR hv),
    fun _ hR O _ hx _ _ hk hl => H.angular hR O hx hk hl⟩

open Rotor.HeisenbergField in
theorem heisenbergPhysicalPartitionCone {V : Type*} [Fintype V] (J : V → V → ℝ)
    (hJ : ∀ x y : V, 0 ≤ J x y) (H : V → Fin 3 → ℂ)
    (hcone : ∀ x, ‖H x 1‖ + ‖H x 2‖ < (H x 0).re) :
    (∫ s : V → Rotor.Spin 3,
      Complex.exp (Complex.ofReal ((∑ x : V, ∑ y : V, J x y * ⟪(s x).val,(s y).val⟫_ℝ) / 2) +
        ∑ x : V, ∑ i : Fin 3, H x i * Complex.ofReal ((s x).val i))
      ∂(Measure.pi fun _ : V => Rotor.SiteReflection.surfacePrior 3)) ≠ 0 :=
  FerromagneticLeeYang.partition_ne_zero J hJ H hcone

open Rotor.HeisenbergField Rotor.HeisenbergField.PhysicalRotation in
theorem heisenbergPhysicalPositiveFreeLaw {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 < h) :
    ∃! P : ProbabilityMeasure (SpinField 3), IsFieldGibbs β h P ∧
      HeisenbergCubeAndRectangle β h P := by
  obtain ⟨P,hP,uniq⟩ := unique_positive_free_limit hβ hh
  exact ⟨P,⟨hP.1,heisenbergCommonFreeLimit_iff.mpr hP.2⟩,
    fun Q hQ => uniq Q ⟨hQ.1,heisenbergCommonFreeLimit_iff.mp hQ.2⟩⟩

open Rotor.HeisenbergField Rotor.HeisenbergField.PhysicalRotation in
theorem heisenbergPhysicalFreeReadout {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q)) (inner : ∀ j, ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) :
    LocalGibbs.IsNearestGibbs 3 β Q ∧
      OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q) := by
  have hp_eq : P = fun j => positiveFreeLaw hβ (hp j) := by
    funext j
    obtain ⟨L,hL,hP⟩ := inner j
    exact tendsto_nhds_unique hP ((free_boxes_tendsto hβ (hp j)).comp hL)
  rw [hp_eq] at hQ
  have H := fun (R : ℕ → ℕ) (hR : Tendsto R atTop atTop) => sharp_rotation hβ hp hz hQ hR
  exact ⟨(H id tendsto_id).1, originalMeasureLimits_of_tangents (fun R hR => (H R hR).2.1)
    (fun R hR => (H R hR).2.2),
    fun _ hR O _ hx _ _ hk hl => rounded_rotation hβ hp hz hQ hR O hx hk hl⟩

open Rotor.HeisenbergField Rotor.HeisenbergField.PhysicalRotation in
theorem heisenbergPhysicalFreeSubsequence {β : ℝ} (hβ : 0 ≤ β) {h : ℕ → ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (P : ℕ → ProbabilityMeasure (SpinField 3)) (u : ℕ → ℕ) (Q : ProbabilityMeasure (SpinField 3)),
      (∀ j, Tendsto (fun n => cubeLaw β (h j) n) atTop (𝓝 (P j))) ∧ StrictMono u ∧
      Tendsto (P ∘ u) atTop (𝓝 Q) ∧ LocalGibbs.IsNearestGibbs 3 β Q ∧
      OriginalMeasureLimits (fieldPair Q) ∧ OriginalSiteAngular (fieldPair Q) := by
  obtain ⟨u,Q,hu,hQ,_⟩ := exists_vanishing_limit hβ hp hz
  refine ⟨fun j => positiveFreeLaw hβ (hp j),u,Q,fun j => free_boxes_tendsto hβ (hp j),hu,hQ,?_⟩
  exact heisenbergPhysicalFreeReadout hβ (fun j => hp (u j)) (hz.comp hu.tendsto_atTop)
    hQ (fun j => ⟨id,tendsto_id,free_boxes_tendsto hβ (hp (u j))⟩)

#check selectedRotorWholeState 1 (β := 0) (by norm_num)
#check freeFKOriginalReadouts (q := 2) (by decide) (p := 0) (by norm_num) (by norm_num)
#check xyFreeOriginalReadouts (β := 0) (by norm_num)
end PacketAlignment
"""

READOUTS = (
    "sameIsingGrid", "IsingTangent", "PottsGrid", "sphereGrid", "canonicalPottsGrid",
    "canonicalPottsShiftedMirrors", "rotorEvenPoints", "rotorCommonRectangleAnnulus",
    "canonicalPottsTangent", "sphereTangent", "physicalMeasureWeights", "freePottsBondSum",
    "canonicalPottsCubeLimits", "canonicalPottsOriginalReadouts", "freeFKCubeLimits",
    "freeFKOriginalReadouts", "finiteFKBondEvents", "freeFKBondField", "finiteFKInducedPaths",
    "freeFKInducedExhaustion", "freeSphereGibbsPair",
    "prescribedRotorCubeLimits",
    "xyFiniteGibbsMonotone", "xyFreeCubeAndRectangle", "xyFreeInducedExhaustion",
    "xyFreeOriginalReadouts", "xyFreeAnnulus",
    "heisenbergFiniteFieldLaw", "heisenbergFixedFieldDLR", "heisenbergScalarFieldInput",
    "heisenbergEveryFieldAccumulation",
    "heisenbergExistsFieldAccumulation", "heisenbergPairComparisonReadout", "heisenbergJointScheduleTanh",
    "heisenbergAnalyticFreeReadout", "heisenbergPhysicalPartitionCone",
    "heisenbergPhysicalPositiveFreeLaw", "heisenbergPhysicalFreeReadout", "heisenbergPhysicalFreeSubsequence",
    "selectedRotorOriginalReadouts", "selectedRotorWholeState", "selectedRotorPeriodicOrigin",
    "uniqueRotorDomainLaws", "uniqueRotorDomainPairs", "highTemperatureFreeRotor",
    "rotorPeriodicLimitOfUniqueness", "rotorNearestBoxBoundary", "selectedRotorNearestBoxes",
    "rotorLimitOfUniqueTemperatures", "zeroRotorProduct",
)

ENDPOINTS = {
    "IsingScaling.Potts.SiteBox": (
        "canonicalFreePair_stationary", "StationaryPairLimit.eq_canonicalFreePair",
        "canonicalFreePair_raw_angular", "boxConnectivity_eq_boxPair",
        "freeConnectivity_eq_canonicalFreePair", "latticeConnectivity_tendsto",
        "freeConnectivity_tangent", "freeConnectivity_exists_tangent", "freeConnectivity_raw_angular",
    ),
    "IsingScaling.Potts.FreeBond": (
        "freeCubeLaw_real", "exists_free_bond_law", "tendsto_freeLaw", "freeLaw_connection",
        "freeLaw_exists_tangent", "freeLaw_tangent", "freeLaw_raw_angular",
        "freeDomainLaw_connection_eq_finite", "freeDomainLaw_mono", "tendsto_freeDomainLaw_atTop",
        "exhaustion_tendsto_freeLaw", "exhaustion_connection_tendsto",
    ),
    "IsingScaling.Rotor.IsStationaryFreeCubePairLimit": (
        "surface_isotropic", "surface_exists_isotropic_tangent", "surface_cube_readout",
        "raw_angular_even_lattice", "raw_angular_annulus_of_crossPair_limit",
    ),
    "IsingScaling.Rotor.XY": (
        "graphPair_mono", "canonicalFreePair_stationary", "finitePair_tendsto_of_exhaustion", "crossPair_tendsto",
        "canonicalFreePair_axialBond_positive", "canonicalFreePair_exists_isotropic_tangent",
        "canonicalFreePair_isotropic", "canonicalFreePair_cube_readout", "canonicalFreePair_raw_angular",
        "canonicalFreePair_raw_annulus",
    ),
    "IsingScaling.Rotor.HeisenbergField": (
        "eq_of_spinMoments", "ScalarThermodynamicLimit.exists_commonFreeLimit", "positiveFieldInput_iff_scalar",
        "fieldPrior_product", "freePair_nonnegative", "cubeLaw_integral", "cubeLaw_pair",
        "CommonFreeLimit.forms", "exists_vanishing_field_origin", "free_cube_field_conditional",
        "field_gibbs_of_free_cube_limit", "nearest_gibbs_of_vanishing_field", "VanishingFieldOrigin.gibbs",
        "VanishingFieldOrigin.angular", "VanishingFieldOrigin.angular_annulus", "VanishingFieldOrigin.isotropic",
        "VanishingFieldOrigin.exists_isotropic_tangent", "VanishingFieldOrigin.cube_readout", "VanishingFieldOrigin.unit_cube",
        "gibbs_of_joint_free_cube_limit", "gibbs_dotForms_of_free_field_limits",
        "exists_free_field_limit_of_dot_comparisons", "joint_free_cube_tendsto_of_unique",
        "DotForms.angular", "DotForms.tangent_readout", "DotForms.exists_isotropic_tangent",
    ),
    "IsingScaling.Rotor.HeisenbergField.PositiveFieldContinuation": (
        "finiteDot_eq_sum_coordinateRatios", "norm_finiteDot_le_three_mul",
        "freeDotComparison_of_complex_control", "cube_dot_limit_of_complex_control",
        "exists_common_free_dot_kernel", "gibbs_dotForms_of_complex_control",
        "exists_gibbs_dotForms_of_complex_control",
    ),
    "IsingScaling.Rotor.HeisenbergField.FerromagneticLeeYang": ("partition_ne_zero",),
    "IsingScaling.Rotor.HeisenbergField.PhysicalRotation": (
        "unique_positive_free_limit", "positiveFreeLaw_spec", "free_boxes_tendsto",
        "exists_vanishing_limit", "sharp_rotation", "rounded_rotation",
    ),
    "IsingScaling.Rotor.PressureSelection.HighTemperature": (
        "nearest_gibbs_eq_tanh", "exists_unique_nearest_gibbs_tanh",
        "exists_unique_nearest_gibbs", "freeDomain_tendsto", "boundary_tendsto",
        "freePair_tendsto", "state_exists_tangent", "state_tangent", "state_raw_angular",
    ),
    "IsingScaling.Rotor.PressureSelection.Dobrushin": ("density_cross_ratio", "update_other_tanh"),
    "IsingScaling.Rotor.PressureSelection.PhysicalMirrorSelection": (
        "exists_nearest_with_rotational_two_point",
    ),
    "IsingScaling.Rotor.PressureSelection.PhysicalStateSymmetries": (
        "exists_symmetric_nearest_with_rotational_two_point",
    ),
    "IsingScaling.Rotor.PressureSelection.PeriodicStateRealization": (
        "exists_selected_periodic_sequence", "finite_pair_tendsto", "periodic_tendsto_of_unique",
        "selected_of_unique_temperature_limit", "zero_gibbs_eq_product",
    ),
    "IsingScaling.Rotor.PressureSelection.NearestWindowRealization": (
        "nearestResample_inside", "nearestResample_inside_of_layer", "boxLaw_outside",
        "boxLaw_idempotent", "exists_selected_nearest_boxes",
    ),
    "IsingScaling.Rotor.PressureSelection.FreeExhaustion": (
        "freeDomain_marginal", "freeDomain_tendsto_of_unique", "boundary_tendsto_of_unique",
        "freePair_cube", "freePair_tendsto_of_unique", "stationary_freeCubePair_of_unique",
    ),
}


def check_axioms(output: str, expected: set[str]) -> None:
    standard = {"propext", "Quot.sound", "Classical.choice"}
    found = {}
    for name, report in re.findall(
        r"^'([\w.]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
        output, re.MULTILINE,
    ):
        if name in found:
            raise RuntimeError(f"Duplicate axiom report for {name}")
        found[name] = {axiom.strip() for axiom in report.split(",") if axiom.strip()}
    if found.keys() != expected:
        raise RuntimeError(f"Missing axiom reports {sorted(expected - found.keys())}, "
                           f"unexpected reports {sorted(found.keys() - expected)}")
    forbidden = {name: sorted(axioms - standard) for name, axioms in found.items()
                 if axioms - standard}
    if forbidden:
        raise RuntimeError(f"Nonstandard transitive axioms {forbidden}")


def main() -> int:
    endpoints = [f"{namespace}.{name}" for namespace, names in ENDPOINTS.items() for name in names]
    names = [f"PacketAlignment.{name}" for name in READOUTS] + endpoints
    directives = "\n".join(f"#print axioms {name}" for name in names)
    probe = subprocess.run(
        ["lake", "env", "lean", "--stdin"], input=PROBE + directives + "\n", cwd=PROJECT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if probe.returncode:
        sys.stderr.write(probe.stdout)
        return probe.returncode
    check_axioms(probe.stdout, set(names))
    print(f"PASS {len(READOUTS)} typed readouts and {len(endpoints)} named endpoint axiom closures.")
    print("Each closure uses only standard Lean axioms. Zero closures contain sorryAx.")
    print("For integer q >= 2 and 0 <= p < 1, all exhaustions by finite induced domains converge to "
          "the same free bond law. Their open-path probabilities converge to its path probabilities "
          "and equal the canonical Potts simplex pair in the limit.")
    print("The original measures, radial densities, sharp cube ratios and independent lattice sites "
          "use those path probabilities.")
    print("For all N >= 1, beta >= 0 and positive auxiliary strengths tending to zero, one selected "
          "nearest-neighbour Gibbs law carries both full-law symmetries and the spatial readouts.")
    print("For every box schedule that same law is a weak limit of the finite torus approximants "
          "and of the nearest-neighbour boxes with boundary sampled from those tori.")
    print("The prescribed free-cube kernel requires joint stationary pair convergence. Its site tests "
          "use even sites, or arbitrary sites given a common bond-rectangle limit.")
    print("For the planar rotor (N = 2), arbitrary exhausting finite induced sets and the bond rectangles "
          "give one canonical dot pair with the sharp-cube, full-lattice point and moving-annulus readouts.")
    print("For every finite set, nonnegative coupling matrix and site-dependent Heisenberg field "
          "in the three-component Lee-Yang cone, the original normalized sphere integral is nonzero.")
    print("For every beta >= 0 and h > 0 the complete sequence of free cubes converges to a "
          "stationary probability measure. Its crossing dot pairs are also the free rectangle limits.")
    print("On every positive-field schedule tending to zero such a weak accumulation law exists. "
          "Every such law Q satisfies the zero-field DLR, sharp tangent and original-site angular "
          "readouts for the dot pair of this same Q.")
    print("Two finite dot-comparison limits suffice for the spatial readouts of a specified iterated "
          "Heisenberg accumulation law. At high temperature, arbitrary simultaneous free volumes "
          "and signed fields tending to zero converge to one Gibbs law before spatial tests are chosen.")
    print("Under uniqueness, the full periodic laws, arbitrary exhausting free domains, and domains with "
          "varying random exterior laws converge to the same nearest-neighbour Gibbs law.")
    print("At beta = 0, the unique rotor Gibbs law is the infinite product of the normalized sphere priors.")
    print("For every N >= 1 and 0 <= beta with 6*tanh(beta) < 1, uniqueness, arbitrary "
          "free and random-boundary exhaustions, and spatial readouts follow with no uniqueness premise.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
