import MathlibProbe.PottsCanonicalFreePair
import MathlibProbe.PottsFreeCubeConnectivity
import MathlibProbe.ModelPacketLatticeCompactness

/-! # The canonical free Potts pair and spatial rotations

Use the same centered simplex spin mark and free-cube exhaustion for every
pair. With all sites fixed by the identity mirror, its quadratic form is
the Gibbs expectation of the squared norm of the marked spin sum. The
finite-volume square passes to the common thermodynamic limit. The
Edwards--Sokal identity supplies its pointwise nonnegativity. These facts,
its cubic symmetry and the site-reflected packet moments apply to the
susceptibility computed from this very pair function.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology CompactlySupported
namespace IsingScaling.Potts.SiteBox

private def identityWall (L : ℕ) : BoxSiteMirror L where
  tip _ := 0
  refl := Equiv.refl _
  invol _ := rfl
  wall _ _ := rfl
  neg _ := by simp
  dist _ _ := rfl
  separated _ _ h := False.elim (lt_irrefl _ h)

/-- The ordinary covariance Gram form of the same stationary Potts pair.
Repeated sites and signed real coefficients are allowed. -/
theorem StationaryPairLimit.stationaryPositive {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (hL : Tendsto sizes atTop atTop) :
    SpatialEnvelope.StationaryPositive g := by
  intro ι _ x c
  exact hg.reflected_positive hq hL (fun _ => 0) id identityWall
    (fun _ _ => rfl) (fun _ _ => rfl) x (fun _ => le_rfl) c

/-- The canonical, all-volume free Potts limit realizes even-layer lattice
moments, symmetry and a strictly positive original cube susceptibility. -/
theorem canonicalFreePair_normalizedPacketSource {q : ℕ} (hq : 2 ≤ q) {β : ℝ}
    (hβ : 0 ≤ β) (R : ℕ → ℕ) : Packet.NormalizedPacketSource (canonicalFreePair q β) R := by
  have h := canonicalFreePair_stationary hq hβ
  exact ⟨fun d {_} _ c x y => h.gridPacket_spectrum hq tendsto_id d c x y,
    h.signedPerm_invariant,fun n => h.cube_pos_of_nonneg hq (h.ferromagnetic_nonneg hq hβ) (R n)⟩

/-- Every moving-site profile on the given scale sequence and the actual
measure it realizes are invariant under all orthogonal maps. -/
theorem canonicalFreePair_rotation_of_spatial_limit {q : ℕ} (hq : 2 ≤ q) {β : ℝ}
    (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space, ℝ), Tendsto
      (fun n => ∫ v, φ v ∂twoPointMeasure (canonicalFreePair q β) (R n))
      atTop (𝓝 (∫ v, φ v ∂μ)))
    {f : Space → ℝ} (hsp : Packet.OffOriginLimit (canonicalFreePair q β) R f)
    (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x :=
  ModelPackets.rotation_of_spatial_limit (canonicalFreePair_normalizedPacketSource hq hβ R)
    ((canonicalFreePair_stationary hq hβ).ferromagnetic_nonneg hq hβ) hR hv hsp O

/-- Under the indicated lattice oscillation estimate, each vague tangent
has one common subsequence realizing a radial spatial profile. -/
theorem canonicalFreePair_rotation_of_localOscillation {q : ℕ} (hq : 2 ≤ q) {β : ℝ}
    (hβ : 0 ≤ β) {C : ℝ} {D r₀ : ℕ} (hC : 0 ≤ C) (hD : 2 ≤ D)
    (hosc : SpatialEnvelope.LocalOscillation (canonicalFreePair q β) C D r₀)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space, ℝ), Tendsto
      (fun n => ∫ v, φ v ∂twoPointMeasure (canonicalFreePair q β) (R n))
      atTop (𝓝 (∫ v, φ v ∂μ))) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧
      Packet.OffOriginLimit (canonicalFreePair q β) (R ∘ u) f ∧
      ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  have h := canonicalFreePair_stationary hq hβ
  exact ModelPackets.rotation_of_localOscillation (canonicalFreePair_normalizedPacketSource hq hβ R)
    (h.ferromagnetic_nonneg hq hβ) (fun z => (le_abs_self _).trans (h.abs_le_one hq z))
    (h.stationaryPositive hq tendsto_id) hC hD hosc hR hv

#print axioms StationaryPairLimit.stationaryPositive
#print axioms canonicalFreePair_normalizedPacketSource
#print axioms canonicalFreePair_rotation_of_spatial_limit
#print axioms canonicalFreePair_rotation_of_localOscillation
end IsingScaling.Potts.SiteBox
