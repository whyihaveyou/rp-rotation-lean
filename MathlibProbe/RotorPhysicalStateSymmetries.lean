import MathlibProbe.RotorPhysicalMirrorSelection
import MathlibProbe.RotorInternalOrthogonal

/-! # Whole-law symmetries of the state carrying the rotational two-point function

At fixed auxiliary strength, the single spin law chosen before testing
any reflection is a limit of ordinary periodic Gibbs probabilities. Each
finite probability is invariant under a common orthogonal map of all
spins, by invariance of the surface product law and every dot product.
It is also invariant under lattice signed permutations, by reindexing
the torus at the original cubic baseline interaction. Integrals of
continuous tests pass both invariances through the periodic limit.

The previously selected nearest-neighbour law is a weak limit of these
same full spin laws at vanishing auxiliary strengths. Applying each
fixed transformation to bounded continuous tests commutes with that
weak limit. The inner subsequences and the final subsequence coincide
with those in the DLR and packet proof. This preserves one witness for
all full-law symmetries and all two-point measurement scales.
-/

noncomputable section
open scoped Topology
open MeasureTheory Filter

namespace IsingScaling.Rotor.PressureSelection.PhysicalStateSymmetries
open IsingRotation Packet PhysicalMirrorSelection PhysicalVariations

/-- Full laws on the infinite spin configuration space. The first
group acts on lattice positions; the second acts on the spin values. -/
theorem exists_symmetric_state (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0≤β) :
    ∃ P : ProbabilityMeasure (SpinField N), Selected N β P ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), PeriodicHorizontal.FixedBy P (signedPerm p s)) ∧
      InternalOrthogonal.AllInternalInvariant P := by
  obtain ⟨Q,h,δ,P,_,_,hOrigin,hQ⟩ := exists_state_with_origin N hβ
  refine ⟨Q,h,?_,?_⟩
  · intro p s
    apply PeriodicHorizontal.fixed_of_tendsto hQ
    apply Eventually.of_forall
    intro n
    obtain ⟨l,_,hP⟩ := hOrigin n
    exact PeriodicHorizontal.cubic_limit_signed N (fun j => 2*(l j+1))
      (fun _ => J β (δ n)) (P n) hP p s (Eventually.of_forall fun _ => J_signedPerm β (δ n) p s)
  · apply InternalOrthogonal.invariant_of_tendsto hQ
    intro n
    obtain ⟨l,_,hP⟩ := hOrigin n
    exact InternalOrthogonal.cubic_limit_invariant N (fun j => 2*(l j+1)) (fun _ => J β (δ n)) (P n) hP

/-- End-to-end theorem with one physical sphere-spin Gibbs law. The
choice of P depends only on β and N, prior to specifying any scales,
cut locations, continuum isometries, or microscopic spin rotations. -/
theorem exists_symmetric_nearest_with_rotational_two_point (N : ℕ) [NeZero N] {β : ℝ} (hβ : 0≤β) :
    ∃ P : ProbabilityMeasure (SpinField N), ShiftInvariant P ∧ LocalGibbs.IsNearestGibbs N β P ∧
      (∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), PeriodicHorizontal.FixedBy P (signedPerm p s)) ∧
      InternalOrthogonal.AllInternalInvariant P ∧
      ThreeMirrors (fieldPair P) ∧ (∀ R : ℕ → ℕ, NormalizedPacketSource (fieldPair P) R 0) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop →
        ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
          ModelPackets.VaguePairLimit (fieldPair P) (R ∘ u) μ ∧ ModelPackets.IsotropicPairMeasure μ) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (μ : Measure Space) [IsLocallyFiniteMeasure μ],
        ModelPackets.VaguePairLimit (fieldPair P) R μ → ModelPackets.IsotropicPairMeasure μ) ∧
      (∀ (R : ℕ → ℕ), Tendsto R atTop atTop → ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x≠0 →
        ∀ k l : ℕ → Site, Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x) →
        Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x)) →
        Tendsto (fun n => normalization (fieldPair P) (R n) *
          (fieldPair P (k n)-fieldPair P (l n))) atTop (𝓝 0)) := by
  obtain ⟨P,h,hs,hi⟩ := exists_symmetric_state N hβ
  exact ⟨P,h.stationary,h.gibbs,hs,hi,h.mirrors,h.packet,fun _ hR => h.exists_tangent hR,
    fun _ hR _ _ hv => h.isotropic hR hv,fun _ hR O _ hx _ _ hk hl => h.raw_angular hR O hx hk hl⟩

#print axioms exists_symmetric_state
#print axioms exists_symmetric_nearest_with_rotational_two_point

end IsingScaling.Rotor.PressureSelection.PhysicalStateSymmetries
