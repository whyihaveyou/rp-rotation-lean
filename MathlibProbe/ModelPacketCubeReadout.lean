import MathlibProbe.ModelPacketPhysicalRotation
import MathlibProbe.PhysicalCubeTangent

/-! # Sharp cube normalization of the original lattice pair

A positive-radius closed cube has null boundary under a measure consisting
of a volume density and a possible atom at zero. The original grid puts its
exact susceptibility quotient on every integer such cube. Compact-set
convergence therefore reads that quotient on the same sequence, and taking
the unit cube gives exactly one. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology CompactlySupported ENNReal

namespace IsingScaling.ModelPackets

theorem IsotropicPairMeasure.susceptibility_ratio_tendsto
    {g : Site → ℝ} (hn : ∀ z, 0 ≤ g z) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hμ : IsotropicPairMeasure μ)
    (hv : VaguePairLimit g R μ) {s : ℕ} (hs : 0 < s) :
    Tendsto (fun j => susceptibility g (s * R j) / susceptibility g (R j))
      atTop (𝓝 (μ.real (observationCube s))) := by
  obtain ⟨f,_,_,_,hd,_⟩ := hμ.radial_density
  have hfront := null_frontier_closedCoordinateCube_of_density hd (show 0 < (s : ℝ) by exact_mod_cast hs)
  have hfin := (hR.eventually_ge_atTop 1).mono fun j hj =>
    Packet.finite_on_compacts_twoPointMeasure g hj
  have H := tendsto_real_compact_of_vague hfin hv (isCompact_closedCoordinateCube s) hfront
  apply H.congr'
  filter_upwards [hR.eventually_ge_atTop 1] with j hj
  change (twoPointMeasure g (R j) (observationCube s)).toReal = _
  rw [twoPointMeasure_observationCube_mass hn hj s, ENNReal.toReal_ofReal]
  exact div_nonneg (Finset.sum_nonneg (fun z _ => hn z)) (Finset.sum_nonneg (fun z _ => hn z))

theorem IsotropicPairMeasure.real_unit_cube_eq_one
    {g : Site → ℝ} (hn : ∀ z, 0 ≤ g z) (h0 : 0 < g 0)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hμ : IsotropicPairMeasure μ) (hv : VaguePairLimit g R μ) : μ.real (observationCube 1) = 1 := by
  have hχ (r : ℕ) : 0 < susceptibility g r := by
    apply lt_of_lt_of_le h0
    apply Finset.single_le_sum (f := g) (fun z _ => hn z)
    simp [cube, Fintype.mem_piFinset]
  have H := hμ.susceptibility_ratio_tendsto hn hR hv (s := 1) (by decide)
  apply tendsto_nhds_unique H
  simpa only [one_mul,div_self (hχ _).ne'] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))

end IsingScaling.ModelPackets

namespace IsingScaling
open ModelPackets

/-- Sharp normalization and all positive integer cube ratios for canonical
free Potts correlations along the original vague convergence sequence. -/
theorem Potts.SiteBox.canonicalFreePair_cube_readout {q : ℕ} (hq : 2 ≤ q)
    {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit (Potts.SiteBox.canonicalFreePair q β) R μ) :
    μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
      Tendsto (fun j => susceptibility (Potts.SiteBox.canonicalFreePair q β) (s * R j) /
        susceptibility (Potts.SiteBox.canonicalFreePair q β) (R j))
        atTop (𝓝 (μ.real (observationCube s))) := by
  have h := Potts.SiteBox.canonicalFreePair_stationary hq hβ
  have hμ := Potts.SiteBox.canonicalFreePair_isotropic hq hβ hR hv
  have hn := h.ferromagnetic_nonneg hq hβ
  exact ⟨hμ.real_unit_cube_eq_one hn (by rw [h.origin hq]; norm_num) hR hv,
    fun _ hs => hμ.susceptibility_ratio_tendsto hn hR hv hs⟩

/-- Sharp normalization and all positive integer cube ratios for the same
stationary thermodynamic sphere-spin pair as in its rotation theorem. -/
theorem Rotor.IsStationaryFreeCubePairLimit.surface_cube_readout {N : ℕ} [NeZero N] {β : ℝ}
    {sizes : ℕ → ℕ} {g : Site → ℝ}
    (h : Rotor.IsStationaryFreeCubePairLimit (Rotor.SiteReflection.surfacePrior N) β sizes g)
    (hβ : 0 ≤ β) (hsizes : Tendsto sizes atTop atTop)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit g R μ) :
    μ.real (observationCube 1) = 1 ∧ ∀ s : ℕ, 0 < s →
      Tendsto (fun j => susceptibility g (s * R j) / susceptibility g (R j))
        atTop (𝓝 (μ.real (observationCube s))) := by
  have hμ := h.surface_isotropic hβ hsizes hR hv
  have hn := h.surface_nonneg hβ
  exact ⟨hμ.real_unit_cube_eq_one hn (by rw [h.origin]; norm_num) hR hv,
    fun _ hs => hμ.susceptibility_ratio_tendsto hn hR hv hs⟩

#print axioms ModelPackets.IsotropicPairMeasure.susceptibility_ratio_tendsto
#print axioms ModelPackets.IsotropicPairMeasure.real_unit_cube_eq_one
#print axioms Potts.SiteBox.canonicalFreePair_cube_readout
#print axioms Rotor.IsStationaryFreeCubePairLimit.surface_cube_readout
end IsingScaling
