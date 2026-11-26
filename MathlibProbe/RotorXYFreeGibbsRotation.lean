import MathlibProbe.RotorXYFourierLaw
import MathlibProbe.RotorXYCanonicalFreePair

/-! # The physical two-point function of the canonical free XY state

The weak limit on spin fields and the free-cube pair limit agree on the
bounded continuous spin dot. This identifies the actual Gibbs state's
two-point function in the spatial rotation and angular comparison theorems.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace IsingScaling.Rotor.XY
open PressureSelection PressureSelection.FreeExhaustion PressureSelection.LocalGibbs

/-- The complete nearest-neighbour planar-spin law selected by free exhaustions. -/
def canonicalFreeGibbs {β : ℝ} (hβ : 0 ≤ β) : ProbabilityMeasure (SpinField 2) :=
  (existsUnique_free_gibbs hβ).exists.choose

theorem canonicalFreeGibbs_isGibbs {β : ℝ} (hβ : 0 ≤ β) :
    IsNearestGibbs 2 β (canonicalFreeGibbs hβ) :=
  (existsUnique_free_gibbs hβ).exists.choose_spec.1

theorem tendsto_canonicalFreeGibbs {β : ℝ} (hβ : 0 ≤ β) (D : ℕ → Finset Site)
    (hD : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField 2) :
    Tendsto (fun n => freeDomainLaw 2 β (D n) (fill n)) atTop (𝓝 (canonicalFreeGibbs hβ)) :=
  (existsUnique_free_gibbs hβ).exists.choose_spec.2 D hD fill

/-- A weak cluster law of the physical free cubes realizes the canonical
pair at both arbitrary observation sites. -/
theorem freeGibbs_dot_of_cube_limit {β : ℝ} (hβ : 0 ≤ β) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    {P : ProbabilityMeasure (SpinField 2)} {u : ℕ → SpinField 2}
    (hP : Tendsto (fun n => freeDomainLaw 2 β (cube (L n)) (u n)) atTop (𝓝 P)) (x y : Site) :
    (∫ s, fieldDot 2 x y s ∂(P : Measure _)) = canonicalFreePair β (x-y) := by
  have h := (ProbabilityMeasure.continuous_integral_continuousMap (fieldDot 2 x y)).continuousAt.tendsto.comp
    hP
  have hc : Tendsto (fun n => SiteReflection.freePair (SiteReflection.surfacePrior 2) β (L n) x y) atTop
      (𝓝 (∫ s, fieldDot 2 x y s ∂(P : Measure _))) := by
    apply h.congr'
    filter_upwards [hL.eventually (BondMirror.ev_cube x), hL.eventually (BondMirror.ev_cube y)] with n hx hy
    exact (freeDomain_pair 2 β (cube (L n)) (u n) hx hy).trans (freePair_cube 2 β (L n) x y)
  exact tendsto_nhds_unique hc ((canonicalFreePair_stationary hβ x y).comp hL)

theorem canonicalFreeGibbs_dot {β : ℝ} (hβ : 0 ≤ β) (x y : Site) :
    (∫ s, fieldDot 2 x y s ∂(canonicalFreeGibbs hβ : Measure _)) = canonicalFreePair β (x-y) := by
  let u : SpinField 2 := fun _ => ⟨EuclideanSpace.single (0 : Fin 2) 1, by simp⟩
  exact freeGibbs_dot_of_cube_limit hβ (L := id) tendsto_id
    (tendsto_canonicalFreeGibbs hβ cube BondMirror.ev_cube (fun _ => u)) x y

theorem canonicalFreeGibbs_fieldPair {β : ℝ} (hβ : 0 ≤ β) :
    fieldPair (canonicalFreeGibbs hβ) = canonicalFreePair β := by
  funext z
  have hswap (s : SpinField 2) : fieldDot 2 0 z s = fieldDot 2 z 0 s := by
    change ⟪(s 0).val, (s z).val⟫_ℝ = ⟪(s z).val, (s 0).val⟫_ℝ
    exact real_inner_comm (s z).val (s 0).val
  simpa only [fieldPair, hswap, sub_zero] using canonicalFreeGibbs_dot hβ z 0

theorem canonicalFreeGibbs_isotropic {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ModelPackets.VaguePairLimit (fieldPair (canonicalFreeGibbs hβ)) R μ) :
    ModelPackets.IsotropicPairMeasure μ := by
  rw [canonicalFreeGibbs_fieldPair] at hv
  exact canonicalFreePair_isotropic hβ hR hv

theorem canonicalFreeGibbs_exists_isotropic_tangent {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      ModelPackets.VaguePairLimit (fieldPair (canonicalFreeGibbs hβ)) (R ∘ u) μ ∧
      ModelPackets.IsotropicPairMeasure μ := by
  rw [canonicalFreeGibbs_fieldPair]
  exact canonicalFreePair_exists_isotropic_tangent hβ hR

theorem canonicalFreeGibbs_raw_angular {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0)
    {k l : ℕ → Site} (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => Packet.normalization (fieldPair (canonicalFreeGibbs hβ)) (R n) *
      (fieldPair (canonicalFreeGibbs hβ) (k n) - fieldPair (canonicalFreeGibbs hβ) (l n))) atTop (𝓝 0) := by
  rw [canonicalFreeGibbs_fieldPair]
  exact canonicalFreePair_raw_angular hβ hR O hx hk hl

/-- Free finite-volume laws at inverse temperatures tending to β from below
select the same zero-field Gibbs state at arbitrary relative rates. -/
theorem tendsto_canonicalFreeGibbs_joint_fromBelow {β : ℝ} (hβ : 0 ≤ β) {γ : ℕ → ℝ}
    (hγ : ∀ n, 0 ≤ γ n) (hle : ∀ n, γ n ≤ β) (hlim : Tendsto γ atTop (𝓝 β))
    (D : ℕ → Finset Site) (hD : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) (fill : ℕ → SpinField 2) :
    Tendsto (fun n => freeDomainLaw 2 (γ n) (D n) (fill n)) atTop (𝓝 (canonicalFreeGibbs hβ)) := by
  apply tendsto_iff_integerMoments.mpr
  intro k
  have fixed := free_integerMoments_tendsto (freeChargeComparison hβ) D hD fill k
  have named := tendsto_iff_integerMoments.mp (tendsto_canonicalFreeGibbs hβ D hD fill) k
  rw [← tendsto_nhds_unique fixed named]
  exact free_integerMoments_tendsto_fromBelow hγ hle hlim D hD fill k

/-- Taking the thermodynamic limit first at each lower inverse temperature
also converges to the complete free law at the endpoint. -/
theorem tendsto_canonicalFreeGibbs_fromBelow {β : ℝ} (hβ : 0 ≤ β) {γ : ℕ → ℝ}
    (hγ : ∀ n, 0 ≤ γ n) (hle : ∀ n, γ n ≤ β) (hlim : Tendsto γ atTop (𝓝 β)) :
    Tendsto (fun n => canonicalFreeGibbs (hγ n)) atTop (𝓝 (canonicalFreeGibbs hβ)) := by
  apply tendsto_iff_integerMoments.mpr
  intro k
  let u : SpinField 2 := fun _ => ⟨EuclideanSpace.single (0 : Fin 2) 1, by simp⟩
  have cubeLimit (n : ℕ) := tendsto_iff_integerMoments.mp
    (tendsto_canonicalFreeGibbs (hγ n) cube BondMirror.ev_cube (fun _ => u)) k
  choose L hL error using fun n => ((eventually_ge_atTop n).and
    ((Metric.tendsto_nhds.mp (cubeLimit n)) (1/((n : ℝ)+1)) (by positivity))).exists
  have grows : Tendsto L atTop atTop := tendsto_atTop_mono hL tendsto_id
  have diagonal := tendsto_iff_integerMoments.mp (tendsto_canonicalFreeGibbs_joint_fromBelow
    hβ hγ hle hlim (fun n => cube (L n)) (fun x => grows.eventually (BondMirror.ev_cube x)) (fun _ => u)) k
  exact diagonal.congr_dist (squeeze_zero (fun _ => dist_nonneg)
    (fun n => (error n).le) tendsto_one_div_add_atTop_nhds_zero_nat)

#print axioms canonicalFreeGibbs_isGibbs
#print axioms tendsto_canonicalFreeGibbs
#print axioms freeGibbs_dot_of_cube_limit
#print axioms canonicalFreeGibbs_dot
#print axioms canonicalFreeGibbs_fieldPair
#print axioms canonicalFreeGibbs_isotropic
#print axioms canonicalFreeGibbs_exists_isotropic_tangent
#print axioms canonicalFreeGibbs_raw_angular
#print axioms tendsto_canonicalFreeGibbs_joint_fromBelow
#print axioms tendsto_canonicalFreeGibbs_fromBelow
end IsingScaling.Rotor.XY
