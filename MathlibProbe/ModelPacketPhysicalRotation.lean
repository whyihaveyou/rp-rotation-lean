import MathlibProbe.RotorPacketParitySmoothing
import MathlibProbe.ModelPacketSmoothedOscillation
import MathlibProbe.ModelPacketSmoothingTangent
import MathlibProbe.ModelPacketTangentExistence
import MathlibProbe.PottsCanonicalSpatialRotation
import MathlibProbe.RotorFreePairNonneg

/-! # Orthogonal invariance of the original two-point measures

The finite spatial mark has a delayed reflection-positive packet. Its
ordinary nearest-neighbor changes are controlled by even-step differences
of the original function. The site forms give these differences, and the
stationary covariance bound gives the sharp susceptibility normalization.
Returning to the point mark preserves the vague limit on the entire original
sequence. Its density is the spatial profile of the smoothed mark.
-/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology CompactlySupported ENNReal

namespace IsingScaling.ModelPackets
open Packet SpatialEnvelope IsingRotation
open Packet.ParitySmoothing

/-- The test of convergence uses the original kernel and sharp cube. -/
abbrev VaguePairLimit (g : Site → ℝ) (R : ℕ → ℕ) (μ : Measure Space) : Prop :=
  ∀ φ : C_c(Space, ℝ), Tendsto (fun j => ∫ x, φ x ∂twoPointMeasure g (R j))
    atTop (𝓝 (∫ x, φ x ∂μ))

/-- Orthogonal invariance and the spatial description of a two-point measure,
with the actual point mass retained at the spatial origin. -/
structure IsotropicPairMeasure (μ : Measure Space) : Prop where
  nonzero : μ ≠ 0
  map_eq : ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ
  radial_density : ∃ f : Space → ℝ, (∀ x, 0 ≤ f x) ∧ ContinuousOn f {0}ᶜ ∧ LocallyIntegrable f ∧
    μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ∀ x y : Space, x ≠ 0 → y ≠ 0 → ‖x‖ = ‖y‖ → f x = f y

private theorem normalForms {g : Site → ℝ}
    (hr : ∀ d, SiteReflectedPositive g (tip d) (reflection d)) (d : PacketNormal) :
    SiteReflectedPositive g (NormalDifference.tip d) (NormalDifference.refl d) := by
  cases d with
  | axis =>
    have hh : NormalDifference.refl .axis = reflection false := by
      ext z i
      fin_cases i <;> rfl
    rw [hh]
    intro ι _ x hx c
    exact hr false x hx c
  | faceDiagonal =>
    have hh : NormalDifference.refl .faceDiagonal = reflection true := by
      ext z i
      fin_cases i <;> rfl
    rw [hh]
    intro ι _ x hx c
    exact hr true x hx c

private theorem smoothOsc {g : Site → ℝ} (hb : ∀ z, |g z| ≤ 1) (hn : ∀ z, 0 ≤ g z)
    (hc : CubicKernel g) (hr : ∀ d, SiteReflectedPositive g (tip d) (reflection d)) :
    LocalOscillation (smooth g) 3072 16 40 :=
  localOscillation_of_site_forms hb hn hc (normalForms hr)

private theorem sameVague {g : Site → ℝ} (hb : ∀ z, |g z| ≤ 1) (hn : ∀ z, 0 ≤ g z)
    (h0 : 0 < g 0) (hc : CubicKernel g) (hg : StationaryPositive g)
    (hr : ∀ d, SiteReflectedPositive g (tip d) (reflection d))
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} :
    VaguePairLimit (smooth g) R μ ↔ VaguePairLimit g R μ := by
  have heven (z : Site) : smooth g (-z) = smooth g z := smooth_cubic hc (Equiv.refl _) (fun _ => true) z
  have henv := pointwise_envelope_of_stationary (smooth_nonneg hn)
    (smooth_le_one (fun z => (le_abs_self _).trans (hb z))) heven (smooth_stationary_positive hg)
    (by norm_num : 0 ≤ (3072:ℝ)) (by norm_num : 2 ≤ (16:ℕ)) (smoothOsc hb hn hc hr)
  exact vague_smooth_iff hn h0 henv hR

theorem isotropic_of_site_forms {g : Site → ℝ} (hb : ∀ z, |g z| ≤ 1)
    (hn : ∀ z, 0 ≤ g z) (h0 : 0 < g 0) (hc : CubicKernel g) (hg : StationaryPositive g)
    (hr : ∀ d, SiteReflectedPositive g (tip d) (reflection d))
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit g R μ) : IsotropicPairMeasure μ := by
  have hs := (sameVague hb hn h0 hc hg hr hR).2 hv
  have src := ParitySmoothing.normalizedPacketSource hb hn h0 hc hr R
  have hpos := smooth_nonneg hn
  obtain ⟨u,f,hu,hsp,rot⟩ := rotation_of_localOscillation src hpos
    (smooth_le_one fun z => (le_abs_self _).trans (hb z)) (smooth_stationary_positive hg)
    (by norm_num : 0 ≤ (3072:ℝ)) (by norm_num : 2 ≤ (16:ℕ)) (smoothOsc hb hn hc hr) hR hs
  have H := hR.comp hu.tendsto_atTop
  let F (z : Space) := max (f z) 0
  have hF (z : Space) (hz : z ≠ 0) : F z = f z := by
    apply max_eq_left
    apply ge_of_tendsto' (hsp z hz _ (gridIndex_scaled_tendsto (v:=fun _ => z) H tendsto_const_nhds))
    exact fun j => mul_nonneg (div_nonneg (by positivity) (src.cube_pos (u j)).le) (hpos _)
  have hspF : OffOriginLimit (smooth g) (R ∘ u) F := fun z hz k hk => hF z hz ▸ hsp z hz k hk
  have hf := hspF.continuousOn H
  refine ⟨twoPointMeasure_vague_ne_zero hpos src.cube_pos hR hs,fun O => (rot O).1,
    F,fun _ => le_max_right _ _,hf,offOrigin_locallyIntegrable hpos H (fun j => src.cube_pos _) hf hspF,
    tangent_eq_contact_add_density hpos H (fun j => src.cube_pos _) hspF
      (fun φ => (hs φ).comp hu.tendsto_atTop),?_⟩
  intro x y hx hy hxy
  let O : Space ≃ₗᵢ[ℝ] Space := (Submodule.span ℝ ({x-y} : Set Space))ᗮ.reflection
  have he : O x = y := Submodule.reflection_sub hxy
  rw [hF x hx,hF y hy,← he]
  exact ((rot O).2 x hx).symm

theorem exists_isotropic_of_site_forms {g : Site → ℝ} (hb : ∀ z, |g z| ≤ 1)
    (hn : ∀ z, 0 ≤ g z) (h0 : 0 < g 0) (hc : CubicKernel g) (hg : StationaryPositive g)
    (hr : ∀ d, SiteReflectedPositive g (tip d) (reflection d))
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit g (R ∘ u) μ ∧ IsotropicPairMeasure μ := by
  have src := ParitySmoothing.normalizedPacketSource hb hn h0 hc hr R
  obtain ⟨u,μ,_,hu,hfin,_,_,hv,_⟩ := exists_rotational_tangent_of_localOscillation src (smooth_nonneg hn)
    (smooth_le_one fun z => (le_abs_self _).trans (hb z)) (smooth_stationary_positive hg)
    (by norm_num : 0 ≤ (3072:ℝ)) (by norm_num : 2 ≤ (16:ℕ)) (smoothOsc hb hn hc hr) hR
  let : IsLocallyFiniteMeasure μ := hfin
  have H := hR.comp hu.tendsto_atTop
  have h := (sameVague hb hn h0 hc hg hr H).1 hv
  exact ⟨u,μ,hu,hfin,h,isotropic_of_site_forms hb hn h0 hc hg hr H h⟩
end IsingScaling.ModelPackets

namespace IsingScaling
open ModelPackets Packet
open Packet.ParitySmoothing

/-- The original free Ising theorem gives the same measure-level conclusion,
including the nonnegative continuous radial density away from the origin. -/
theorem IsTwoPointTangent.isotropicPairMeasure {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β) :
    IsotropicPairMeasure μ :=
  ⟨ht.ne_zero,ht.rotation_invariant hβ,ht.exists_radial_density hβ⟩

namespace Potts.SiteBox

private theorem canonicalSiteForms {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) (d : Bool) :
    SiteReflectedPositive (canonicalFreePair q β) (tip d) (reflection d) := by
  have h := canonicalFreePair_stationary hq hβ
  cases d <;> intro ι _ x hx c
  · exact h.axis_positive hq tendsto_id x hx c
  · exact h.diagonal_positive hq tendsto_id x hx c

/-- Every susceptibility-normalized vague tangent of the canonical free
integer Potts simplex correlation on the cubic lattice is orthogonally
invariant. Its sharp cube susceptibility is computed from that same pair. -/
theorem canonicalFreePair_isotropic {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit (canonicalFreePair q β) R μ) : IsotropicPairMeasure μ := by
  have h := canonicalFreePair_stationary hq hβ
  exact isotropic_of_site_forms (h.abs_le_one hq) (h.ferromagnetic_nonneg hq hβ)
    (by rw [h.origin hq]; norm_num) h.signedPerm_invariant (h.stationaryPositive hq tendsto_id)
    (canonicalSiteForms hq hβ) hR hv

theorem canonicalFreePair_exists_isotropic_tangent {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (canonicalFreePair q β) (R ∘ u) μ ∧ IsotropicPairMeasure μ := by
  have h := canonicalFreePair_stationary hq hβ
  exact exists_isotropic_of_site_forms (h.abs_le_one hq) (h.ferromagnetic_nonneg hq hβ)
    (by rw [h.origin hq]; norm_num) h.signedPerm_invariant (h.stationaryPositive hq tendsto_id)
    (canonicalSiteForms hq hβ) hR
end Potts.SiteBox

namespace Rotor
private theorem surfaceSiteForms {N : ℕ} [NeZero N] {β : ℝ} {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g)
    (hRadii : Tendsto radii atTop atTop) (d : Bool) : SiteReflectedPositive g (tip d) (reflection d) := by
  have hid : signedPerm (Equiv.refl (Fin 3)) (fun _ : Fin 3 => false) = Equiv.refl Site := by
    ext z i
    rfl
  obtain ⟨ha,hd⟩ := h.reflected_reindexed hRadii (Equiv.refl _) (fun _ => false)
  cases d <;> intro ι _ x hx c
  · simpa only [hid,Equiv.refl_symm,Equiv.refl_apply,ParitySmoothing.reflection] using ha x hx c
  · simpa only [hid,Equiv.refl_symm,Equiv.refl_apply,ParitySmoothing.reflection] using hd x hx c

/-- For each nonzero integer N and each common stationary free-cube
thermodynamic pair limit with the sphere surface prior, every spatial
susceptibility-normalized tangent of the original dot correlation is
orthogonally invariant. -/
theorem IsStationaryFreeCubePairLimit.surface_isotropic {N : ℕ} [NeZero N] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g) (hβ : 0 ≤ β)
    (hRadii : Tendsto radii atTop atTop) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {μ : Measure Space} [IsLocallyFiniteMeasure μ] (hv : VaguePairLimit g R μ) :
    IsotropicPairMeasure μ :=
  isotropic_of_site_forms h.abs_le_one (h.surface_nonneg hβ) (by rw [h.origin]; norm_num)
    h.cubic (h.stationaryPositive hRadii) (surfaceSiteForms h hRadii) hR hv

theorem IsStationaryFreeCubePairLimit.surface_exists_isotropic_tangent {N : ℕ} [NeZero N] {β : ℝ}
    {radii : ℕ → ℕ} {g : Site → ℝ}
    (h : IsStationaryFreeCubePairLimit (SiteReflection.surfacePrior N) β radii g) (hβ : 0 ≤ β)
    (hRadii : Tendsto radii atTop atTop) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit g (R ∘ u) μ ∧ IsotropicPairMeasure μ :=
  exists_isotropic_of_site_forms h.abs_le_one (h.surface_nonneg hβ) (by rw [h.origin]; norm_num)
    h.cubic (h.stationaryPositive hRadii) (surfaceSiteForms h hRadii) hR

end Rotor
#print axioms ModelPackets.isotropic_of_site_forms
#print axioms ModelPackets.exists_isotropic_of_site_forms
#print axioms IsTwoPointTangent.isotropicPairMeasure
#print axioms Potts.SiteBox.canonicalFreePair_isotropic
#print axioms Potts.SiteBox.canonicalFreePair_exists_isotropic_tangent
#print axioms Rotor.IsStationaryFreeCubePairLimit.surface_isotropic
#print axioms Rotor.IsStationaryFreeCubePairLimit.surface_exists_isotropic_tangent
end IsingScaling
