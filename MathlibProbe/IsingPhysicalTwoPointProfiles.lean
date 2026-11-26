import MathlibProbe.IsingPhysicalCoordinateBounds
import MathlibProbe.IsingLatticePathCompactness
import MathlibProbe.IsingTangentContact

/-! Spatial profiles of the actual Gibbs two-point function. The lattice
site in the limit may follow an arbitrary sequence converging to a
nonzero macroscopic displacement. For an already specified vague tangent
the auxiliary subsequence still realizes that very measure. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported NNReal ENNReal
namespace IsingScaling.Packet
open IsingRotation

/-- Compactness on all annuli along a common subsequence of any sequence
of diverging lattice scales. The microscopic estimates come from the
actual free Ising correlation. -/
theorem exists_offOriginLimit {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ OffOriginLimit g (R ∘ u) f :=
  extract_of_coordinate_bounds hR (physical_coordinate_values hg hβ hR)
    (physical_coordinate_bounds hg hβ hR)

end IsingScaling.Packet

namespace IsingScaling
open IsingRotation Packet

/-- A given locally finite two-point tangent and its same realizing
sequence, refined to a subsequence carrying a continuous spatial
profile off the origin. The arbitrary value of this density at zero is
chosen to be zero, while the contact mass is retained separately. -/
theorem IsTwoPointTangent.exists_spatial_profile {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0≤β) :
    ∃ (g : Site → ℝ) (R : ℕ → ℕ) (f : Space → ℝ),
      IsFreeTwoPoint β g ∧ Tendsto R atTop atTop ∧
      (∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (R n))
        atTop (𝓝 (∫ x, φ x ∂μ))) ∧
      OffOriginLimit g R f ∧ ContinuousOn f {0}ᶜ ∧ LocallyIntegrable f ∧
      BoundedAwayFromOrigin f ∧ (∀ x, 0 ≤ f x) ∧
      μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun v => ENNReal.ofReal (f v)) := by
  obtain ⟨g,R,hg,hn,hχ,hR,hm⟩ := ht.realizes
  obtain ⟨u,f₀,hu,hf₀⟩ := exists_offOriginLimit hg hβ hR
  let f (v : Space) := if v = 0 then 0 else f₀ v
  have hR' := hR.comp hu.tendsto_atTop
  have hsp : OffOriginLimit g (R ∘ u) f := by
    intro x hx k hk
    simpa only [f,hx,ite_false] using hf₀ x hx k hk
  have hm' (φ : C_c(Space,ℝ)) := (hm φ).comp hu.tendsto_atTop
  have hfc := hsp.continuousOn hR'
  refine ⟨g,R ∘ u,f,hg,hR',hm',hsp,hfc,
    offOrigin_locallyIntegrable hn hR' (fun n => hχ (u n)) hfc hsp,
    hsp.boundedAwayFromOrigin_of_free hg hβ hR',?_,
    tangent_eq_contact_add_density hn hR' (fun n => hχ (u n)) hsp hm'⟩
  intro x
  by_cases hx : x = 0
  · simp [f,hx]
  · exact hsp.nonneg_of_free hg hβ hR' x hx

#print axioms IsTwoPointTangent.exists_spatial_profile

end IsingScaling
