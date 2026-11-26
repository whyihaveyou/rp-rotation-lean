import MathlibProbe.IsingTwoPointSpatialAssembly
import MathlibProbe.IsingAnnularFourierBounds

/-! Orthogonal invariance of every locally finite, cube-susceptibility
normalized two-point tangent of the nearest-neighbour ferromagnetic
Ising model on the simple cubic lattice, with free boundary and zero field. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace IsingScaling
open IsingRotation Packet

/-- AS-7 for the thermodynamic limit of the actual finite-box spin sums.
The scale sequence and the off-origin profile are extracted from the
tangent itself. This includes both orientations of each orthogonal axis. -/
theorem IsTwoPointTangent.rotation_invariant {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β)
    (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ := by
  obtain ⟨g,R,f,hg,hR,_,hsp,hf,hL,hB,hn,hμ⟩ := ht.exists_spatial_profile hβ
  obtain ⟨A,hs⟩ := OffOriginLimit.exists_volume_shell_bounds hg hβ hR hf hsp
  exact (gibbs_rotation_of_volume_annuli ht hβ hg hR hsp hf hL hB hn hμ hs O).1

/-- Every such tangent has a nonnegative real density continuous away
from zero, invariant pointwise there, plus its actual atom at zero. -/
theorem IsTwoPointTangent.exists_rotation_invariant_density {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β) :
    ∃ f : Space → ℝ, (∀ x, 0 ≤ f x) ∧ ContinuousOn f {0}ᶜ ∧
      LocallyIntegrable f ∧
      μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∀ (O : Space ≃ₗᵢ[ℝ] Space) (x : Space), x ≠ 0 → f (O x) = f x := by
  obtain ⟨_,_,f,_,_,_,_,hf,hL,_,hn,hμ⟩ := ht.exists_spatial_profile hβ
  refine ⟨f,hn,hf,hL,hμ,fun O x hx => (ENNReal.ofReal_eq_ofReal_iff (hn _) (hn _)).1 ?_⟩
  exact spatialDensity_invariant_of_map_eq μ (μ {0}) measure_singleton_lt_top.ne _
    (measurable_of_continuousOn_compl_singleton 0 hf).ennreal_ofReal
    (ENNReal.continuous_ofReal.comp_continuousOn hf) hμ O (ht.rotation_invariant hβ O) x hx

#print axioms IsTwoPointTangent.rotation_invariant
#print axioms IsTwoPointTangent.exists_rotation_invariant_density

/-- The off-origin density of every tangent is radial. The orthogonal map
used here is the reflection in the hyperplane perpendicular to x-y. -/
theorem IsTwoPointTangent.exists_radial_density {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ) (hβ : 0 ≤ β) :
    ∃ f : Space → ℝ, (∀ x, 0 ≤ f x) ∧ ContinuousOn f {0}ᶜ ∧
      LocallyIntegrable f ∧
      μ = μ {0} • Measure.dirac 0 + volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∀ x y : Space, x ≠ 0 → y ≠ 0 → ‖x‖ = ‖y‖ → f x = f y := by
  obtain ⟨f,hf0,hfc,hfi,hdecomp,hinv⟩ := ht.exists_rotation_invariant_density hβ
  refine ⟨f,hf0,hfc,hfi,hdecomp,?_⟩
  intro x y hx hy hxy
  let O : Space ≃ₗᵢ[ℝ] Space :=
    (Submodule.span ℝ ({x-y} : Set Space))ᗮ.reflection
  have hOx : O x = y := by
    exact Submodule.reflection_sub hxy
  have hfx : f (O x) = f x := hinv O x hx
  have hfyx : f y = f x := by
    simpa only [hOx] using hfx
  exact hfyx.symm

#print axioms IsTwoPointTangent.exists_radial_density

end IsingScaling
