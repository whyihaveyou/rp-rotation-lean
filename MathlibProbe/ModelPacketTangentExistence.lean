import MathlibProbe.ModelPacketLatticeCompactness
import MathlibProbe.IsingTangentExistence

/-! Start from any sequence of diverging radii. Passing to a tail ensures
positive mesh sizes. The microscopic oscillation estimate produces a common
off-origin spatial profile, and tightness of the mass in the closed unit
ball retains its possible contact at zero. Taking a further subsequence
therefore gives a nonzero locally finite measure. The lattice packet and
angular proof applies to this very measure, including its contact mass.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology CompactlySupported
namespace IsingScaling.ModelPackets
open IsingRotation Packet SpatialEnvelope

theorem exists_rotational_tangent_of_localOscillation {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ}
    (src : NormalizedPacketSource g R delay) (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1)
    (hpos : StationaryPositive g) {C : ℝ} {D r₀ : ℕ}
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀)
    (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space) (f : Space → ℝ),
      StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧ OffOriginLimit g (R ∘ u) f ∧
      (∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (R (u n)))
        atTop (𝓝 (∫ x, φ x ∂μ))) ∧
      ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  have hsym (z : Site) : g (-z) = g z := src.cubic (Equiv.refl _) (fun _ => true) z
  have h0 : 0 < g 0 := by
    by_contra! h
    have hz (z : Site) : g z = 0 := le_antisymm ((le_origin_of_stationary hsym hpos z).trans h) (hn z)
    have H := src.cube_pos 0
    simp only [susceptibility,hz,Finset.sum_const_zero,lt_self_iff_false] at H
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hR.eventually_ge_atTop 1)
  let v (n : ℕ) := N+n
  have hv : StrictMono v := fun _ _ h => Nat.add_lt_add_left h _
  have hRv := hR.comp hv.tendsto_atTop
  obtain ⟨u,f,hu,hs⟩ := exists_spatial_limit_of_localOscillation hn hb h0 hsym hpos hC hD hosc hRv
  have hRu : Tendsto (R ∘ v ∘ u) atTop atTop := hRv.comp hu.tendsto_atTop
  obtain ⟨w,μ,hw,hm,hlim⟩ := hs.extract_vague hn hRu
    (fun n => hN _ (Nat.le_add_right N (u n))) (fun n => src.cube_pos _)
  let σ := (v ∘ u) ∘ w
  have hσ : StrictMono σ := (hv.comp hu).comp hw
  have hRσ := hR.comp hσ.tendsto_atTop
  let src' : NormalizedPacketSource g (R ∘ σ) delay :=
    ⟨src.moments,src.cubic,fun j => src.cube_pos (σ j)⟩
  have hs' : OffOriginLimit g (R ∘ σ) f := hs.subseq hRu hw
  letI : IsLocallyFiniteMeasure μ := hm
  exact ⟨σ,μ,f,hσ,hm,twoPointMeasure_vague_ne_zero hn src'.cube_pos hRσ hlim,hs',hlim,
    fun O => rotation_of_spatial_limit src' hn hRσ hlim hs' O⟩

#print axioms exists_rotational_tangent_of_localOscillation
end IsingScaling.ModelPackets
