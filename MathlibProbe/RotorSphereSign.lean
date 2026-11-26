import MathlibProbe.RotorPhysicalSiteReflection

/-!
For a measurable set on the unit sphere its polar area is the dimension
times the volume swept out by radii strictly between zero and one.
The cone over an orthogonal preimage is the orthogonal preimage of the
cone. Euclidean volume is invariant under every linear isometry, so the
normalized polar area is invariant as well. Choosing the diagonal map
that changes just coordinate j gives the sign rule for each spin and,
by linearity, for any finite weighted sum of spins.
-/
noncomputable section
open MeasureTheory Finset Set
open scoped BigOperators ENNReal Pointwise
namespace IsingScaling.Rotor.SiteReflection.SphereSign

abbrev Ambient (N : ℕ) := EuclideanSpace ℝ (Fin N)
variable {N : ℕ}

/-- The measured unit-sphere action of an orthogonal change of spin coordinates. -/
def sphereMap (O : Ambient N ≃ₗᵢ[ℝ] Ambient N) : Rotor.Spin N ≃ᵐ Rotor.Spin N :=
  (O.toHomeomorph.subtype
    (p := fun x => x ∈ Metric.sphere (0 : Ambient N) 1)
    (q := fun x => x ∈ Metric.sphere (0 : Ambient N) 1) (fun x => by
      change x ∈ Metric.sphere 0 1 ↔ O x ∈ Metric.sphere 0 1
      simp [Metric.mem_sphere])).toMeasurableEquiv

@[simp] theorem sphereMap_val (O : Ambient N ≃ₗᵢ[ℝ] Ambient N) (s : Rotor.Spin N) :
    (sphereMap O s).val = O s.val := rfl

private def sector (s : Set (Rotor.Spin N)) : Set (Ambient N) :=
  Ioo (0 : ℝ) 1 • (Subtype.val '' s)

private theorem sector_preimage (O : Ambient N ≃ₗᵢ[ℝ] Ambient N) (s : Set (Rotor.Spin N)) :
    sector (sphereMap O ⁻¹' s) = O ⁻¹' sector s := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨r, hr, O u.val, ⟨sphereMap O u, hu, rfl⟩, ?_⟩
    exact (O.map_smul r u.val).symm
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, hru⟩
    refine ⟨r, hr, O.symm u.val, ⟨(sphereMap O).symm u, ?_, rfl⟩, ?_⟩
    · change sphereMap O ((sphereMap O).symm u) ∈ s
      simpa using hu
    · apply O.injective
      simpa only [map_smul, O.apply_symm_apply] using hru

/-- The normalized area measure defined from Lebesgue polar coordinates
has the native orthogonal symmetry in every dimension. -/
theorem sphereMap_preserving (O : Ambient N ≃ₗᵢ[ℝ] Ambient N) :
    MeasurePreserving (sphereMap O) (surfacePrior N) (surfacePrior N) := by
  let m := (volume : Measure (Ambient N)).toSphere
  have hpre (s : Set (Rotor.Spin N)) (hs : MeasurableSet s) :
      m (sphereMap O ⁻¹' s) = m s := by
    dsimp only [m]
    rw [Measure.toSphere_apply' _ ((sphereMap O).measurable hs), Measure.toSphere_apply' _ hs]
    change _ * volume (sector (sphereMap O ⁻¹' s)) = _ * volume (sector s)
    rw [sector_preimage]
    exact congrArg (_ * ·)
      (O.measurePreserving.measure_preimage_emb O.toHomeomorph.measurableEmbedding (sector s))
  refine ⟨(sphereMap O).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereMap O).measurable hs]
  change (m univ)⁻¹ * m (sphereMap O ⁻¹' s) = (m univ)⁻¹ * m s
  rw [hpre s hs]

private def ambientFlip (j : Fin N) : Ambient N ≃ₗᵢ[ℝ] Ambient N :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun k : Fin N =>
    if k = j then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else .refl ℝ ℝ)

/-- The involution changing the sign of the specified spin component. -/
def flipCoord (j : Fin N) : Rotor.Spin N ≃ᵐ Rotor.Spin N :=
  sphereMap (ambientFlip j)

theorem flipCoord_apply (j k : Fin N) (s : Rotor.Spin N) :
    (flipCoord j s).val k = if k = j then -s.val k else s.val k := by
  change ((if k = j then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else .refl ℝ ℝ) (s.val k)) = _
  by_cases hk : k = j <;> simp [hk]

theorem flipCoord_preserving (j : Fin N) :
    MeasurePreserving (flipCoord j) (surfacePrior N) (surfacePrior N) :=
  sphereMap_preserving (ambientFlip j)

/-- Simultaneously reflect all spins in a weighted sum. -/
theorem flipCoord_weighted_sum {V : Type*} (B : Finset V) (w : V → ℝ)
    (σ : V → Rotor.Spin N) (j k : Fin N) :
    (∑ v ∈ B, w v * (flipCoord j (σ v)).val k) =
      if k = j then -(∑ v ∈ B, w v * (σ v).val k) else ∑ v ∈ B, w v * (σ v).val k := by
  by_cases h : k = j <;> simp [flipCoord_apply, h, Finset.sum_neg_distrib]

#print axioms sphereMap_preserving
#print axioms flipCoord_apply
#print axioms flipCoord_preserving
#print axioms flipCoord_weighted_sum
end IsingScaling.Rotor.SiteReflection.SphereSign
