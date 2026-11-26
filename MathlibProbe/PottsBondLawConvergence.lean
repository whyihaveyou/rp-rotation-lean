import MathlibProbe.PottsBondPathLimit
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Order.MonotoneConvergence

/-! Probabilities that a specified finite set of bonds is open determine
a law on the lattice bond field. If these probabilities increase with
volume, compactness and uniqueness of subsequential limits give weak
convergence along the entire exhaustion. -/

noncomputable section

open Filter MeasurableSpace MeasureTheory Set
open scoped Classical Topology

namespace IsingScaling.Potts.FreeBond

def allOpen (F : Finset Bond) : Set Field := {ω | ∀ e ∈ F, ω e = true}

theorem allOpen_isClopen (F : Finset Bond) : IsClopen (allOpen F) := by
  have h : allOpen F = ⋂ e ∈ F, (fun ω : Field => ω e) ⁻¹' {true} := by
    ext ω
    simp [allOpen]
  rw [h]
  exact isClopen_biInter_finset fun e _ =>
    (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply e)

theorem allOpen_union (F G : Finset Bond) : allOpen (F ∪ G) = allOpen F ∩ allOpen G := by
  ext ω
  simp only [allOpen, mem_ofPred_eq, Finset.mem_union, mem_inter_iff]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun ⟨hF, hG⟩ e he => he.elim (hF e) (hG e)⟩

private theorem allOpen_piSystem : IsPiSystem (range allOpen) := by
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
  exact ⟨F ∪ G, allOpen_union F G⟩

/-- The one-bond cylinders generate every coordinate projection, and
finite intersections of these cylinders give exactly the all-open events. -/
theorem measurableSpace_eq_generateFrom_allOpen :
    (inferInstance : MeasurableSpace Field) = generateFrom (range allOpen) := by
  apply le_antisymm
  · change (⨆ e : Bond, MeasurableSpace.comap (fun ω : Field => ω e) inferInstance) ≤ _
    refine iSup_le fun e => ?_
    have he : (fun ω : Field => ω e) ⁻¹' {true} = allOpen {e} := by
      ext ω
      simp [allOpen]
    have hm : MeasurableSet[generateFrom (range allOpen)] ((fun ω : Field => ω e) ⁻¹' {true}) := by
      rw [he]
      exact measurableSet_generateFrom ⟨{e}, rfl⟩
    exact (measurable_to_bool hm).comap_le
  · apply generateFrom_le
    rintro _ ⟨F, rfl⟩
    exact (allOpen_isClopen F).isOpen.measurableSet

theorem probability_ext_allOpen {μ ν : ProbabilityMeasure Field}
    (h : ∀ F, μ (allOpen F) = ν (allOpen F)) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite _ measurableSpace_eq_generateFrom_allOpen allOpen_piSystem
  · rintro _ ⟨F, rfl⟩
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun r : NNReal => (r : ENNReal)) (h F)
  · simp

/-- Each all-open cylinder probability converges to its supremum. Every
weak subsequential limit agrees on these clopen generators, and compactness
then gives convergence of the entire sequence of laws. -/
theorem exists_weak_limit_of_allOpen_mono (P : ℕ → ProbabilityMeasure Field)
    (hP : ∀ F, Monotone (fun L => P L (allOpen F))) :
    ∃ μ : ProbabilityMeasure Field, Tendsto P atTop (𝓝 μ) := by
  have hlim (F : Finset Bond) :
      Tendsto (fun L => P L (allOpen F)) atTop (𝓝 (⨆ L, P L (allOpen F))) := by
    apply tendsto_atTop_ciSup (hP F)
    refine ⟨1, ?_⟩
    rintro _ ⟨L, rfl⟩
    exact (P L).apply_le_one _
  have hread {k : ℕ → ℕ} {μ : ProbabilityMeasure Field} (hk : Tendsto k atTop atTop)
      (hμ : Tendsto (P ∘ k) atTop (𝓝 μ)) (F : Finset Bond) :
      μ (allOpen F) = ⨆ L, P L (allOpen F) :=
    tendsto_nhds_unique
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (allOpen_isClopen F))
      ((hlim F).comp hk)
  obtain ⟨μ, k, hk, hμ⟩ := CompactSpace.tendsto_subseq P
  refine ⟨μ, Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)⟩
  obtain ⟨ν, m, hm, hν⟩ := CompactSpace.tendsto_subseq (P ∘ ns)
  have heq : ν = μ := probability_ext_allOpen fun F =>
    (hread (hns.comp hm.tendsto_atTop) hν F).trans (hread hk.tendsto_atTop hμ F).symm
  exact ⟨m, heq ▸ hν⟩

#print axioms probability_ext_allOpen
#print axioms exists_weak_limit_of_allOpen_mono

end IsingScaling.Potts.FreeBond
