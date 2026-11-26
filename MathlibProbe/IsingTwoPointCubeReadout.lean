import MathlibProbe.IsingGibbsPositivity
import MathlibProbe.IsingFreePairLimit

/-! The mass assigned to a closed continuum cube by the untruncated
two-point measure at a positive lattice scale. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace IsingScaling

/-- The closed cube with integer half-side in rescaled Euclidean coordinates. -/
def observationCube (s : ℕ) : Set Space :=
  ⋂ i : Fin 3, (fun x : Space => x i) ⁻¹' Set.Icc (-(s:ℝ)) (s:ℝ)

private theorem observationCube_measurable (s : ℕ) : MeasurableSet (observationCube s) := by
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ i)).measurableSet

private theorem scaledSite_mem_observationCube (s : ℕ) {r : ℕ} (hr : 0 < r) (k : Site) :
    scaledSite r k ∈ observationCube s ↔ k ∈ cube (s*r) := by
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  simp only [observationCube, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc,
    cube, Fintype.mem_piFinset, Finset.mem_Icc, scaledSite]
  constructor
  · intro h i
    obtain ⟨hl, hu⟩ := h i
    change -(s:ℝ) ≤ (k i:ℝ)/(r:ℝ) at hl
    change (k i:ℝ)/(r:ℝ) ≤ (s:ℝ) at hu
    rw [le_div_iff₀ hr', neg_mul] at hl
    rw [div_le_iff₀ hr'] at hu
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩
  · intro h i
    obtain ⟨hl, hu⟩ := h i
    change -(s:ℝ) ≤ (k i:ℝ)/(r:ℝ) ∧ (k i:ℝ)/(r:ℝ) ≤ (s:ℝ)
    rw [le_div_iff₀ hr', div_le_iff₀ hr', neg_mul]
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

/-- The untruncated original measure reads the exact ratio on a closed cube,
using the same nonnegative lattice pair in its numerator and denominator. -/
theorem twoPointMeasure_observationCube_mass {g : Site → ℝ} (hg : ∀ k, 0 ≤ g k)
    {r : ℕ} (hr : 0 < r) (s : ℕ) :
    twoPointMeasure g r (observationCube s) =
      ENNReal.ofReal (susceptibility g (s*r) / susceptibility g r) := by
  classical
  have hχ : 0 ≤ susceptibility g r := Finset.sum_nonneg (fun k _ => hg k)
  let S := observationCube s
  let a (k : Site) := ENNReal.ofReal (g k / susceptibility g r)
  have hS : MeasurableSet S := observationCube_measurable s
  have he : twoPointMeasure g r S =
      ∑' k : Site, a k * (Measure.dirac (scaledSite r k)) S := by
    rw [twoPointMeasure, Measure.sum_apply _ hS]
    rfl
  change twoPointMeasure g r S = _
  rw [he, tsum_eq_sum (s := cube (s*r)) (fun k hk => ?_)]
  · have hm (k : Site) (hk : k ∈ cube (s*r)) :
        a k * (Measure.dirac (scaledSite r k)) S = a k := by
      have hx : scaledSite r k ∈ S := (scaledSite_mem_observationCube s hr k).2 hk
      simp [hx]
    rw [Finset.sum_congr rfl hm]
    unfold a
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg (hg k) hχ),
      ← Finset.sum_div]
    rfl
  · have hx : scaledSite r k ∉ S := fun hx => hk ((scaledSite_mem_observationCube s hr k).1 hx)
    simp [hx]

/-- Specialization to the actual thermodynamic Ising pair. -/
theorem thermodynamicTwoPoint_observationCube_mass {β : ℝ} (hβ : 0 ≤ β)
    {r : ℕ} (hr : 0 < r) (s : ℕ) :
    twoPointMeasure (thermodynamicTwoPoint β) r (observationCube s) =
      ENNReal.ofReal (susceptibility (thermodynamicTwoPoint β) (s*r) /
        susceptibility (thermodynamicTwoPoint β) r) :=
  twoPointMeasure_observationCube_mass
    ((thermodynamicTwoPoint_isLimit hβ).positive_cube_mass hβ).1 hr s

#print axioms thermodynamicTwoPoint_observationCube_mass

end IsingScaling
