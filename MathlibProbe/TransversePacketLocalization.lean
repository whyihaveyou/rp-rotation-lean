import MathlibProbe.TwoPointAngularRotation

/-! Real transverse packet localization at positive normal frequency.
The fixed packet shape can have unbounded Fourier support. -/
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace IsingRotation

def planeFrequency (α ω t z : ℝ) : Space3 :=
  xyz (ω * Real.cos α - t * Real.sin α) (ω * Real.sin α + t * Real.cos α) z

theorem norm_planeFrequency_sq (α ω t z : ℝ) :
    ‖planeFrequency α ω t z‖^2 = ω^2 + t^2 + z^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change (ω * Real.cos α - t * Real.sin α)^2 +
    (ω * Real.sin α + t * Real.cos α)^2 + z^2 = _
  linear_combination (ω^2+t^2) * Real.sin_sq_add_cos_sq α

theorem le_norm_planeFrequency (α ω t z : ℝ) :
    ω ≤ ‖planeFrequency α ω t z‖ := by
  nlinarith [norm_nonneg (planeFrequency α ω t z), norm_planeFrequency_sq α ω t z,
    sq_nonneg t, sq_nonneg z]

def BoundedAwayFromOrigin (C : Space3 → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ p : Space3, ε ≤ ‖p‖ → ‖C p‖ ≤ B

def packetAverage (κ : Measure (ℝ × ℝ)) (C : Space3 → ℝ)
    (α ω t z : ℝ) (n : ℕ) : ℝ :=
  ∫ v, C (planeFrequency α ω (t + (1/((n:ℝ)+1))*v.1) (z + (1/((n:ℝ)+1))*v.2)) ∂κ

theorem packetAverage_tendsto (κ : Measure (ℝ × ℝ)) [IsProbabilityMeasure κ]
    (C : Space3 → ℝ) (hc : ContinuousOn C {0}ᶜ) (hB : BoundedAwayFromOrigin C)
    (α ω t z : ℝ) (hω : 0 < ω) :
    Tendsto (packetAverage κ C α ω t z) atTop (𝓝 (C (planeFrequency α ω t z))) := by
  obtain ⟨B, hB'⟩ := hB ω hω
  let f (u : ℝ × ℝ) := C (planeFrequency α ω u.1 u.2)
  have hf : Continuous f := by
    apply hc.comp_continuous (continuous_xyz
      (continuous_const.sub (continuous_fst.mul continuous_const))
      (continuous_const.add (continuous_fst.mul continuous_const)) continuous_snd)
    intro v
    exact norm_pos_iff.mp (hω.trans_le (le_norm_planeFrequency α ω v.1 v.2))
  let τ (n : ℕ) := 1/((n:ℝ)+1)
  have hτ : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hh := tendsto_integral_of_dominated_convergence (μ := κ)
    (F := fun n (v : ℝ × ℝ) => f (t+τ n*v.1, z+τ n*v.2))
    (f := fun _ => f (t,z)) (fun _ => B)
    (fun n => (hf.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun v =>
      hB' _ (le_norm_planeFrequency _ _ _ _)) (by
      apply ae_of_all
      intro v
      apply hf.continuousAt.tendsto.comp
      rw [nhds_prod_eq]
      apply Filter.Tendsto.prodMk
      · simpa using (hτ.mul_const v.1).const_add t
      · simpa using (hτ.mul_const v.2).const_add z)
  change Tendsto (fun n : ℕ => ∫ v : ℝ × ℝ, f (t + τ n*v.1, z + τ n*v.2) ∂κ)
    atTop (𝓝 (f (t,z)))
  simpa only [integral_const, probReal_univ, one_smul] using hh

end IsingRotation
