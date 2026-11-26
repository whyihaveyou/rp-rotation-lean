import MathlibProbe.TransversePacketLocalization
import MathlibProbe.TwoPointSpectralRotation

/-! Two-point rotation from the real packet identity AS-8. The physical
spectral premise is stated for integrated normal sections of the Fourier
density. Packet localization and rescaling the normal energy are proved here. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Real Topology
namespace IsingRotation

/-- AS-8 at all positive normal frequencies for each member of a
localizing packet family. The measures can have unbounded total mass.
The normalization of the packet shape (e.g. its squared Fourier amplitude)
is made explicit. -/
def HasTransversePacketSpectrum (C : Space3 → ℝ) : Prop :=
  ∀ (z : ℝ), z ≠ 0 → ∀ (i : ℤ) (w : ℝ),
    ∃ (κ : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure κ)
      (ρ : ℕ → Measure ℝ≥0) (c : ℕ → ℝ≥0),
        (∀ n, (∫⁻ E, (Stieltjes.energyWeight E : ℝ≥0∞) ∂ρ n) < ⊤) ∧
        ∀ n (x : Stieltjes.Frequency),
          packetAverage κ C ((i:ℝ)*(π/4)) (Real.sqrt (x:ℝ)) (Real.exp w) z n =
            (c n:ℝ) + ∫ E : ℝ≥0, 2*(E:ℝ)/((x:ℝ)+(E:ℝ)^2) ∂ρ n

theorem directionalProfiles_of_packetSpectrum (C : Space3 → ℝ)
    (hc : ContinuousOn C {0}ᶜ) (hB : BoundedAwayFromOrigin C)
    (hp : HasTransversePacketSpectrum C) : HasDirectionalProfiles C := by
  intro z hz i w
  obtain ⟨κ, hκ, ρ, c, hρ, he⟩ := hp z hz i w
  let _ := hκ
  let α := (i:ℝ)*(π/4)
  let r := Real.exp w
  have hr : 0 < r := Real.exp_pos _
  let F (x : Stieltjes.Frequency) := C (planeFrequency α (Real.sqrt (x:ℝ)) r z)
  have ht (x : Stieltjes.Frequency) : Tendsto
      (fun n => (c n:ℝ) + ∫ E : ℝ≥0, 2*(E:ℝ)/((x:ℝ)+(E:ℝ)^2) ∂ρ n)
      atTop (𝓝 (F x)) := by
    simp_rw [← he]
    exact packetAverage_tendsto κ C hc hB α _ r z (Real.sqrt_pos.mpr x.2)
  obtain ⟨m, hm, _⟩ := Stieltjes.packet_limit_has_stieltjes_extension ρ c hρ F ht
  obtain ⟨m', hm'⟩ := Stieltjes.exists_profile_rescaled m (r^2) (sq_pos_of_pos hr)
  refine ⟨m', fun x => ?_⟩
  rw [hm', hm]
  change C (planeFrequency α (Real.sqrt (r^2*(x:ℝ))) r z) = _
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  unfold planeFrequency transverseValue
  change C (xyz _ _ _) = C (xyz (r * _) (r * _) _)
  congr 2 <;> dsimp only [α] <;> ring

theorem BoundedAwayFromOrigin.on_spectator {C : Space3 → ℝ} (hB : BoundedAwayFromOrigin C)
    (z : ℝ) (hz : z ≠ 0) : ∃ B : ℝ, ∀ x y, ‖C (xyz x y z)‖ ≤ B := by
  obtain ⟨B, hB'⟩ := hB |z| (abs_pos.mpr hz)
  exact ⟨B, fun x y => hB' _ (PiLp.norm_apply_le (p := 2) (xyz x y z) (2:Fin 3))⟩

end IsingRotation
namespace IsingScaling
open IsingRotation

/-- AS-7 with the remaining Fourier and physical packet inputs displayed.
Both conclusions allow contact at zero. -/
theorem tangent_rotation_of_packetSpectrum {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    {C : Space → ℝ} (hF : HasTwoPointFourierDensity μ C)
    (hL : LocallyIntegrable C volume) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hp : HasTransversePacketSpectrum C) :
    ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧
      ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ (f : Space → ℝ≥0∞), Measurable f →
        ContinuousOn f {0}ᶜ → μ = c • Measure.dirac 0 + volume.withDensity f →
        ∀ x : Space, x ≠ 0 → f (O x) = f x := by
  intro O
  have h := tangent_rotation_of_directionalProfiles ht hF hL hc hB.on_spectator
    (directionalProfiles_of_packetSpectrum C hc hB hp) O
  exact ⟨h, fun c hc' f hf hfc hd => spatialDensity_invariant_of_map_eq μ c hc' f hf hfc hd O h⟩

end IsingScaling
