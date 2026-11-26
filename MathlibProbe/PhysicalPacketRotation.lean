import MathlibProbe.ModulatedPacketLocalization
import MathlibProbe.ThreeDimensionalPacketFourier
import MathlibProbe.IsingPacketFrames

/-! From the original compact test packets in two physical lattice directions
to rotation of the tangent measure and its off-origin density. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Real FourierTransform SchwartzMap Topology ContDiff
namespace IsingRotation

theorem spectralSlice_modulated (φ : 𝓢(ℝ,ℂ)) (C : Space3 → ℝ)
    (α v t z : ℝ) (n : ℕ) :
    spectralSlice (horizontalFrame α) C (modulatedPacket φ (n+1) t)
      (modulatedPacket φ (n+1) z) v =
    (packetAverage (packetPlaneLaw φ) C α v t z n : ℂ) := by
  rw [← packetAverage_modulated]
  unfold spectralSlice
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  simp only [horizontalFrame_inv, transverseIntensity, Complex.ofReal_mul, mul_assoc]

end IsingRotation
namespace IsingScaling
open IsingRotation

def HasPhysicalPacketProfiles (C : Space → ℝ) : Prop :=
  ∀ (d : Bool) (φ ψ : ℝ → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∃ m : FiniteMeasure Stieltjes.Parameter,
    ∀ (ξ : ℝ) (hξ : ξ ≠ 0), spectralSlice (horizontalFrame (Packet.frameAngle d)) C φ ψ ξ =
      (Stieltjes.profile m ⟨ξ^2,sq_pos_of_ne_zero hξ⟩ : ℂ)

theorem directionalProfiles_of_packet_profiles_and_base {C : Space → ℝ}
    (hbase : ∀ i : ℤ, ∃ d : Bool, ∀ v u z, C (planeFrequency ((i:ℝ)*(π/4)) v u z) =
      C (planeFrequency (Packet.frameAngle d) v u z))
    (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hP : HasPhysicalPacketProfiles C) :
    HasDirectionalProfiles C := by
  intro z _ i w
  obtain ⟨d, hdir⟩ := hbase i
  obtain ⟨φ, hφ, hunit⟩ := exists_unit_compact_packet
  let r := Real.exp w
  have hr : 0 < r := Real.exp_pos _
  let α := Packet.frameAngle d
  let F (x : Stieltjes.Frequency) := C (planeFrequency α (Real.sqrt (x:ℝ)) r z)
  have hreg (n : ℕ) (k : ℝ) := modulatedPacket_regular φ (φ.smooth ⊤) hφ
    (d := (n:ℝ)+1) (by positivity) k
  choose m hm using fun n : ℕ => hP d (modulatedPacket φ (n+1) r) (modulatedPacket φ (n+1) z)
    (hreg n r).1 (hreg n r).2 (hreg n z).1 (hreg n z).2
  have htF (x : Stieltjes.Frequency) :
      Tendsto (fun n => Stieltjes.profile (m n) x) atTop (𝓝 (F x)) := by
    have ha (n : ℕ) : Stieltjes.profile (m n) x =
        packetAverage (packetPlaneLaw φ) C α (Real.sqrt (x:ℝ)) r z n := by
      have he := hm n (Real.sqrt (x:ℝ)) (Real.sqrt_pos.mpr x.2).ne'
      rw [spectralSlice_modulated] at he
      have he' := congrArg Complex.re he.symm
      simpa only [Complex.ofReal_re,Real.sq_sqrt x.2.le] using he'
    simp_rw [ha]
    have := packetPlaneLaw_probability φ hunit
    exact packetAverage_tendsto _ C hc hB α _ r z (Real.sqrt_pos.mpr x.2)
  obtain ⟨M, hM⟩ := (htF ⟨1, by norm_num⟩).bddAbove_range
  obtain ⟨ν, _, hν⟩ := Stieltjes.exists_profile_of_tendsto m M.toNNReal
    (fun n => (hM (Set.mem_range_self n)).trans (Real.le_coe_toNNReal _)) F htF
  obtain ⟨ν', hν'⟩ := Stieltjes.exists_profile_rescaled ν (r^2) (sq_pos_of_pos hr)
  refine ⟨ν', fun x => ?_⟩
  rw [hν',hν]
  change C (planeFrequency α (Real.sqrt (r^2*(x:ℝ))) r z) = _
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le, ← hdir]
  unfold planeFrequency transverseValue
  change C (xyz _ _ _) = C (xyz (r * _) (r * _) _)
  congr 2 <;> ring

theorem directionalProfiles_of_physical_packet_profiles {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    {C : Space → ℝ} (hF : HasTwoPointFourierDensity μ C)
    (hL : LocallyIntegrable C volume) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hP : HasPhysicalPacketProfiles C) :
    HasDirectionalProfiles C :=
  directionalProfiles_of_packet_profiles_and_base (Packet.tangent_frequency_base ht hF hL hc)
    hc hB hP

theorem tangent_rotation_of_physical_packet_profiles {β : ℝ} {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] (ht : IsTwoPointTangent β μ)
    {C : Space → ℝ} (hF : HasTwoPointFourierDensity μ C)
    (hL : LocallyIntegrable C volume) (hc : ContinuousOn C {0}ᶜ)
    (hB : BoundedAwayFromOrigin C) (hP : HasPhysicalPacketProfiles C) :
    ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧
      ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ (f : Space → ℝ≥0∞), Measurable f →
        ContinuousOn f {0}ᶜ → μ = c • Measure.dirac 0 + volume.withDensity f →
        ∀ x : Space, x ≠ 0 → f (O x) = f x := by
  intro O
  have h := tangent_rotation_of_directionalProfiles ht hF hL hc hB.on_spectator
    (directionalProfiles_of_physical_packet_profiles ht hF hL hc hB hP) O
  exact ⟨h, fun c hc' f hf hfc hd => spatialDensity_invariant_of_map_eq μ c hc' f hf hfc hd O h⟩

end IsingScaling
