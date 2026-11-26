import MathlibProbe.PacketHausdorff
import MathlibProbe.PositiveTimeLaplace
import MathlibProbe.NormalPacketFourier

/-! From the reflected Gibbs two-point form to a continuum time packet.
Time is in units of R two-layer steps, with the physical direction kept
in gridPacket. Packet coefficients and support may vary with the scale.
Only positive-time convergence is required. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology NNReal Real
namespace IsingScaling.Packet
open IsingRotation IsingRotation.Laplace

def gridPacket {ι : Type} [Fintype ι] (diagonal : Bool) (g : Site → ℝ) (c : ι → ℝ)
    (x y : ι → ℤ) (n : ℕ) : ℝ :=
  if diagonal then
    evenPacket c (fun m i j => g ![x i-x j+(m:ℤ), x i-x j-(m:ℤ), y i-y j]) n
  else evenPacket c (fun m i j => g ![(m:ℤ), x i-x j, y i-y j]) n

/-- A packet translated inward by a fixed number of two-layer steps.
The positive measure represents all moments of this one delayed packet. -/
def HasDelayedGridPacketMoments (g : Site → ℝ) (delay : ℕ) : Prop :=
  ∀ (d : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ),
    ∃ ν : FiniteMeasure UnitInterval, ∀ k,
      (∫ v, (v:ℝ)^k ∂(ν : Measure UnitInterval)) = gridPacket d g c x y (k+delay)

/-- Undelayed two-layer moment identities, including time zero. -/
abbrev HasGridPacketMoments (g : Site → ℝ) : Prop := HasDelayedGridPacketMoments g 0

theorem gridPacketMoments_of_freePair {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x-y))) : HasGridPacketMoments g := by
  intro d ι _ c x y
  cases d
  · exact axis_evenPacket_spectrum hg c x y
  · exact diagonal_evenPacket_spectrum hg c x y

private def meshEigenvalue (R : ℕ) (v : UnitInterval) : Eigenvalue :=
  ⟨(⟨v.val, v.2.1⟩ : ℝ≥0)^R, bot_le, pow_le_one₀ bot_le
    (show (⟨v.val, v.2.1⟩ : ℝ≥0) ≤ 1 from v.2.2)⟩

private theorem continuous_meshEigenvalue (R : ℕ) : Continuous (meshEigenvalue R) := by
  apply Continuous.subtype_mk
  apply Continuous.pow
  exact continuous_subtype_val.subtype_mk _

theorem scaled_packet_laplace_of_moments {g : Site → ℝ} {delay : ℕ}
    (hmom : HasDelayedGridPacketMoments g delay) (diagonal : Bool)
    (ι : ℕ → Type) [∀ n, Fintype (ι n)] (c : ∀ n, ι n → ℝ)
    (x y : ∀ n, ι n → ℤ) (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (H : ℝ → ℝ) (hc : ContinuousOn H (Ioi 0))
    (hl : ∀ t : ℝ, 0 < t → Tendsto
      (fun n => gridPacket diagonal g (c n) (x n) (y n) (⌊t*R n⌋₊+delay)) atTop (𝓝 (H t))) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = H t := by
  have hν (n : ℕ) : ∃ ν : FiniteMeasure UnitInterval, ∀ k,
      (∫ v, (v:ℝ)^k ∂(ν:Measure UnitInterval)) = gridPacket diagonal g (c n) (x n) (y n) (k+delay) :=
    hmom diagonal (c n) (x n) (y n)
  choose ν hm using hν
  let μ (n : ℕ) := (ν n).map (meshEigenvalue (R n))
  obtain ⟨ρ, hρ⟩ := exists_laplace_measure_of_rounded_moment_limits μ R hR H hc (by
    intro t ht
    apply (hl t ht).congr'
    filter_upwards [hR.eventually (eventually_ge_atTop 1)] with n hn
    rw [← hm]
    let k := ⌊t*(R n : ℝ)⌋₊
    let s := (k:ℝ)/(R n:ℝ)
    have hcont : Continuous (fun v : Eigenvalue => ((v.val^s : ℝ≥0):ℝ)) :=
      NNReal.continuous_coe.comp ((NNReal.continuous_rpow_const
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).comp continuous_subtype_val)
    change _ = ∫ v : Eigenvalue, ((v.val^s : ℝ≥0):ℝ)
                  ∂((ν n : Measure UnitInterval).map (meshEigenvalue (R n)))
    rw [integral_map (continuous_meshEigenvalue _).aemeasurable hcont.aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro v
    have hpos : (0 : ℝ) < R n := by exact_mod_cast (show 0 < R n by omega)
    have hs : (R n : ℝ) * s = k := by dsimp [s]; field_simp
    let b : ℝ≥0 := ⟨v.val,v.2.1⟩
    change (v:ℝ)^k = ((((b^(R n) : ℝ≥0)^s : ℝ≥0) : ℝ))
    rw [← NNReal.rpow_natCast_mul, hs, NNReal.rpow_natCast, NNReal.coe_pow]
    rfl)
  exact ⟨ρ, fun t ht => hρ ⟨t,ht⟩⟩

theorem scaled_packet_laplace {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x-y))) (diagonal : Bool)
    (ι : ℕ → Type) [∀ n, Fintype (ι n)] (c : ∀ n, ι n → ℝ)
    (x y : ∀ n, ι n → ℤ) (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (H : ℝ → ℝ) (hc : ContinuousOn H (Ioi 0))
    (hl : ∀ t : ℝ, 0 < t → Tendsto
      (fun n => gridPacket diagonal g (c n) (x n) (y n) ⌊t*R n⌋₊) atTop (𝓝 (H t))) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = H t :=
  scaled_packet_laplace_of_moments (gridPacketMoments_of_freePair hg) diagonal ι c x y R hR H hc hl

/-- A continuous positive-time limit of actual stationary lattice packets,
locally integrable through time zero, has a Stieltjes Fourier profile for
every nonzero normal frequency. No limiting spectral measure is an input. -/
theorem scaled_packet_frequency_profile {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x-y))) (diagonal : Bool)
    (ι : ℕ → Type) [∀ n, Fintype (ι n)] (c : ∀ n, ι n → ℝ)
    (x y : ∀ n, ι n → ℤ) (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (H : ℝ → ℝ) (hc : ContinuousOn H (Ioi 0)) (hi : IntegrableOn H (Ioc 0 1))
    (hl : ∀ t : ℝ, 0 < t → Tendsto
      (fun n => gridPacket diagonal g (c n) (x n) (y n) ⌊t*R n⌋₊) atTop (𝓝 (H t)))
    (contact : ℝ≥0) : ∃ ν : FiniteMeasure Stieltjes.Parameter,
      ∀ ξ : ℝ, ∀ hξ : ξ ≠ 0, Tendsto (fun ε : ℝ =>
        ((contact:ℝ):ℂ) + ∫ t : ℝ, PacketFourier.mode ε (2*π*ξ) t * (H |t| : ℂ))
        (𝓝[>] (0:ℝ)) (𝓝 ((Stieltjes.profile ν ⟨ξ^2, sq_pos_of_ne_zero hξ⟩ : ℝ):ℂ)) := by
  obtain ⟨ρ, hρ⟩ := scaled_packet_laplace hg diagonal ι c x y R hR H hc hl
  obtain ⟨ν,hν⟩ := PacketFourier.exists_profile_abel_cycles
    (PacketFourier.integrable_weight_of_time_correlation H hi hρ) contact
  have hae : ∀ᵐ t : ℝ, PacketFourier.packet ρ t = (H |t| : ℂ) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    unfold PacketFourier.packet
    rw [integral_complex_ofReal, ← (hρ |t| (abs_pos.mpr ht)).2]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun E => by simp only [neg_mul, mul_comm (E:ℝ) |t|])
  refine ⟨ν, fun ξ hξ => (hν ξ hξ).congr' (Eventually.of_forall fun ε => ?_)⟩
  congr 1
  apply integral_congr_ae
  filter_upwards [hae] with t ht
  rw [ht]

end IsingScaling.Packet
