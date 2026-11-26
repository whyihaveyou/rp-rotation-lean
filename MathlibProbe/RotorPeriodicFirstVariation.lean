import MathlibProbe.RotorPeriodicPairResponse
import MathlibProbe.RotorPeriodicVM4Bridge
import MathlibProbe.RotorPeriodicFourierMeasure

/-! # First variations of the physical periodic Gibbs pressure

First let the side length tend to infinity at a fixed perturbation. Then
let the perturbation tend to zero in the directional ℓ¹ norm. The cubic
base profile stays fixed throughout, while the adapted profiles and the
subsequences of side lengths may depend on the perturbation.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace IsingScaling.Rotor.PressureSelection

private theorem weighted_summable {J f : Site → ℝ} (hJ : Summable J) (hb : ∀ z, |f z| ≤ 1) :
    Summable (fun z => J z*f z) := by
  apply hJ.abs.of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

private theorem pairing_error {A B f : Site → ℝ} (a : Summable A) (b : Summable B)
    (hb : ∀ z, |f z| ≤ 1) :
    |(∑' z, A z*f z) - ∑' z, B z*f z| ≤ ∑' z, |A z-B z| := by
  have h := (weighted_summable a hb).sub (weighted_summable b hb)
  rw [← (weighted_summable a hb).tsum_sub (weighted_summable b hb)]
  calc
    _ ≤ ∑' z, |A z*f z-B z*f z| := by
      simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm (f := fun z => A z * f z - B z * f z) (by
        simpa only [Real.norm_eq_abs] using h.abs))
    _ ≤ _ := h.abs.tsum_le_tsum (fun z => by
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb z)) (a.sub b).abs

/-- VM-5 for actual cubic and diagonal-adapted sphere-spin Gibbs pairs.
The only direction estimate is convergence of the lattice couplings in
ℓ¹; no positivity or order on the readouts is assumed. -/
theorem spectral_first_variation (N : ℕ) [NeZero N]
    (J H : Site → ℝ) (K : ℕ → Site → ℝ) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hJ : Summable (fun z => |J z|)) (hH : Summable (fun z => |H z|))
    (hK : ∀ n, Summable (fun z => |K n z|))
    (hder : Tendsto (fun n => ∑' z, |(K n z-J z)/t n-H z|) atTop (𝓝 0))
    (sides : ℕ → ℕ → ℕ) [∀ n m, NeZero (sides n m)]
    (hsize : ∀ n, Tendsto (sides n) atTop atTop)
    (μ ν : Measure Momentum) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : ℕ → Site → ℝ)
    (hcubic : ∀ n z, Tendsto (fun m => cubicPair N (sides n m) J z)
      atTop (𝓝 (spectralPair μ z)))
    (hadapt : ∀ n z, Tendsto (fun m => diagonalPair N (sides n m) (K n) z)
      atTop (𝓝 (a n z)))
    (hdir : ∀ z, Tendsto (fun n => a n z) atTop (𝓝 (spectralPair ν z))) :
    (∫ k, interactionMultiplier H hH k ∂μ) ≤ ∫ k, interactionMultiplier H hH k ∂ν := by
  let D (n : ℕ) (z : Site) := (K n z-J z)/t n
  let err (n : ℕ) := ∑' z, |D n z-H z|
  have hab (n : ℕ) (z : Site) : |a n z| ≤ 1 :=
    le_of_tendsto (hadapt n z).abs (Eventually.of_forall fun m =>
      abs_averagedDot_le_one N _ _ z)
  have hμb (z : Site) : |spectralPair μ z| ≤ 1 :=
    le_of_tendsto (hcubic 0 z).abs (Eventually.of_forall fun m =>
      abs_averagedDot_le_one N _ _ z)
  have hsD (n : ℕ) : Summable (D n) := ((hK n).of_abs.sub hJ.of_abs).div_const (t n)
  have hcmp (n : ℕ) :
      (∑' z, D n z * spectralPair μ z) ≤ ∑' z, D n z*a n z := by
    have h := compare_periodic_pairings N J (K n) hJ (hK n) (sides n) (hsize n) (hcubic n) (hadapt n)
    simp only [D, div_mul_eq_mul_div, tsum_div_const]
    exact div_le_div_of_nonneg_right h (ht n).le
  have hpoint (n : ℕ) :
      (∑' z, H z*spectralPair μ z) ≤ (∑' z, H z*a n z) + 2*err n := by
    have h1 := (abs_le.mp (pairing_error (hsD n) hH.of_abs hμb)).1
    have h2 := (abs_le.mp (pairing_error (hsD n) hH.of_abs (hab n))).2
    change -(err n) ≤ _ at h1
    change _ ≤ err n at h2
    linarith [hcmp n]
  have hsum : Tendsto (fun n => ∑' z, H z * a n z) atTop (𝓝 (∑' z, H z*spectralPair ν z)) := by
    apply tendsto_tsum_of_dominated_convergence hH (fun z => (hdir z).const_mul (H z))
    refine Eventually.of_forall fun n z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hab n z)
  have herr : Tendsto err atTop (𝓝 0) := hder
  rw [integral_interactionMultiplier, integral_interactionMultiplier]
  simpa using (le_of_tendsto_of_tendsto' tendsto_const_nhds (hsum.add (herr.const_mul 2)) hpoint)

/-- Actual spin-law provenance of a directional witness: first the side
length tends to infinity at a fixed interaction, then a subsequence of
the perturbations tends to the spin law Q. -/
def AdaptedVariationLimit (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (Q : ProbabilityMeasure (SpinField N)) : Prop :=
  ∃ v : ℕ → ℕ, StrictMono v ∧ ∃ w : ℕ → ℕ → ℕ, ∃ P : ℕ → ProbabilityMeasure (SpinField N),
    (∀ n, StrictMono (w n) ∧
      Tendsto (fun j => rootedLaw N Seam.adaptedDestination
        (Seam.adaptedSeries (sides (w n j)) (K (v n)))) atTop (𝓝 (P n))) ∧
    Tendsto P atTop (𝓝 Q)

/-- For every original cubic subsequence with a fixed limiting momentum
law, each ℓ¹ directional perturbation produces an actual adapted spin
state, its momentum law, and the ordered spectral-energy comparison. -/
theorem select_adapted_variation (N : ℕ) [NeZero N]
    (J : Site → ℝ) (hJ : Summable (fun z => |J z|))
    (sides : ℕ → ℕ) [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop)
    (μ : ProbabilityMeasure Momentum)
    (hbase : ∀ z, Tendsto (fun n => cubicPair N (sides n) J z) atTop (𝓝 (spectralPair (μ : Measure _) z)))
    (H : Site → ℝ) (K : ℕ → Site → ℝ) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hH : Summable (fun z => |H z|)) (hK : ∀ n, Summable (fun z => |K n z|))
    (hder : Tendsto (fun n => ∑' z, |(K n z-J z)/t n-H z|) atTop (𝓝 0)) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ ν : ProbabilityMeasure Momentum,
      AdaptedVariationLimit N sides K Q ∧ ShiftInvariant Q ∧
      (∀ z, spectralPair (ν : Measure Momentum) z = fieldPair Q z) ∧
      (∫ k, interactionMultiplier H hH k ∂(μ : Measure Momentum)) ≤
        ∫ k, interactionMultiplier H hH k ∂(ν : Measure Momentum) := by
  choose P σ w hw hP hspin hσ hpair using (fun n =>
    diagonal_spin_and_momentum_limit N sides (fun _ => K n))
  obtain ⟨Q,v,hv,hQ,hF⟩ := spinField_subsequence N P
  have houter (z : Site) : Tendsto (fun n => fieldPair (P (v n)) z) atTop (𝓝 (fieldPair Q z)) :=
    hF (fieldDot N 0 z)
  obtain ⟨ν,hν⟩ := HasMomentumLaw.of_pointwise_limit
    (fun n => ⟨σ (v n),hσ (v n)⟩) houter
  refine ⟨Q,ν,⟨v,hv,fun n => w (v n),P ∘ v,
    fun n => ⟨hw (v n),hspin (v n)⟩,hQ⟩,
    ShiftInvariant.of_tendsto hQ (fun n => hP (v n)),hν,?_⟩
  apply spectral_first_variation N J H (fun n => K (v n)) (fun n => t (v n))
    (fun n => ht (v n)) hJ hH (fun n => hK (v n)) (hder.comp hv.tendsto_atTop)
    (fun n j => sides (w (v n) j)) (fun n => hsides.comp (hw (v n)).tendsto_atTop)
    (μ : Measure Momentum) (ν : Measure Momentum) (fun n => fieldPair (P (v n)))
  · exact fun n z => (hbase z).comp (hw (v n)).tendsto_atTop
  · exact fun n z => hpair (v n) z
  · intro z
    rw [hν]
    exact houter z

/-- A single cubic spin state and its momentum law work for *all*
directions. Only the adapted witness is selected anew for each actual
perturbation. The hypotheses mention couplings and side lengths only. -/
theorem common_cubic_variational_state (N : ℕ) [NeZero N] (J : Site → ℝ)
    (hJ : Summable (fun z => |J z|)) (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (hsides : Tendsto sides atTop atTop) :
    ∃ P : ProbabilityMeasure (SpinField N), ∃ μ : ProbabilityMeasure Momentum, ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant P ∧
      Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides (l n)) J))
        atTop (𝓝 P) ∧ (∀ z, spectralPair (μ : Measure Momentum) z = fieldPair P z) ∧
      ∀ (H : Site → ℝ) (K : ℕ → Site → ℝ) (t : ℕ → ℝ), (∀ n, 0 < t n) →
        ∀ hH : Summable (fun z => |H z|), (∀ n, Summable (fun z => |K n z|)) →
        Tendsto (fun n => ∑' z, |(K n z-J z)/t n-H z|) atTop (𝓝 0) →
        ∃ Q : ProbabilityMeasure (SpinField N), ∃ ν : ProbabilityMeasure Momentum,
          AdaptedVariationLimit N (fun n => sides (l n)) K Q ∧ ShiftInvariant Q ∧
          (∀ z, spectralPair (ν : Measure Momentum) z = fieldPair Q z) ∧
          (∫ k, interactionMultiplier H hH k ∂(μ : Measure Momentum)) ≤
            ∫ k, interactionMultiplier H hH k ∂(ν : Measure Momentum) := by
  obtain ⟨P,μ,l,hl,hP,hspin,hμ,hpair⟩ := cubic_spin_and_momentum_limit N sides (fun _ => J)
  refine ⟨P,μ,l,hl,hP,hspin,hμ,fun H K t ht hH hK hder => ?_⟩
  apply select_adapted_variation N J hJ (fun n => sides (l n)) (hsides.comp hl.tendsto_atTop)
    μ _ H K t ht hH hK hder
  intro z
  rw [hμ]
  exact hpair z

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.spectral_first_variation
#print axioms IsingScaling.Rotor.PressureSelection.common_cubic_variational_state
