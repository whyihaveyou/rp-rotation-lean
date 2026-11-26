import MathlibProbe.TwoPointAngularRotation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Fourier factorization of normal and transverse test functions in a
common orthonormal frame. This test identity assumes no symmetry of the
measure or its Fourier density. -/
open MeasureTheory Set
open scoped FourierTransform Real RealInnerProductSpace SchwartzMap ContDiff NNReal ENNReal
noncomputable section
namespace IsingRotation

def tensorTest (u : Fin 3 → ℝ → ℂ) (x : Space3) : ℂ := ∏ i, u i (x i)

theorem integral_tensorTest (u : Fin 3 → ℝ → ℂ) :
    ∫ x : Space3, tensorTest u x = ∏ i, ∫ t : ℝ, u i t := by
  calc _ = ∫ x : Fin 3 → ℝ, ∏ i, u i (x i) :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp' _
    _ = _ := integral_fin_nat_prod_volume_eq_prod u

/-- All Fourier frequencies here are in cycles per unit, as in mathlib. -/
theorem fourier_tensorTest (u : Fin 3 → ℝ → ℂ) (p : Space3) :
    𝓕 (tensorTest u) p = ∏ i, 𝓕 (u i) (p i) := by
  let k (i : Fin 3) (t : ℝ) := Complex.exp (((-2*π*(t*p i) : ℝ):ℂ)*Complex.I) * u i t
  have hp (x : Space3) : inner ℝ x p = ∑ i, x i*p i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]
  rw [Real.fourier_eq']
  calc _ = ∫ x : Space3, tensorTest k x := by
          apply integral_congr_ae
          apply ae_of_all
          intro x
          change Complex.exp _ * (∏ i, u i (x i)) = ∏ i, k i (x i)
          simp only [k, Finset.prod_mul_distrib]
          congr 1
          rw [hp, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      _ = _ := by
        rw [integral_tensorTest]
        apply Finset.prod_congr rfl
        intro i _
        rw [Real.fourier_eq']
        simp [k, mul_comm]

private theorem projection_derivative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : E →L[ℝ] F) (hP : ‖P‖ ≤ 1)
    (f : 𝓢(F, ℂ)) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n ((f : F → ℂ) ∘ P) x‖ ≤ ‖iteratedFDeriv ℝ n f (P x)‖ := by
  rw [P.iteratedFDeriv_comp_right (f.smooth n) x (le_refl _)]
  apply ((iteratedFDeriv ℝ n f (P x)).norm_compContinuousLinearMap_le _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hP)

/-- External products remain Schwartz even when the normal-time factor
is the (noncompact) Fourier transform of a compact frequency test. -/
def externalSchwartz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (u : 𝓢(E, ℂ)) (v : 𝓢(F, ℂ)) :
    𝓢(E × F, ℂ) where
  toFun x := u x.1 * v x.2
  smooth' := (u.smooth'.comp contDiff_fst).mul (v.smooth'.comp contDiff_snd)
  decay' k n := by
    let P := ContinuousLinearMap.fst ℝ E F
    let Q := ContinuousLinearMap.snd ℝ E F
    let U (k m : ℕ) := SchwartzMap.seminorm ℝ k m u
    let V (k m : ℕ) := SchwartzMap.seminorm ℝ k m v
    refine ⟨∑ m ∈ Finset.range (n+1), (n.choose m : ℝ) *
      (U k m * V 0 (n-m) + U 0 m * V k (n-m)), ?_⟩
    intro x
    have hmul := norm_iteratedFDeriv_mul_le (u.smooth'.comp P.contDiff)
      (v.smooth'.comp Q.contDiff) x (n := n) (by simp)
    apply (mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ ‖x‖^k)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    let a := ‖iteratedFDeriv ℝ m u x.1‖
    let b := ‖iteratedFDeriv ℝ (n-m) v x.2‖
    have ha := projection_derivative P (ContinuousLinearMap.norm_fst_le ..) u m x
    have hb := projection_derivative Q (ContinuousLinearMap.norm_snd_le ..) v (n-m) x
    have hab : ‖x‖^k * (a*b) ≤ U k m * V 0 (n-m) + U 0 m * V k (n-m) := by
      change max ‖x.1‖ ‖x.2‖ ^ k * (a*b) ≤ _
      rcases le_total ‖x.1‖ ‖x.2‖ with h | h
      · rw [max_eq_right h, mul_left_comm]
        exact (mul_le_mul (u.norm_iteratedFDeriv_le_seminorm ℝ m _)
          (v.le_seminorm ℝ k (n-m) _) (by positivity) (by positivity)).trans
            (le_add_of_nonneg_left (by positivity))
      · rw [max_eq_left h, ← mul_assoc]
        exact (mul_le_mul (u.le_seminorm ℝ k m _)
          (v.norm_iteratedFDeriv_le_seminorm ℝ (n-m) _) (by positivity) (by positivity)).trans
            (le_add_of_nonneg_right (by positivity))
    calc
      _ ≤ ‖x‖^k * ((n.choose m : ℝ)*a*b) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left ha (by positivity)) hb (by positivity)
          (by dsimp [a]; positivity)
      _ = (n.choose m : ℝ)*(‖x‖^k*(a*b)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)

private def splitCoordinates : Space3 ≃L[ℝ] ℝ × ℝ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x 0, x 1, x 2)
      invFun := fun x => xyz x.1 x.2.1 x.2.2
      left_inv := by intro x; ext i; fin_cases i <;> rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }

private def splitVolume : Space3 ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow))

private theorem splitVolume_preserves : MeasurePreserving splitVolume := by
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans ?_
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans ?_
  exact MeasurePreserving.prod (MeasurePreserving.id _) (volume_preserving_finTwoArrow ℝ)

theorem integral_normal_transverse (O : Space3 ≃ₗᵢ[ℝ] Space3) (F : ℝ → ℝ × ℝ → ℂ)
    (hi : Integrable (Function.uncurry F)) :
    (∫ p : Space3, F ((O p) 0) ((O p) 1, (O p) 2)) = ∫ t, ∫ k, F t k := by
  let e := O.toHomeomorph.toMeasurableEquiv.trans splitVolume
  have hp : MeasurePreserving e := splitVolume_preserves.comp O.measurePreserving
  exact (hp.integral_comp' (Function.uncurry F)).trans (integral_prod _ hi)

theorem integrable_normal_transverse_iff (O : Space3 ≃ₗᵢ[ℝ] Space3) (F : ℝ → ℝ × ℝ → ℂ) :
    Integrable (fun p : Space3 => F ((O p) 0) ((O p) 1,(O p) 2)) ↔
      Integrable (Function.uncurry F) := by
  let e := O.toHomeomorph.toMeasurableEquiv.trans splitVolume
  have hp : MeasurePreserving e := splitVolume_preserves.comp O.measurePreserving
  exact hp.integrable_comp_emb (g := Function.uncurry F) e.measurableEmbedding

def schwartzTensor (u : Fin 3 → 𝓢(ℝ,ℂ)) : 𝓢(Space3,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ splitCoordinates
    (externalSchwartz (u 0) (externalSchwartz (u 1) (u 2)))

theorem schwartzTensor_apply (u : Fin 3 → 𝓢(ℝ,ℂ)) (x : Space3) :
    schwartzTensor u x = tensorTest (fun i => u i) x := by
  change u 0 (x 0) * (u 1 (x 1) * u 2 (x 2)) = _
  simp [tensorTest, Fin.prod_univ_three, mul_assoc]

/-- Integrate a three-dimensional two-point measure against three
Schwartz tests in a rotated frame and read the result against its
Fourier density. A spatial contact remains in the left-hand integral. -/
theorem twoPoint_tensor_test {μ : Measure Space3} {C : Space3 → ℝ}
    (hF : HasTwoPointFourierDensity μ C) (O : Space3 ≃ₗᵢ[ℝ] Space3)
    (u : Fin 3 → 𝓢(ℝ,ℂ)) :
    (∫ x, tensorTest (fun i => u i) (O x) ∂μ) =
      ∫ p : Space3, (C p:ℂ) * ∏ i, 𝓕 (u i : ℝ → ℂ) (-(O p) i) := by
  let ψ := schwartzTensor u
  have hψ := schwartzTensor_apply u
  let ψO := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ O.toContinuousLinearEquiv ψ
  have he := hF (𝓕⁻ ψO)
  rw [FourierTransform.fourier_fourierInv_eq] at he
  calc _ = ∫ x, ψO x ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => (hψ (O x)).symm
      _ = _ := he.trans (by
        apply integral_congr_ae
        apply ae_of_all
        intro p
        apply congrArg ((C p:ℂ) * ·)
        rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
        change 𝓕 ((ψ : Space3 → ℂ) ∘ O) (-p) = _
        rw [Real.fourier_comp_linearIsometry, show O (-p) = -(O p) from map_neg O p,
          show (ψ : Space3 → ℂ) = tensorTest (fun i => u i) from funext hψ, fourier_tensorTest]
        rfl)

open scoped ComplexConjugate Convolution

def reflectedPacket (φ : ℝ → ℂ) (r : ℝ) : ℂ := conj (φ (-r))

def packetAutocorrelation (φ : ℝ → ℂ) : ℝ → ℂ :=
  φ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] reflectedPacket φ

theorem fourier_reflectedPacket (φ : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (reflectedPacket φ) ξ = conj (𝓕 φ ξ) := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, ← integral_conj]
  conv_lhs => rw [← integral_neg_eq_self]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  norm_num [reflectedPacket, ← Complex.exp_conj, map_mul]
  rw [show (starRingEnd ℂ) (2:ℂ) = 2 by
    rw [show (2:ℂ) = 1+1 by norm_num, map_add, map_one]]
  exact Or.inl rfl

private theorem reflectedPacket_compact {φ : ℝ → ℂ} (hk : HasCompactSupport φ) :
    HasCompactSupport (reflectedPacket φ) :=
  (hk.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)

theorem fourier_packetAutocorrelation {φ : ℝ → ℂ}
    (hc : Continuous φ) (hk : HasCompactSupport φ) (ξ : ℝ) :
    𝓕 (packetAutocorrelation φ) ξ = (‖𝓕 φ ξ‖^2 : ℝ) := by
  have hr : Continuous (reflectedPacket φ) := Complex.continuous_conj.comp
    (hc.comp continuous_neg)
  rw [packetAutocorrelation, Real.fourier_mul_convolution_eq
    (hc.integrable_of_hasCompactSupport hk)
    (hr.integrable_of_hasCompactSupport (reflectedPacket_compact hk)),
    fourier_reflectedPacket, Complex.mul_conj']
  norm_cast

theorem packetAutocorrelation_regular {φ : ℝ → ℂ}
    (hs : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ) :
    ContDiff ℝ ∞ (packetAutocorrelation φ) ∧ HasCompactSupport (packetAutocorrelation φ) := by
  have hr : Continuous (reflectedPacket φ) := Complex.continuous_conj.comp
    (hs.continuous.comp continuous_neg)
  exact ⟨hk.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hs hr.locallyIntegrable,
    hk.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflectedPacket_compact hk)⟩

theorem packetAutocorrelation_zero (φ : ℝ → ℂ) :
    packetAutocorrelation φ 0 = ((∫ x, ‖φ x‖^2 : ℝ) : ℂ) := by
  change (∫ x : ℝ, φ x * conj (φ (-(0-x)))) = _
  simp only [zero_sub, neg_neg, Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal]

/-- The transverse Fourier factors are the squared amplitudes of the
original complex packets. Both frequency signs follow the inverse transform. -/
theorem twoPoint_transverse_autocorrelation {μ : Measure Space3} {C : Space3 → ℝ}
    (hF : HasTwoPointFourierDensity μ C) (O : Space3 ≃ₗᵢ[ℝ] Space3)
    (v : 𝓢(ℝ,ℂ)) (φ ψ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (kφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (kψ : HasCompactSupport ψ) :
    (∫ x, v ((O x) 0) * packetAutocorrelation φ ((O x) 1) *
        packetAutocorrelation ψ ((O x) 2) ∂μ) =
    ∫ p : Space3, (C p:ℂ) * (𝓕 (v : ℝ → ℂ) (-(O p) 0) *
      (‖𝓕 φ (-(O p) 1)‖^2 : ℝ) * (‖𝓕 ψ (-(O p) 2)‖^2 : ℝ)) := by
  obtain ⟨sφ,cφ⟩ := packetAutocorrelation_regular hφ kφ
  obtain ⟨sψ,cψ⟩ := packetAutocorrelation_regular hψ kψ
  let u : Fin 3 → 𝓢(ℝ,ℂ) := ![v, cφ.toSchwartzMap sφ, cψ.toSchwartzMap sψ]
  have h₁ : (cφ.toSchwartzMap sφ : ℝ → ℂ) = packetAutocorrelation φ := rfl
  have h₂ : (cψ.toSchwartzMap sψ : ℝ → ℂ) = packetAutocorrelation ψ := rfl
  simpa [tensorTest, Fin.prod_univ_three, u, h₁, h₂, mul_assoc,
    fourier_packetAutocorrelation hφ.continuous kφ,
    fourier_packetAutocorrelation hψ.continuous kψ] using twoPoint_tensor_test hF O u

/-- Normal-frequency testing with the full spatial contact. The residual
measure can include a locally integrable density. -/
theorem twoPoint_packet_frequency_test {ν : Measure Space3} {C : Space3 → ℝ}
    (c : ℝ≥0) (hF : HasTwoPointFourierDensity ((c : ℝ≥0∞) • Measure.dirac 0 + ν) C)
    (O : Space3 ≃ₗᵢ[ℝ] Space3) (s : 𝓢(ℝ,ℂ)) (φ ψ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (kφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (kψ : HasCompactSupport ψ)
    (hi : Integrable (fun x : Space3 => (𝓕 s) ((O x) 0) *
      packetAutocorrelation φ ((O x) 1) * packetAutocorrelation ψ ((O x) 2)) ν) :
    (∫ p : Space3, (C p:ℂ) * (s ((O p) 0) *
      (‖𝓕 φ (-(O p) 1)‖^2 : ℝ) * (‖𝓕 ψ (-(O p) 2)‖^2 : ℝ))) =
    (c:ℝ) * ((∫ t : ℝ, s t) * ((∫ u, ‖φ u‖^2 : ℝ) : ℂ) * ((∫ u, ‖ψ u‖^2 : ℝ) : ℂ)) +
    ∫ x : Space3, (𝓕 s) ((O x) 0) * packetAutocorrelation φ ((O x) 1) *
       packetAutocorrelation ψ ((O x) 2) ∂ν := by
  let F (x : Space3) := (𝓕 s) ((O x) 0) * packetAutocorrelation φ ((O x) 1) *
    packetAutocorrelation ψ ((O x) 2)
  have hFF (t : ℝ) : 𝓕 ((𝓕 s : 𝓢(ℝ,ℂ)) : ℝ → ℂ) (-t) = s t := by
    rw [← Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourierInv_coe,
      FourierTransform.fourierInv_fourier_eq]
  have h0 : (𝓕 s) 0 = ∫ t : ℝ, s t := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    simp
  have he := twoPoint_transverse_autocorrelation hF O (𝓕 s) φ ψ hφ kφ hψ kψ
  simp only [hFF] at he
  rw [← he]
  change (∫ x : Space3, F x ∂((c:ℝ≥0∞) • Measure.dirac 0 + ν)) = _
  rw [integral_add_measure _ hi, integral_smul_measure, integral_dirac]
  · simp [h0, packetAutocorrelation_zero, Complex.real_smul]
  · exact (integrable_dirac (f := F) (by simp)).smul_measure (by simp)

def transverseIntensity (φ ψ : ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  ((‖𝓕 φ (-k.1)‖^2 : ℝ) : ℂ) * ((‖𝓕 ψ (-k.2)‖^2 : ℝ) : ℂ)

def spectralSlice (O : Space3 ≃ₗᵢ[ℝ] Space3) (C : Space3 → ℝ) (φ ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ k : ℝ × ℝ, (C (O.symm (xyz t k.1 k.2)) : ℂ) * transverseIntensity φ ψ k

theorem disintegrate_spectral_test (O : Space3 ≃ₗᵢ[ℝ] Space3) (C : Space3 → ℝ)
    (s φ ψ : ℝ → ℂ) (hi : Integrable (fun z : ℝ × ℝ × ℝ =>
      s z.1 * ((C (O.symm (xyz z.1 z.2.1 z.2.2)) : ℂ) * transverseIntensity φ ψ z.2))) :
    (∫ p : Space3, (C p:ℂ) * (s ((O p) 0) *
      (‖𝓕 φ (-(O p) 1)‖^2 : ℝ) * (‖𝓕 ψ (-(O p) 2)‖^2 : ℝ))) =
      ∫ t, s t * spectralSlice O C φ ψ t := by
  let F (t : ℝ) (k : ℝ × ℝ) :=
    s t * ((C (O.symm (xyz t k.1 k.2)) : ℂ) * transverseIntensity φ ψ k)
  have hx (p : Space3) : xyz (p 0) (p 1) (p 2) = p := by
    ext i; fin_cases i <;> rfl
  calc
    _ = ∫ p : Space3, F ((O p) 0) ((O p) 1, (O p) 2) := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by simp [F, transverseIntensity, hx]; ring
    _ = _ := (integral_normal_transverse O F hi).trans (by
      apply integral_congr_ae
      exact ae_of_all _ fun t => integral_const_mul _ _)

/-- Express a spatial self-correlation as an integral over pair displacements.
The Lebesgue change of variables retains the two original complex amplitudes. -/
theorem packet_displacement_integral (φ ψ : ℝ → ℂ)
    (hφ : Continuous φ) (kφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (kψ : HasCompactSupport ψ)
    (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    (∫ p : (ℝ×ℝ)×(ℝ×ℝ), (φ p.1.1 * ψ p.1.2) * conj (φ p.2.1 * ψ p.2.2) *
      F (p.1-p.2)) =
      ∫ k : ℝ × ℝ, F k * (packetAutocorrelation φ k.1 * packetAutocorrelation ψ k.2) := by
  let W (a : ℝ×ℝ) := φ a.1 * ψ a.2
  have hW : Continuous W := (hφ.comp continuous_fst).mul (hψ.comp continuous_snd)
  have kW : HasCompactSupport W := by
    apply HasCompactSupport.intro (kφ.prod kψ)
    intro a ha
    by_cases h : a.1 ∈ tsupport φ
    · have hh : a.2 ∉ tsupport ψ := fun h' => ha ⟨h,h'⟩
      simp [W, image_eq_zero_of_notMem_tsupport hh]
    · simp [W, image_eq_zero_of_notMem_tsupport h]
  let B (z : (ℝ×ℝ)×(ℝ×ℝ)) := W (z.1+z.2) * conj (W z.2) * F z.1
  have hB : Continuous B := ((hW.comp (continuous_fst.add continuous_snd)).mul
    (Complex.continuous_conj.comp (hW.comp continuous_snd))).mul (hF.comp continuous_fst)
  let T (z : (ℝ×ℝ)×(ℝ×ℝ)) := (z.1-z.2,z.2)
  have hT : MeasurePreserving T := measurePreserving_sub_prod volume volume
  have hI : Integrable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => W p.1 * conj (W p.2) * F (p.1-p.2)) := by
    apply (((hW.comp continuous_fst).mul (Complex.continuous_conj.comp
      (hW.comp continuous_snd))).mul (hF.comp (continuous_fst.sub continuous_snd))).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (kW.prod kW)
    intro p hp
    by_cases h : p.1 ∈ tsupport W
    · have hh : p.2 ∉ tsupport W := fun h' => hp ⟨h,h'⟩
      simp [image_eq_zero_of_notMem_tsupport hh]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have hIB : Integrable B := (hT.integrable_comp hB.aestronglyMeasurable).mp (by
    simpa [B, T, Function.comp_def] using hI)
  have he := integral_map (μ := volume) hT.measurable.aemeasurable hB.aestronglyMeasurable
  rw [hT.map_eq] at he
  calc
    _ = ∫ z, B z := by simpa [T, B, W] using he.symm
    _ = _ := (integral_prod B hIB).trans (by
      apply integral_congr_ae
      apply ae_of_all
      intro k
      change (∫ y : ℝ × ℝ, B (k,y)) = F k *
        (packetAutocorrelation φ k.1 * packetAutocorrelation ψ k.2)
      have one (g : ℝ → ℂ) (q : ℝ) :
          (∫ b, g (q+b) * conj (g b)) = packetAutocorrelation g q := by
        change _ = ∫ a, g a * conj (g (-(q-a)))
        simpa using (integral_add_left_eq_self (fun a : ℝ => g a * conj (g (a-q))) q)
      rw [← one φ k.1, ← one ψ k.2, ← integral_prod_mul, ← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro b
      simp only [B, W, Prod.fst_add, Prod.snd_add, map_mul]
      ring)

end IsingRotation
