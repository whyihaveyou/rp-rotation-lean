import MathlibProbe.TwoPointAngularRotation
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

/-! Large spatial annuli of a critical two-point tangent, in mathlib's 2π
Fourier convention. The real-space shell estimates enter as L¹ bounds on
each piece and its fourth translation difference. -/
noncomputable section
open MeasureTheory FourierTransform VectorFourier Real Filter Finset Set
open scoped Real FourierTransform Topology SchwartzMap
namespace IsingRotation.FourierShell
abbrev V := Space3

theorem norm_fourier_le_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : V → E) (p : V) : ‖𝓕 f p‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- Fourth-order integration by parts along p. Lower derivatives need only
be integrable, so their potentially large L¹ norms do not enter the estimate. -/
theorem fourth_decay (f : V → ℂ) (hf : ContDiff ℝ 4 f)
    (hi : ∀ k : ℕ, k ≤ 4 → Integrable (iteratedFDeriv ℝ k f))
    (p : V) : ‖p‖^4 * ‖𝓕 f p‖ ≤ ∫ x, ‖iteratedFDeriv ℝ 4 f x‖ := by
  by_cases hp : p=0
  · simpa [hp] using (integral_nonneg (fun x : V => norm_nonneg (iteratedFDeriv ℝ 4 f x)))
  have hh := congrFun (Real.fourier_iteratedFDeriv (N:=4) hf
    (fun k hk => hi k (by exact_mod_cast hk)) (n:=4) (by norm_num)) p
  let m (_ : Fin 4) := p
  have he := ((𝓕 (iteratedFDeriv ℝ 4 f)) p).le_opNorm m
  have hb := norm_fourier_le_integral (iteratedFDeriv ℝ 4 f) p
  rw [hh] at he
  have hnorm : ‖fourierPowSMulRight (-innerSL ℝ) (𝓕 f) p 4 m‖ =
      (2*π)^4 * ((‖p‖^2)^4 * ‖𝓕 f p‖) := by
    have hv : ((innerSL ℝ) p) p = ‖p‖^2 := real_inner_self_eq_norm_sq p
    simp [fourierPowSMulRight_apply, m, abs_of_nonneg Real.pi_nonneg, hv]
  rw [hnorm, ← hh] at he
  simp only [m, prod_const, card_univ, Fintype.card_fin] at he
  have hp4 : 0 < ‖p‖^4 := pow_pos (norm_pos_iff.mpr hp) _
  have hpow : 1 ≤ (2*π)^4 := one_le_pow₀ (by linarith [Real.pi_gt_three]) 
  apply (le_of_mul_le_mul_right _ hp4 : _)
  calc (‖p‖^4 * ‖𝓕 f p‖)*‖p‖^4 = (‖p‖^2)^4 * ‖𝓕 f p‖ := by ring
    _ ≤ (2*π)^4 * ((‖p‖^2)^4 * ‖𝓕 f p‖) := le_mul_of_one_le_left (by positivity) hpow
    _ ≤ _ := he.trans (mul_le_mul_of_nonneg_right hb hp4.le)

def translateDifference (h : V) (f : V → ℂ) (x : V) : ℂ := f x - f (x+h)

theorem translateDifference_integrable (h : V) {f : V → ℂ} (hi : Integrable f)
    (k : ℕ) : Integrable ((translateDifference h)^[k] f) := by
  induction k with
  | zero => exact hi
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.sub (ih.comp_add_right h)

private def halfPeriod (p : V) : V := (1 / (2*‖p‖^2) : ℝ) • p

private theorem fourier_halfPeriod (f : V → ℂ) (hi : Integrable f) {p : V} (hp : p≠0)
    (k : ℕ) : ‖𝓕 f p‖ = (1/2:ℝ)^k * ‖𝓕 ((translateDifference (halfPeriod p))^[k] f) p‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    let F := (translateDifference (halfPeriod p))^[k] f
    have hf := translateDifference_integrable (halfPeriod p) hi k
    have hid : 𝓕 F p = (1/2:ℂ) • 𝓕 (translateDifference (halfPeriod p) F) p :=
      fourierIntegral_eq_half_sub_half_period_translate hp hf
    have hid' : ‖𝓕 F p‖ = (1/2:ℝ)*‖𝓕 (translateDifference (halfPeriod p) F) p‖ := by
      rw [hid, norm_smul]; norm_num
    rw [Function.iterate_succ_apply', pow_succ, ih, mul_assoc]
    exact congrArg ((1/2:ℝ)^k * ·) hid'

private theorem halfPeriod_norm {p : V} (hp : p≠0) : ‖halfPeriod p‖ = 1/(2*‖p‖) := by
  rw [halfPeriod, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp [norm_ne_zero_iff.mpr hp]

/-- An L¹ estimate on actual fourth translations yields Fourier decay
even when fourth classical derivatives are unavailable. -/
theorem fourth_difference_decay (f : V → ℂ) (hi : Integrable f) {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ h : V, (∫ x, ‖((translateDifference h)^[4] f) x‖) ≤ B*‖h‖^4)
    {p : V} (hp : p≠0) : ‖p‖^4 * ‖𝓕 f p‖ ≤ B := by
  have h := (norm_fourier_le_integral _ p).trans (hd (halfPeriod p))
  rw [halfPeriod_norm hp] at h
  rw [fourier_halfPeriod f hi hp 4]
  calc _ ≤ ‖p‖^4 * ((1/2:ℝ)^4 * (B*(1/(2*‖p‖))^4)) := by gcongr
       _ = B / 256 := by field_simp [norm_ne_zero_iff.mpr hp]; ring
       _ ≤ B := by linarith

structure SpatialShells (f : ℕ → V → ℂ) (A : ℝ) : Prop where
  nonneg : 0 ≤ A
  integrable (j : ℕ) : Integrable (f j)
  mass (j : ℕ) : (∫ x, ‖f j x‖) ≤ A * (4:ℝ)^j
  fourth (j : ℕ) (h : V) :
    (∫ x, ‖((translateDifference h)^[4] (f j)) x‖) ≤ (A * (1/4:ℝ)^j)*‖h‖^4

private theorem integral_norm_iterated_difference (h : V) {f : V → ℂ} (hi : Integrable f)
    (k : ℕ) : (∫ x, ‖((translateDifference h)^[k] f) x‖) ≤
      2^k * ∫ x, ‖f x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    let F := (translateDifference h)^[k] f
    have hiF : Integrable F := translateDifference_integrable h hi k
    rw [Function.iterate_succ_apply', pow_succ]
    calc
      _ ≤ ∫ x, ‖F x‖ + ‖F (x+h)‖ :=
        integral_mono (hiF.sub (hiF.comp_add_right h)).norm
          (hiF.norm.add (hiF.comp_add_right h).norm) (fun x => norm_sub_le ..)
      _ = 2 * (∫ x, ‖F x‖) := by
        rw [integral_add hiF.norm (hiF.comp_add_right h).norm,
          integral_add_right_eq_self (fun x => ‖F x‖) h]
        ring
      _ ≤ 2^k * 2 * (∫ x, ‖f x‖) := by dsimp [F]; linarith

/-- Only sub-shell-length increments need a fourth-difference estimate.
The elementary L¹ translation bound handles every longer step. -/
theorem spatialShells_of_short {f : ℕ → V → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hi : ∀ j, Integrable (f j)) (hm : ∀ j, (∫ x, ‖f j x‖) ≤ A * (4:ℝ)^j)
    (hd : ∀ j h, ‖h‖ ≤ (2:ℝ)^j →
      (∫ x, ‖((translateDifference h)^[4] (f j)) x‖) ≤ (A * (1/4:ℝ)^j)*‖h‖^4) :
    SpatialShells f (16*A) := by
  refine ⟨by positivity, hi, fun j => (hm j).trans (by gcongr; linarith), ?_⟩
  intro j h
  by_cases hsmall : ‖h‖ ≤ (2:ℝ)^j
  · apply (hd j h hsmall).trans
    gcongr; linarith
  · have hv : (2:ℝ)^j ≤ ‖h‖ := le_of_not_ge hsmall
    have hz : (4:ℝ)^j * (4:ℝ)^j = ((2:ℝ)^j)^4 := by
      calc (4:ℝ)^j * 4^j = (4*4:ℝ)^j := (mul_pow ..).symm
           _ = ((2:ℝ)^4)^j := by norm_num
           _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hpower : (4:ℝ)^j ≤ (1/4:ℝ)^j * ‖h‖^4 := by
      rw [one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity), hz]
      exact pow_le_pow_left₀ (by positivity) hv 4
    calc _ ≤ 2^4 * (∫ x, ‖f j x‖) := integral_norm_iterated_difference h (hi j) 4
         _ ≤ (16*A) * 4^j := by nlinarith [hm j]
         _ ≤ _ := by rw [mul_assoc (16*A)]; exact mul_le_mul_of_nonneg_left hpower (by positivity)

private theorem difference_outside {f : V → ℂ} {r : ℝ}
    (hs : ∀ x, r ≤ ‖x‖ → f x = 0) (h : V) (k : ℕ) :
    ∀ x, r + k*‖h‖ ≤ ‖x‖ → ((translateDifference h)^[k] f) x = 0 := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    intro x hx
    have hnorm : ‖x‖ ≤ ‖x+h‖ + ‖h‖ := by simpa using norm_sub_le (x+h) h
    push_cast at hx
    have hx' : r+k*‖h‖ ≤ ‖x‖ := by nlinarith [norm_nonneg h]
    have hxh : r+k*‖h‖ ≤ ‖x+h‖ := by nlinarith
    rw [Function.iterate_succ_apply']
    exact sub_eq_zero.mpr ((ih x hx').trans (ih (x+h) hxh).symm)

theorem norm_integral_from_ball {u : V → ℂ} {D r : ℝ} (hr : 0<r)
    (hi : Integrable u) (hs : ∀ x, r ≤ ‖x‖ → u x=0) (hm : ∀ x, ‖u x‖ ≤ D) :
    (∫ x, ‖u x‖) ≤ volume.real (Metric.ball (0:V) 1) * r^3 * D := by
  have hvol : volume.real (Metric.ball (0:V) r) = r^3 * volume.real (Metric.ball (0:V) 1) := by
    rw [measureReal_def, volume.addHaar_ball_of_pos (0:V) hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    simp [V, Space3, measureReal_def]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Metric.ball (0:V) r)
    (fun x hx => by rw [hs x (by simpa using hx), norm_zero])]
  calc _ ≤ ∫ x in Metric.ball (0:V) r, D :=
          setIntegral_mono_on hi.norm.integrableOn (integrableOn_const measure_ball_lt_top.ne)
            Metric.isOpen_ball.measurableSet (fun x _ => hm x)
       _ = _ := by rw [setIntegral_const, smul_eq_mul, hvol]; ring

/-- For dyadic annuli of spatial scale L=2^j, pointwise size O(L⁻¹)
and fourth increments O(|h|⁴L⁻⁵) at |h|≤L suffice for all shell estimates.
A ball of radius 4L covers the initial spatial support. No classical
fourth derivative of the profile is required. -/
theorem spatialShells_of_pointwise {f : ℕ → V → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ j, Integrable (f j))
    (hs : ∀ j x, 4*(2:ℝ)^j ≤ ‖x‖ → f j x = 0)
    (hm : ∀ j x, ‖f j x‖ ≤ C/(2:ℝ)^j)
    (hd : ∀ j h x, ‖h‖ ≤ (2:ℝ)^j →
      ‖((translateDifference h)^[4] (f j)) x‖ ≤ C*‖h‖^4/((2:ℝ)^j)^5) :
    ∃ A, SpatialShells f A := by
  let v : ℝ := volume.real (Metric.ball (0:V) 1)
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  refine ⟨16*(v*8^3*C), spatialShells_of_short (by positivity) hi ?_ ?_⟩
  · intro j
    let L : ℝ := 2^j
    have hL : 0 < L := by dsimp [L]; positivity
    have h4 : (4:ℝ)^j = L^2 := by
      dsimp [L]; rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have hx := norm_integral_from_ball (r:=8*L) (by positivity) (hi j)
      (fun x hx => hs j x (by change 4*L ≤ ‖x‖; linarith)) (hm j)
    calc _ ≤ v*(8*L)^3*(C/L) := hx
         _ = _ := by rw [h4]; field_simp
  · intro j h hh
    let L : ℝ := 2^j
    have hL : 0 < L := by dsimp [L]; positivity
    have h4 : (4:ℝ)^j = L^2 := by
      dsimp [L]; rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have hx := norm_integral_from_ball (r:=8*L) (by positivity)
      (translateDifference_integrable h (hi j) 4)
      (fun x hx => difference_outside (hs j) h 4 x (by change 4*L+4*‖h‖ ≤ ‖x‖; change ‖h‖ ≤ L at hh; linarith)) (fun x => hd j h x hh)
    calc _ ≤ v*(8*L)^3*(C*‖h‖^4/L^5) := hx
         _ = _ := by rw [one_div, inv_pow, h4]; field_simp

theorem SpatialShells.low {f A} (h : SpatialShells f A) (j : ℕ) (p : V) :
    ‖𝓕 (f j) p‖ ≤ A*(4:ℝ)^j := (norm_fourier_le_integral _ _).trans (h.mass j)

theorem SpatialShells.high {f A} (h : SpatialShells f A) (j : ℕ) {p : V} (hp : p ≠ 0) :
    ‖𝓕 (f j) p‖ ≤ (A/‖p‖^4)*(1/4:ℝ)^j := by
  have hx := fourth_difference_decay _ (h.integrable j)
    (mul_nonneg h.nonneg (by positivity)) (h.fourth j) hp
  have ht : 0 < ‖p‖^4 := pow_pos (norm_pos_iff.mpr hp) _
  rw [div_mul_eq_mul_div, le_div_iff₀ ht, mul_comm]
  exact hx

private lemma shell_geom : Summable (fun j : ℕ => (1/4:ℝ)^j) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

private lemma prefix_geom (k : ℕ) : ∑ j ∈ Finset.range k, (4:ℝ)^j ≤ 4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith [show (0:ℝ) ≤ 4^k by positivity]

/-- The two parts of the series are split at the individual frequency.
This is the step that improves the crude |p|⁻⁴ sum to |p|⁻². -/
private lemma dyadic_bound (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) {A u : ℝ}
    (hA : 0 ≤ A) (hu : 0 < u) (low : ∀ j, a j ≤ A*4^j)
    (high : ∀ j, a j ≤ (A*u^2)*(1/4:ℝ)^j) :
    ∑' j, a j ≤ 6*A*u := by
  obtain ⟨k,huk,hku⟩ : ∃ k : ℕ, u ≤ (4:ℝ)^k ∧ (k=0 ∨ (4:ℝ)^k ≤ 4*u) := by
    by_cases h : 1 ≤ u
    · obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near h (show (1:ℝ) < 4 by norm_num)
      refine ⟨k+1,hk'.le,Or.inr ?_⟩
      rw [pow_succ]; linarith
    · exact ⟨0,by simpa using (le_of_not_ge h), Or.inl rfl⟩
  have hs : Summable a :=
    Summable.of_nonneg_of_le ha high (shell_geom.mul_left _)
  have hlo : ∑ j ∈ Finset.range k, a j ≤ (4*A)*u := by
    rcases hku with rfl|hk
    · simp [mul_nonneg (by positivity : 0 ≤ 4*A) hu.le]
    · calc _ ≤ ∑ j ∈ Finset.range k, A*4^j := Finset.sum_le_sum fun j _ => low j
           _ ≤ A * 4^k := by rw [← Finset.mul_sum]; gcongr; exact prefix_geom k
           _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hk hA]
  have hpart (j : ℕ) : a (j+k) ≤ (A*u)*(1/4:ℝ)^j := by
    have hk : u*(1/4:ℝ)^k ≤ 1 := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]; exact huk
    calc _ ≤ (A*u^2) * ((1/4:ℝ)^j*(1/4:ℝ)^k) := by simpa only [pow_add] using high (j+k)
         _ = ((A*u)*(1/4:ℝ)^j)*(u*(1/4:ℝ)^k) := by ring
         _ ≤ _ := mul_le_of_le_one_right (by positivity) hk
  have ht : ∑' j, a (j+k) ≤ (A*u)*2 := by
    calc
      _ ≤ ∑' j : ℕ, (A*u)*(1/4:ℝ)^j :=
        ((summable_nat_add_iff k).mpr hs).tsum_le_tsum hpart (shell_geom.mul_left _)
      _ ≤ _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)]
        gcongr; norm_num
  rw [← hs.sum_add_tsum_nat_add k]
  linarith

def shellDensity (f : ℕ → V → ℂ) (p : V) : ℂ := ∑' j, 𝓕 (f j) p

theorem SpatialShells.summable_norm {f A} (h : SpatialShells f A) {p : V} (hp : p ≠ 0) :
    Summable (fun j => ‖𝓕 (f j) p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => h.high _ hp)
    (shell_geom.mul_left _)

theorem SpatialShells.absolute_density_bound {f A} (h : SpatialShells f A) {p : V} (hp : p ≠ 0) :
    ∑' j, ‖𝓕 (f j) p‖ ≤ (6*A)/‖p‖^2 := by
  rw [div_eq_mul_inv]
  apply dyadic_bound _ (fun _ => norm_nonneg _) h.nonneg (by positivity) (fun j => h.low j p)
  intro j
  convert h.high j hp using 1
  ring

theorem SpatialShells.continuousOn_density {f A} (h : SpatialShells f A) :
    ContinuousOn (shellDensity f) {0}ᶜ := by
  intro p hp
  have hp' : p ≠ 0 := hp
  let r := ‖p‖/2
  have hr : 0 < r := half_pos (norm_pos_iff.mpr hp')
  let U := {q : V | r < ‖q‖}
  have hopen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hmem : p ∈ U := by change ‖p‖/2 < ‖p‖; linarith [norm_pos_iff.mpr hp']
  have cont : ContinuousOn (shellDensity f) U := by
    refine continuousOn_tsum ?_ (shell_geom.mul_left (A/r^4)) ?_
    · intro j
      exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ (E:=V)).continuous₂ (h.integrable j)).continuousOn
    · intro j q hq
      change r < ‖q‖ at hq
      apply (h.high j (norm_pos_iff.mp (hr.trans hq))).trans
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left h.nonneg (pow_pos hr _)
        (pow_le_pow_left₀ hr.le hq.le 4)) (by positivity)
  exact (cont.continuousAt (hopen.mem_nhds hmem)).continuousWithinAt

theorem SpatialShells.density_bound {f A} (h : SpatialShells f A) {p : V} (hp : p ≠ 0) :
    ‖shellDensity f p‖ ≤ (6*A)/‖p‖^2 :=
  (norm_tsum_le_tsum_norm (h.summable_norm hp)).trans (h.absolute_density_bound hp)

/-- The |p|⁻² majorant is locally integrable in dimension three.
The value assigned to the density at the single point p=0 is immaterial. -/
theorem SpatialShells.density_locallyIntegrable {f A} (h : SpatialShells f A) :
    LocallyIntegrable (shellDensity f) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (C:=6*A) (α:=2)
    (by norm_num [V,Space3]) (by norm_num [V,Space3]) ?_ ?_
  · filter_upwards [volume.ae_ne (0:V)] with p hp
    simpa [Real.rpow_neg (norm_nonneg p), Real.rpow_two, div_eq_mul_inv]
      using h.density_bound hp
  · exact (measurable_of_continuousOn_compl_singleton 0 h.continuousOn_density).aestronglyMeasurable

theorem fourier_pair_integral {u : V → ℂ} (hu : Integrable u) (φ : 𝓢(V,ℂ)) :
    ∫ p, 𝓕 u p * φ p = ∫ x, u x * (𝓕 φ) x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L:=innerₗ V) Real.continuous_fourierChar continuous_inner hu φ.integrable)

private theorem weightedTest_integrable (A : ℝ) (hA : 0 ≤ A) (φ : 𝓢(V,ℂ)) :
    Integrable (fun p : V => (A/‖p‖^2)*‖φ p‖) := by
  let B := Metric.ball (0:V) 1
  let b (p : V) := (A/‖p‖^2)*‖φ p‖
  have hm : Measurable b := by dsimp [b]; fun_prop
  have hpos (p : V) : 0 ≤ b p := by dsimp [b]; positivity
  have hnear : IntegrableOn b B := by
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow (C:=A * SchwartzMap.seminorm ℝ 0 0 φ)
      (α:=2) (by norm_num [V,Space3]) (by norm_num [V,Space3]) _ hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    rw [Real.norm_of_nonneg (hpos p), Real.rpow_neg (norm_nonneg p), Real.rpow_two]
    calc b p ≤ (A/‖p‖^2)*(SchwartzMap.seminorm ℝ 0 0 φ) := by
           dsimp [b]; gcongr; exact SchwartzMap.norm_le_seminorm ℝ φ p
         _ = _ := by ring
  have hfar : IntegrableOn b Bᶜ := by
    apply ((φ.integrable.norm.const_mul A).integrableOn (s:=Bᶜ)).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with p hp
    have hv : 1 ≤ ‖p‖ := by simpa [B, Metric.mem_ball, dist_zero_right] using hp
    rw [Real.norm_of_nonneg (hpos p)]
    dsimp [b]
    exact mul_le_mul_of_nonneg_right (div_le_self hA (one_le_pow₀ hv)) (norm_nonneg _)
  simpa only [B, Set.union_compl_self, integrableOn_univ] using hnear.union hfar

/-- The real-space dyadic decomposition computes the Fourier density on every
Schwartz test, including tests meeting zero frequency. -/
theorem SpatialShells.tested_density {f A} (h : SpatialShells f A) (φ : 𝓢(V,ℂ)) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, ∫ x, (f j x) * (𝓕 φ) x)
      atTop (𝓝 (∫ p, shellDensity f p * φ p)) := by
  have hcont (j : ℕ) : Continuous (𝓕 (f j)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ (E:=V)).continuous₂ (h.integrable j)
  let S (N : ℕ) (p : V) := ∑ j ∈ Finset.range N, 𝓕 (f j) p * φ p
  have hS (N) : Continuous (S N) := continuous_finsetSum _ fun j _ =>
    (hcont j).mul φ.continuous
  have hconv : Tendsto (fun N => ∫ p, S N p) atTop
      (𝓝 (∫ p, shellDensity f p * φ p)) := by
    apply tendsto_integral_of_dominated_convergence (fun p : V => (6*A/‖p‖^2)*‖φ p‖)
      (fun n => (hS n).aestronglyMeasurable) (weightedTest_integrable _ (mul_nonneg (by norm_num) h.nonneg) φ)
    · intro N
      filter_upwards [volume.ae_ne (0:V)] with p hp
      have hsum := (h.summable_norm hp).sum_le_tsum (Finset.range N) (fun i _ => norm_nonneg _)
      calc ‖S N p‖ ≤ ∑ j ∈ Finset.range N, ‖𝓕 (f j) p * φ p‖ := norm_sum_le _ _
           _ = (∑ j ∈ Finset.range N, ‖𝓕 (f j) p‖)*‖φ p‖ := by simp [Finset.sum_mul]
           _ ≤ _ := mul_le_mul_of_nonneg_right (hsum.trans (h.absolute_density_bound hp)) (norm_nonneg _)
    · filter_upwards [volume.ae_ne (0:V)] with p hp
      exact (((h.summable_norm hp).of_norm.hasSum).mul_right (φ p)).tendsto_sum_nat
  convert hconv using 1
  funext N
  rw [show (∫ p, S N p) = ∑ j ∈ Finset.range N, ∫ p, 𝓕 (f j) p * φ p from
    integral_finsetSum _ (fun j _ => φ.integrable.bdd_mul (hcont j).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_fourier_le_integral (f j))))]
  exact Finset.sum_congr rfl fun j _ => (fourier_pair_integral (h.integrable j) φ).symm

theorem bounded_inner_and_contact (c : ℂ) (u : V → ℂ)
    {f A} (h : SpatialShells f A) {p : V} (hp : p ≠ 0) :
    ‖c + 𝓕 u p + shellDensity f p‖ ≤ ‖c‖ + (∫ x, ‖u x‖) + (6*A)/‖p‖^2 := by
  exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans
    (add_le_add (le_refl _) (norm_fourier_le_integral u p))) (h.density_bound hp))

/-- A spatial contact contributes the constant high-frequency limit. -/
theorem tendsto_contact (c : ℂ) (u : V → ℂ) {f A} (h : SpatialShells f A) :
    Tendsto (fun p => c + 𝓕 u p + shellDensity f p) (cocompact V) (𝓝 c) := by
  have ht : Tendsto (fun p : V => ‖p‖) (cocompact V) atTop := tendsto_norm_cocompact_atTop
  have hb : Tendsto (fun p : V => (6*A)/‖p‖^2) (cocompact V) (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((ht.inv_tendsto_atTop.pow 2).const_mul (6*A))
  have hzero : Tendsto (shellDensity f) (cocompact V) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (.of_forall fun _ => norm_nonneg _)
      ((ht.eventually_gt_atTop 0).mono fun _ hp => h.density_bound (norm_pos_iff.mp hp)) hb
  have hu : Tendsto (𝓕 u) (cocompact V) (𝓝 0) := tendsto_integral_exp_inner_smul_cocompact u
  simpa using (tendsto_const_nhds (x:=c)).add hu |>.add hzero

/-- An even real spatial density has a real Fourier transform, without an
integrability assumption besides Bochner's usual convention at undefined integrals. -/
theorem conj_fourier_real_even (u : V → ℝ) (he : ∀ x, u (-x) = u x) (p : V) :
    starRingEnd ℂ (𝓕 (fun x => (u x:ℂ)) p) = 𝓕 (fun x => (u x:ℂ)) p := by
  rw [Real.fourier_eq', ← integral_conj]
  nth_rw 2 [← integral_neg_eq_self]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [smul_eq_mul, ← Complex.exp_conj, he, map_ofNat]

/-- Assemble one Fourier test from a real, even spatial partition and
its integrable frequency sum. This also applies to a test vanishing at zero. -/
theorem fourier_test_of_even_partition (μ : Measure V) (c : ℝ) (u : V → ℝ)
    (sh : ℕ → V → ℝ) (hi : Integrable (fun x => (u x:ℂ))) (he : ∀ x, u (-x) = u x)
    (hse : ∀ j x, sh j (-x) = sh j x)
    (hμ : ∀ ψ : 𝓢(V,ℂ), Tendsto (fun N => (c:ℂ)*ψ 0 + (∫ x, (u x:ℂ)*ψ x) +
        ∑ j ∈ Finset.range N, ∫ x, (sh j x:ℂ)*ψ x)
      atTop (𝓝 (∫ x, ψ x ∂μ)))
    (φ : 𝓢(V,ℂ)) (hsint : Integrable (fun p => shellDensity (fun j x => (sh j x:ℂ)) p*φ p))
    (ht : Tendsto (fun N => ∑ j ∈ Finset.range N, ∫ x, (sh j x:ℂ)*(𝓕 φ) x) atTop
      (𝓝 (∫ p, shellDensity (fun j x => (sh j x:ℂ)) p*φ p))) :
    (∫ x, (𝓕 φ) x ∂μ) = ∫ p, ((((c:ℂ) + 𝓕 (fun x => (u x:ℂ)) p +
      shellDensity (fun j x => (sh j x:ℂ)) p).re : ℂ) * φ p) := by
  let U : V → ℂ := fun x => u x
  let f : ℕ → V → ℂ := fun j x => sh j x
  let D (p : V) := (c:ℂ) + 𝓕 U p + shellDensity f p
  change (∫ x, (𝓕 φ) x ∂μ) = ∫ p, ((D p).re:ℂ)*φ p
  have hreal (p : V) : ((D p).re:ℂ)=D p := by
    apply Complex.conj_eq_iff_re.mp
    simp only [D, shellDensity, map_add, Complex.conj_ofReal, Complex.conj_tsum,
      U, conj_fourier_real_even u he p, f, fun j => conj_fourier_real_even (sh j) (hse j) p]
  have huC : Continuous (𝓕 U) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ (E:=V)).continuous₂ hi
  have hcint : Integrable (fun p => (c:ℂ)*φ p) := φ.integrable.const_mul _
  have huint : Integrable (fun p => 𝓕 U p*φ p) := φ.integrable.bdd_mul huC.aestronglyMeasurable
    (.of_forall (norm_fourier_le_integral U))
  have h0 : (𝓕 φ) 0 = ∫ p, φ p := by
    change 𝓕 (φ : V → ℂ) 0 = _
    simp [Real.fourier_eq]
  have heq :
      (c:ℂ)*(𝓕 φ) 0 + (∫ x, U x*(𝓕 φ) x) + (∫ p, shellDensity f p*φ p) =
        ∫ p, D p*φ p := by
    simp only [D, add_mul]
    have hcu : Integrable (fun p => (c:ℂ)*φ p + 𝓕 U p*φ p) := hcint.add huint
    rw [integral_add hcu hsint, integral_add hcint huint, h0,
      integral_const_mul, fourier_pair_integral hi φ]
  have hseq : Tendsto (fun N => (c:ℂ)*(𝓕 φ) 0 + (∫ x, U x*(𝓕 φ) x) +
      ∑ j ∈ Finset.range N, ∫ x, f j x*(𝓕 φ) x) atTop
      (𝓝 ((c:ℂ)*(𝓕 φ) 0 + (∫ x, U x*(𝓕 φ) x) + ∫ p, shellDensity f p*φ p)) :=
    tendsto_const_nhds.add ht
  calc (∫ x, (𝓕 φ) x ∂μ) =
        (c:ℂ)*(𝓕 φ) 0 + (∫ x, U x*(𝓕 φ) x) + (∫ p, shellDensity f p*φ p) :=
      tendsto_nhds_unique (hμ (𝓕 φ)) hseq
    _ = ∫ p, D p*φ p := heq
    _ = _ := integral_congr_ae (.of_forall fun p => congrArg (·*φ p) (hreal p).symm)

set_option maxHeartbeats 2500000 in
/-- Spatial dyadic approximation of μ on Schwartz tests, with its contact
at zero isolated, gives the real Fourier density used by the rotation theorem. -/
theorem hasTwoPointFourierDensity_of_spatialShells
    (μ : Measure V) (c : ℝ) (u : V → ℝ) (sh : ℕ → V → ℝ) (A : ℝ)
    (hi : Integrable (fun x => (u x:ℂ))) (he : ∀ x, u (-x) = u x)
    (hs : SpatialShells (fun j x => (sh j x:ℂ)) A)
    (hse : ∀ j x, sh j (-x) = sh j x)
    (hμ : ∀ ψ : 𝓢(V,ℂ), Tendsto (fun N => (c:ℂ)*ψ 0 + (∫ x, (u x:ℂ)*ψ x) +
        ∑ j ∈ Finset.range N, ∫ x, (sh j x:ℂ)*ψ x)
      atTop (𝓝 (∫ x, ψ x ∂μ))) :
    HasTwoPointFourierDensity μ (fun p =>
      ((c:ℂ) + 𝓕 (fun x => (u x:ℂ)) p + shellDensity (fun j x => (sh j x:ℂ)) p).re) := by
  intro φ
  apply fourier_test_of_even_partition μ c u sh hi he hse hμ φ _ (hs.tested_density φ)
  apply (weightedTest_integrable (6*A) (mul_nonneg (by norm_num) hs.nonneg) φ).mono'
    ((measurable_of_continuousOn_compl_singleton 0 hs.continuousOn_density).aestronglyMeasurable.mul
      φ.continuous.aestronglyMeasurable)
  filter_upwards [volume.ae_ne (0:V)] with x hx
  change ‖shellDensity (fun j z => (sh j z:ℂ)) x * φ x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hs.density_bound hx) (norm_nonneg _)

end IsingRotation.FourierShell
