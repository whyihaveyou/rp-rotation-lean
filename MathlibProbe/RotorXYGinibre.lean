import MathlibProbe.RotorFreePairNonneg
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Coupling monotonicity of the physical planar rotor

Use the complex unit circle as coordinates on the Euclidean spin sphere.
Two independent Haar configurations can be written as `(u / v, u * v)`.
Increasing the pair couplings from J to K makes the joint Boltzmann
factor the exponential of a Gram kernel. Its cosine coefficients are
K + J and its sine coefficients are K - J. The difference of the real
parts of any tested circle character is twice the product of its two
imaginary parts. Integration gives the finite-volume Fourier comparison,
including the dot test as a special case.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace
namespace IsingScaling.Rotor.XY

private abbrev plane := Complex.orthonormalBasisOneI.repr
local instance : MeasurableSpace Circle := borel _
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The two real orthonormal coordinates identify a planar spin with a phase. -/
def phase (s : Spin 2) : Circle :=
  ⟨plane.symm s.val, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [plane.symm.norm_map, norm_eq_of_mem_sphere s]⟩

theorem continuous_phase : Continuous phase :=
  (plane.symm.continuous.comp continuous_subtype_val).subtype_mk _

private def circlePrior : Measure Circle := (SiteReflection.surfacePrior 2).map phase

private theorem phase_preserving : MeasurePreserving phase (SiteReflection.surfacePrior 2) circlePrior :=
  ⟨continuous_phase.measurable,rfl⟩

private instance : IsProbabilityMeasure circlePrior :=
  Measure.isProbabilityMeasure_map (μ := SiteReflection.surfacePrior 2) continuous_phase.measurable.aemeasurable

private instance : Measure.IsMulLeftInvariant circlePrior where
  map_mul_left_eq_self a := by
    let U := (plane.symm.trans (rotation a)).trans plane
    have h (s : Spin 2) : phase (SiteReflection.SphereSign.sphereMap U s) = a * phase s := by
      apply Subtype.ext
      change plane.symm (plane (rotation a (plane.symm s.val))) = _
      rw [plane.symm_apply_apply]
      rfl
    change ((SiteReflection.surfacePrior 2).map phase).map (a * ·) = _
    rw [Measure.map_map (measurable_const_mul _) continuous_phase.measurable]
    have hmap := (phase_preserving.comp (SiteReflection.SphereSign.sphereMap_preserving U)).map_eq
    simpa only [Function.comp_def,h] using hmap

private instance : Measure.IsHaarMeasure circlePrior where

private abbrev Config (V : Type*) := V → Circle
private abbrev prior (V : Type*) [Fintype V] : Measure (Config V) := Measure.pi (fun _ => circlePrior)

private def replicas (V : Type*) : (Config V × Config V) →* (Config V × Config V) where
  toFun p := (p.1 / p.2, p.1 * p.2)
  map_one' := by simp
  map_mul' := by intro a b; ext <;> simp [div_eq_mul_inv] <;> group

private theorem replicas_surjective (V : Type*) : Function.Surjective (replicas V) := by
  rintro ⟨a,b⟩
  have sq (x : Circle) : ∃ u : Circle, u ^ 2 = x := by
    obtain ⟨t,rfl⟩ := Circle.exp_surjective x
    exact ⟨Circle.exp (t/2),by rw [pow_two, ← Circle.exp_add]; congr 1; ring⟩
  choose u hu using fun i : V => sq (a i * b i)
  refine ⟨(u,u / a),?_⟩
  apply Prod.ext
  · funext i
    change u i / (u i / a i) = a i
    exact div_div_self' _ _
  · funext i
    change u i * (u i / a i) = b i
    rw [←mul_div_assoc,←pow_two,hu]
    exact mul_div_cancel_left _ _

private theorem replicas_preserving (V : Type*) [Fintype V] :
    MeasurePreserving (replicas V) ((prior V).prod (prior V)) ((prior V).prod (prior V)) :=
  MonoidHom.measurePreserving (by
    change Continuous (fun p : Config V × Config V => (p.1 / p.2, p.1 * p.2))
    fun_prop) (replicas_surjective V) rfl

variable {V : Type*}

private def angle (e : V × V) (s : Config V) : Circle := s e.1 / s e.2
private def cosine (e : V × V) (s : Config V) : ℝ := (angle e s : ℂ).re
private def sine (e : V × V) (s : Config V) : ℝ := (angle e s : ℂ).im

private theorem continuous_cosine (e : V × V) : Continuous (cosine e) := by
  unfold cosine angle
  exact Complex.continuous_re.comp (continuous_subtype_val.comp ((continuous_apply _).div' (continuous_apply _)))

private theorem continuous_sine (e : V × V) : Continuous (sine e) := by
  unfold sine angle
  exact Complex.continuous_im.comp (continuous_subtype_val.comp ((continuous_apply _).div' (continuous_apply _)))

private theorem cosine_div (e : V × V) (s t : Config V) :
    cosine e (s/t) = cosine e s * cosine e t + sine e s * sine e t := by
  have he : angle e (s/t) = angle e s * (angle e t)⁻¹ := by
    simp [angle,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
  simp only [cosine,sine,he,Circle.coe_mul,Circle.coe_inv_eq_conj,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  ring

private theorem cosine_mul (e : V × V) (s t : Config V) :
    cosine e (s*t) = cosine e s * cosine e t - sine e s * sine e t := by
  have he : angle e (s*t) = angle e s * angle e t := by
    exact (div_mul_div_comm ..).symm
  simp only [cosine,sine,he,Circle.coe_mul,Complex.mul_re]

theorem cosine_phase (x y : Spin 2) :
    ((phase x / phase y : Circle) : ℂ).re = ⟪x.val,y.val⟫_ℝ := by
  rw [← plane.symm.inner_map_map, real_inner_comm]
  change ((phase x / phase y : Circle) : ℂ).re =
    (plane.symm x.val * (starRingEnd ℂ) (plane.symm y.val)).re
  rw [div_eq_mul_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]
  rfl

variable [Fintype V]

private def weight (J : V × V → ℝ) (s : Config V) : ℝ :=
  Real.exp (∑ e, J e * cosine e s)

private theorem continuous_weight (J : V × V → ℝ) : Continuous (weight J) :=
  (continuous_finsetSum _ (fun e _ => continuous_const.mul (continuous_cosine e))).rexp

private def mean (J : V × V → ℝ) (a : V × V) : ℝ :=
  (∫ s, weight J s * cosine a s ∂prior V) / ∫ s, weight J s ∂prior V

private def featureKernel (b : V × V → ℝ) (f : V × V → Config V → ℝ)
    (s t : Config V) : ℝ := ∏ e, Real.exp (b e * (f e s * f e t))

private theorem continuous_featureKernel (b : V × V → ℝ) (f : V × V → Config V → ℝ)
    (hf : ∀ e, Continuous (f e)) : Continuous (featureKernel b f).uncurry := by
  apply continuous_finsetProd
  intro e _
  exact (continuous_const.mul (((hf e).comp continuous_fst).mul ((hf e).comp continuous_snd))).rexp

private theorem feature_positive {b : V × V → ℝ} (hb : ∀ e, 0 ≤ b e)
    (f : V × V → Config V → ℝ) {ι : Type*} [Fintype ι] (s : ι → Config V) :
    (Matrix.of fun i j => featureKernel b f (s i) (s j)).PosSemidef := by
  have h := seam_posSemidef Finset.univ b (fun e _ => hb e) (fun i e => f e (s i))
  simpa only [featureKernel,Real.inner_apply,mul_comm] using h

private def kernel (J K : V × V → ℝ) (s t : Config V) : ℝ :=
  featureKernel (fun e => K e+J e) cosine s t *
    featureKernel (fun e => K e-J e) sine s t

private theorem weight_replicas (J K : V × V → ℝ) (s t : Config V) :
    weight K (s/t) * weight J (s*t) = kernel J K s t := by
  unfold weight kernel featureKernel
  rw [← Real.exp_sum,← Real.exp_sum,← Real.exp_add,← Real.exp_add,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply congrArg Real.exp
  apply Finset.sum_congr rfl
  intro e _
  rw [cosine_div,cosine_mul]
  ring

private theorem kernel_integral_nonneg {J K : V × V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (hJK : ∀ e, J e ≤ K e) (f : Config V → ℝ) (hf : Continuous f) :
    0 ≤ ∫ p : Config V × Config V, f p.1 * f p.2 * kernel J K p.1 p.2
      ∂((prior V).prod (prior V)) := by
  let A (p : Config V × Config V) := f p.1 * f p.2 * kernel J K p.1 p.2
  have hcont : Continuous A :=
    ((hf.comp continuous_fst).mul (hf.comp continuous_snd)).mul
      ((continuous_featureKernel _ cosine continuous_cosine).mul
        (continuous_featureKernel _ sine continuous_sine))
  apply integral_nonneg_of_sample_sum (prior V) A
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hcont.comp (continuous_id.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  intro n s
  have hcos := feature_positive (fun e => add_nonneg ((hJ e).trans (hJK e)) (hJ e)) cosine s
  have hsin := feature_positive (fun e => sub_nonneg.mpr (hJK e)) sine s
  have h := (hcos.hadamard hsin).dotProduct_mulVec_nonneg (fun i => f (s i))
  simpa only [A,kernel,Matrix.mulVec,dotProduct,Pi.star_apply,star_trivial,Finset.mul_sum,
    Matrix.hadamard_apply,Matrix.of_apply,mul_assoc,mul_left_comm,mul_comm] using h

private theorem intCont {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hc : Continuous f) : Integrable f μ :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem read_mono {J K : V × V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (hJK : ∀ e, J e ≤ K e) (c d : Config V → ℝ) (hc : Continuous c) (hd : Continuous d)
    (hdiff : ∀ u v, c (u/v) - c (u*v) = 2 * (d u * d v)) :
    (∫ s, weight J s * c s ∂prior V) / (∫ s, weight J s ∂prior V) ≤
      (∫ s, weight K s * c s ∂prior V) / (∫ s, weight K s ∂prior V) := by
  let μ := prior V
  let F (p : Config V × Config V) :=
    (weight K p.1 * c p.1) * weight J p.2 -
      weight K p.1 * (weight J p.2 * c p.2)
  have hL : Continuous (fun p : Config V × Config V =>
      (weight K p.1 * c p.1) * weight J p.2) :=
    ((continuous_weight K).mul hc).comp continuous_fst
    |>.mul ((continuous_weight J).comp continuous_snd)
  have hR : Continuous (fun p : Config V × Config V =>
      weight K p.1 * (weight J p.2 * c p.2)) := ((continuous_weight K).comp continuous_fst).mul
    (((continuous_weight J).mul hc).comp continuous_snd)
  have hf : Continuous F := hL.sub hR
  have he (p : Config V × Config V) : F (replicas V p) =
      2 * (d p.1 * d p.2 * kernel J K p.1 p.2) := by
    change (weight K (p.1/p.2) * c (p.1/p.2)) * weight J (p.1*p.2) -
      weight K (p.1/p.2) * (weight J (p.1*p.2) * c (p.1*p.2)) = _
    rw [←weight_replicas]
    linear_combination (weight K (p.1/p.2) * weight J (p.1*p.2)) * hdiff p.1 p.2
  have h0 : 0 ≤ ∫ p, F p ∂(μ.prod μ) := by
    rw [← (replicas_preserving V).hasLaw.integral_comp hf.aestronglyMeasurable]
    simp only [Function.comp_def,he,integral_const_mul]
    exact mul_nonneg (by norm_num) (kernel_integral_nonneg hJ hJK d hd)
  change 0 ≤ ∫ p, (weight K p.1*c p.1)*weight J p.2 -
    weight K p.1*(weight J p.2*c p.2) ∂(μ.prod μ) at h0
  rw [integral_sub (intCont hL) (intCont hR),
    integral_prod_mul (fun s => weight K s * c s) (weight J),
    integral_prod_mul (weight K) (fun s => weight J s * c s)] at h0
  have hz (B : V × V → ℝ) : 0 < ∫ s, weight B s ∂μ :=
    integral_exp_pos (intCont (continuous_weight B))
  apply (div_le_div_iff₀ (hz J) (hz K)).mpr
  linarith

private theorem mean_mono {J K : V × V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (hJK : ∀ e, J e ≤ K e) (a : V × V) : mean J a ≤ mean K a := by
  apply read_mono hJ hJK (cosine a) (sine a) (continuous_cosine a) (continuous_sine a)
  intro u v
  rw [cosine_div,cosine_mul]
  ring

/-- A finite list of sites and signed integer multiplicities specifies a cylinder character.
Repeated sites are allowed. -/
def chargeCharacter {I : Type*} [Fintype I] (a : I → V) (m : I → ℤ) : (V → Circle) →* Circle where
  toFun s := ∏ i, s (a i) ^ m i
  map_one' := by simp
  map_mul' := by intro s t; simp [mul_zpow,Finset.prod_mul_distrib]

omit [Fintype V] in
theorem continuous_chargeCharacter {I : Type*} [Fintype I] (a : I → V) (m : I → ℤ) :
    Continuous (chargeCharacter a m) :=
  continuous_finsetProd _ fun i _ => (continuous_apply (a i)).zpow _

private def realCharacter {I : Type*} [Fintype I] (a : I → V) (m : I → ℤ) (s : V → Circle) : ℝ :=
  (chargeCharacter a m s : ℂ).re

omit [Fintype V] in
private theorem continuous_realCharacter {I : Type*} [Fintype I] (a : I → V) (m : I → ℤ) :
    Continuous (realCharacter a m) :=
  Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_chargeCharacter a m))

private theorem realCharacter_mono {I : Type*} [Fintype I] {J K : V × V → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (hJK : ∀ e, J e ≤ K e) (a : I → V) (m : I → ℤ) :
    (∫ s, weight J s * realCharacter a m s ∂prior V) / (∫ s, weight J s ∂prior V) ≤
      (∫ s, weight K s * realCharacter a m s ∂prior V) / (∫ s, weight K s ∂prior V) := by
  let χ := chargeCharacter a m
  apply read_mono hJ hJK _ (fun s => (χ s : ℂ).im) (continuous_realCharacter a m)
    (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_chargeCharacter a m)))
  intro u v
  change (χ (u/v) : ℂ).re - (χ (u*v) : ℂ).re = _
  simp only [div_eq_mul_inv,map_mul,map_inv,Circle.coe_mul,Circle.coe_inv_eq_conj,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

/-- Finite graph integral with an independent uniform unit-circle spin
at every vertex. J already includes any directed-edge counting factor. -/
def graphPair (J : V × V → ℝ) (v w : V) : ℝ :=
  let μ := Measure.pi (fun _ : V => SiteReflection.surfacePrior 2)
  let W (s : V → Spin 2) := Real.exp (∑ e : V × V, J e * ⟪(s e.1).val,(s e.2).val⟫_ℝ)
  (∫ s, W s * ⟪(s v).val,(s w).val⟫_ℝ ∂μ) / ∫ s, W s ∂μ

private theorem graphPair_eq_mean (J : V × V → ℝ) (v w : V) :
    graphPair J v w = mean J (v,w) := by
  let μ := Measure.pi (fun _ : V => SiteReflection.surfacePrior 2)
  have h : MeasurePreserving (fun s : V → Spin 2 => phase ∘ s) μ (prior V) :=
    measurePreserving_pi _ _ (fun _ => phase_preserving)
  have hs (e : V × V) (s : V → Spin 2) : cosine e (phase ∘ s) = ⟪(s e.1).val,(s e.2).val⟫_ℝ :=
    cosine_phase _ _
  unfold mean
  have hc : Continuous (fun s => weight J s * cosine (v,w) s) :=
    (continuous_weight J).mul (continuous_cosine (v,w))
  rw [← h.hasLaw.integral_comp hc.aestronglyMeasurable,
    ← h.hasLaw.integral_comp (continuous_weight J).aestronglyMeasurable]
  simp only [Function.comp_apply,weight,hs]
  rfl

/-- Ginibre monotonicity for the original dot read and normalized sphere prior. -/
theorem graphPair_mono {J K : V × V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (hJK : ∀ e, J e ≤ K e) (v w : V) : graphPair J v w ≤ graphPair K v w := by
  rw [graphPair_eq_mean,graphPair_eq_mean]
  exact mean_mono hJ hJK _

/-- A circle-coordinate observable integrated against the finite graph sphere Gibbs law. -/
def graphPhaseRead (J : V × V → ℝ) (f : (V → Circle) → ℝ) : ℝ :=
  let μ := Measure.pi (fun _ : V => SiteReflection.surfacePrior 2)
  let W (s : V → Spin 2) := Real.exp (∑ e : V × V, J e * ⟪(s e.1).val,(s e.2).val⟫_ℝ)
  (∫ s, W s * f (phase ∘ s) ∂μ) / (∫ s, W s ∂μ)

private def circleRead (J : V × V → ℝ) (f : Config V → ℝ) : ℝ :=
  (∫ s, weight J s * f s ∂prior V) / (∫ s, weight J s ∂prior V)

private theorem graphPhaseRead_eq (J : V × V → ℝ) {f : Config V → ℝ} (hf : Continuous f) :
    graphPhaseRead J f = circleRead J f := by
  let μ := Measure.pi (fun _ : V => SiteReflection.surfacePrior 2)
  have h : MeasurePreserving (fun s : V → Spin 2 => phase ∘ s) μ (prior V) :=
    measurePreserving_pi _ _ (fun _ => phase_preserving)
  have hs (e : V × V) (s : V → Spin 2) : cosine e (phase ∘ s) = ⟪(s e.1).val,(s e.2).val⟫_ℝ :=
    cosine_phase _ _
  have hc : Continuous (fun s => weight J s * f s) := (continuous_weight J).mul hf
  unfold circleRead
  rw [← h.hasLaw.integral_comp hc.aestronglyMeasurable,
    ← h.hasLaw.integral_comp (continuous_weight J).aestronglyMeasurable]
  simp only [Function.comp_apply,weight,hs]
  rfl

/-- Real Fourier moment under the finite graph XY Gibbs law. -/
def graphFourierMoment {I : Type*} [Fintype I] (J : V × V → ℝ) (a : I → V) (m : I → ℤ) : ℝ :=
  graphPhaseRead J (realCharacter a m)

private theorem graphFourierMoment_eq_integral {I : Type*} [Fintype I] (J : V × V → ℝ)
    (a : I → V) (m : I → ℤ) : graphFourierMoment J a m = circleRead J (realCharacter a m) :=
  graphPhaseRead_eq J (continuous_realCharacter a m)

/-- Conjugating every spin annihilates every sine Fourier moment at zero field. -/
theorem graphPhaseRead_im_eq_zero {I : Type*} [Fintype I] (J : V × V → ℝ) (a : I → V) (m : I → ℤ) :
    graphPhaseRead J (fun s => (chargeCharacter a m s : ℂ).im) = 0 := by
  let χ := chargeCharacter a m
  have hc : Continuous (fun s : Config V => (chargeCharacter a m s : ℂ).im) :=
    Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_chargeCharacter a m))
  rw [graphPhaseRead_eq J hc]
  have hweight (s : Config V) : weight J s⁻¹ = weight J s := by
    unfold weight
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    have ha : angle e s⁻¹ = (angle e s)⁻¹ := by simp [angle,div_eq_mul_inv,mul_comm]
    simp only [cosine,ha,Circle.coe_inv_eq_conj,Complex.conj_re]
  let F (s : Config V) := weight J s * (χ s : ℂ).im
  have hF (s : Config V) : F s⁻¹ = -F s := by simp [F,hweight,map_inv,Circle.coe_inv_eq_conj]
  have hp : MeasurePreserving (invMonoidHom : Config V →* Config V) (prior V) (prior V) :=
    MonoidHom.measurePreserving continuous_inv inv_surjective rfl
  have hcontF : Continuous F := (continuous_weight J).mul hc
  have he := hp.hasLaw.integral_comp hcontF.aestronglyMeasurable
  change (∫ s, F s⁻¹ ∂prior V) = ∫ s, F s ∂prior V at he
  simp only [hF,integral_neg] at he
  have hz : (∫ s, F s ∂prior V) = 0 := by linarith
  exact div_eq_zero_iff.mpr (Or.inl hz)

/-- Ginibre comparison for the real part of any finite integer character. -/
theorem graphFourierMoment_mono {I : Type*} [Fintype I] {J K : V × V → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (hJK : ∀ e, J e ≤ K e) (a : I → V) (m : I → ℤ) :
    graphFourierMoment J a m ≤ graphFourierMoment K a m := by
  simpa only [graphFourierMoment_eq_integral,circleRead] using realCharacter_mono hJ hJK a m

private def edges (p : V → Site) : Finset (V × V) :=
  univ.filter fun e => latticeDistance (p e.1) (p e.2) = 1

private def coupling [DecidableEq V] (S : Finset (V × V)) (β : ℝ) (e : V × V) : ℝ :=
  if e ∈ S then β/2 else 0

/-- Dot expectation for the finite induced free lattice with vertex locations p. -/
def finitePair (p : V → Site) (β : ℝ) (v w : V) : ℝ :=
  graphPair (fun e => if latticeDistance (p e.1) (p e.2) = 1 then β/2 else 0) v w

private theorem finitePair_edges [DecidableEq V] (p : V → Site) (β : ℝ) (v w : V) :
    finitePair p β v w = mean (coupling (edges p) β) (v,w) := by
  rw [finitePair, graphPair_eq_mean]
  congr 1
  funext e
  simp [coupling,edges]

private theorem weight_on_edges [DecidableEq V] (S : Finset (V × V)) (β : ℝ) (s : Config V) :
    weight (coupling S β) s = Real.exp (∑ e ∈ S, β/2 * cosine e s) := by
  unfold weight coupling
  simp only [ite_mul,zero_mul,←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]

private theorem read_embed {W : Type*} [Fintype W] [DecidableEq V] [DecidableEq W]
    (p : V → Site) (q : W → Site) (i : V ↪ W)
    (hi : ∀ x y, latticeDistance (q (i x)) (q (i y)) = latticeDistance (p x) (p y))
    {β : ℝ} (hβ : 0 ≤ β) (f : Config V → ℝ) (g : Config W → ℝ) (hf : Continuous f)
    (hg : ∀ s, g s = f (s ∘ i))
    (hmono : ∀ {J K : W × W → ℝ}, (∀ e, 0 ≤ J e) → (∀ e, J e ≤ K e) → circleRead J g ≤ circleRead K g) :
    circleRead (coupling (edges p) β) f ≤ circleRead (coupling (edges q) β) g := by
  classical
  let emb := i.prodMap i
  let S := (edges p).map emb
  have hS : S ⊆ edges q := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hb
    exact mem_filter.mpr ⟨mem_univ _,(hi a.1 a.2).trans (mem_filter.mp ha).2⟩
  let restrict : Config W →* Config V :=
    { toFun := fun s => s ∘ i, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hr : MeasurePreserving restrict (prior W) (prior V) :=
    MonoidHom.measurePreserving (continuous_pi fun x => continuous_apply (i x))
      i.injective.surjective_comp_right (by simp)
  have hw (s : Config W) : weight (coupling S β) s = weight (coupling (edges p) β) (restrict s) := by
    simp only [weight_on_edges,S,Finset.sum_map]
    rfl
  have hsmall : circleRead (coupling S β) g = circleRead (coupling (edges p) β) f := by
    let J := coupling (edges p) β
    have hc : Continuous (fun s => weight J s * f s) := (continuous_weight J).mul hf
    unfold circleRead
    rw [← hr.hasLaw.integral_comp hc.aestronglyMeasurable,
      ← hr.hasLaw.integral_comp (continuous_weight J).aestronglyMeasurable]
    simp only [hw,hg,Function.comp_apply] <;> rfl
  rw [←hsmall]
  apply hmono
  · intro b
    unfold coupling
    split_ifs <;> positivity
  · intro b
    by_cases hb : b ∈ S
    · simp [coupling,hb,hS hb]
    · simp [coupling,hb]
      split_ifs <;> positivity

/-- Inserting additional nearest-neighbour bonds after embedding the old
vertices increases every original two-site expectation. -/
theorem finitePair_embed {W : Type*} [Fintype W] (p : V → Site) (q : W → Site)
    (i : V ↪ W) (hi : ∀ a b, latticeDistance (q (i a)) (q (i b)) = latticeDistance (p a) (p b))
    {β : ℝ} (hβ : 0 ≤ β) (v w : V) : finitePair p β v w ≤ finitePair q β (i v) (i w) := by
  classical
  rw [finitePair_edges,finitePair_edges]
  exact read_embed p q i hi hβ (cosine (v,w)) (cosine (i v,i w)) (continuous_cosine _) (fun _ => rfl)
    (fun hJ hJK => mean_mono hJ hJK (i v,i w))

/-- Real Fourier read on a finite induced physical domain, with the original nearest-neighbour coupling. -/
def finiteFourierMoment {I : Type*} [Fintype I] (p : V → Site) (β : ℝ) (a : I → V) (m : I → ℤ) : ℝ :=
  graphFourierMoment (fun e => if latticeDistance (p e.1) (p e.2) = 1 then β/2 else 0) a m

private theorem finiteFourierMoment_edges {I : Type*} [Fintype I] [DecidableEq V] (p : V → Site)
    (β : ℝ) (a : I → V) (m : I → ℤ) :
    finiteFourierMoment p β a m = circleRead (coupling (edges p) β) (realCharacter a m) := by
  rw [finiteFourierMoment,graphFourierMoment_eq_integral]
  congr 1
  funext e
  simp [coupling,edges]

/-- Adding sites and all their ferromagnetic bonds increases every real Fourier moment. -/
theorem finiteFourierMoment_embed {I W : Type*} [Fintype I] [Fintype W] (p : V → Site) (q : W → Site)
    (i : V ↪ W) (hi : ∀ x y, latticeDistance (q (i x)) (q (i y)) = latticeDistance (p x) (p y))
    {β : ℝ} (hβ : 0 ≤ β) (a : I → V) (m : I → ℤ) :
    finiteFourierMoment p β a m ≤ finiteFourierMoment q β (i ∘ a) m := by
  classical
  rw [finiteFourierMoment_edges,finiteFourierMoment_edges]
  exact read_embed p q i hi hβ (realCharacter a m) (realCharacter (i ∘ a) m)
    (continuous_realCharacter a m) (fun _ => rfl) (fun hJ hJK => realCharacter_mono hJ hJK (i ∘ a) m)

#print axioms graphPhaseRead_im_eq_zero
#print axioms finiteFourierMoment_embed
#print axioms graphFourierMoment_mono
#print axioms graphPair_mono
#print axioms finitePair_embed
end IsingScaling.Rotor.XY
