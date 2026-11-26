import MathlibProbe.RotorLocalGibbsLimit
import MathlibProbe.RotorPeriodicVM4Bridge
import MathlibProbe.RotorPeriodizedWalkResolvent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Positive resolvent mixtures and their physical first variations

Index the mass-one lattice resolvents by all rational admissible triples.
Make three copies of each triple, corresponding to the mass, the third-axis
hopping and the horizontal face hopping. Give each copy strictly positive
weight with summable weighted lattice norm. Thus every finite linear
combination of the density generators changes only finitely many copies of
the same interaction. Rescaling time by their actual coefficients and Fourier
multiplicities realizes the requested derivative of the original lattice
coupling. The open positivity and mass-gap bounds hold simultaneously near
zero because only these finitely many components change.
-/

noncomputable section
open Filter Finset
open scoped Topology ENNReal
namespace IsingScaling.Rotor.PressureSelection.PhysicalVariations
open MathlibProbe.RotorResolventTestApproximation
open LatticeWalk

abbrev AdmissibleRat := {p : Fin 3 → ℚ // Good (fun i => (p i : ℝ))}
abbrev Index := AdmissibleRat × Fin 3

def parameter (j : Index) (i : Fin 3) : ℝ := j.1.1 i
def a (j : Index) := parameter j 0 / 2
def b (j : Index) := parameter j 1 / 4
def c (j : Index) := parameter j 2 / 8

theorem admissible (j : Index) :
    0 < c j ∧ 2*c j < b j ∧ 4*b j+4*c j < a j ∧ 6*a j+12*b j+8*c j < 1 := by
  have h : ![2*a j,4*b j,8*c j] = parameter j := by
    funext i
    fin_cases i <;> simp [a,b,c] <;> ring
  exact (good_walk_coefficients_iff _ _ _).mp (h ▸ j.1.property)

private theorem positive (j : Index) : 0<a j ∧ 0<b j ∧ 0<c j := by
  obtain ⟨hc,hb,ha,_⟩ := admissible j
  exact ⟨by linarith,by linarith,hc⟩

def sites : Fin 3 → List (Fin 3) := ![[],[2],[0,1]]
def multiplicity : Fin 3 → ℝ := ![1,2,4]
def coeff (j : Index) : Alg := ![1,coord 2,coord 0 * coord 1] j.2
def generator (j : Index) : Alg := coeff j * R (parameter j)^2

theorem variations_eq_range : variations = Set.range generator := by
  ext F
  constructor
  · rintro (⟨p,hp,rfl⟩ | ⟨_,⟨p,hp,rfl⟩,rfl⟩ | ⟨_,⟨p,hp,rfl⟩,rfl⟩)
    · exact ⟨(⟨p,hp⟩,0),one_mul _⟩
    · exact ⟨(⟨p,hp⟩,1),rfl⟩
    · exact ⟨(⟨p,hp⟩,2),rfl⟩
  · rintro ⟨⟨p,i⟩,rfl⟩
    have hg : R (fun l => (p.1 l:ℝ)) ^ 2 ∈ gens := ⟨p.1,p.2,rfl⟩
    fin_cases i
    · apply Or.inl
      change (1:Alg) * R (parameter (p,0)) ^ 2 ∈ gens
      rw [one_mul]
      exact ⟨p.1,p.2,rfl⟩
    · exact Or.inr (Or.inl ⟨_,hg,rfl⟩)
    · exact Or.inr (Or.inr ⟨_,hg,rfl⟩)

def component (j : Index) (t : ℝ) : LatticeL1 :=
  operatorCurve (a j) (b j) (c j) (orbitOperator (sites j.2)) t

def C (j : Index) := component j 0

theorem component_zero (j : Index) : component j 0 = C j := rfl

theorem component_zero_apply (j : Index) (z : Site) :
    C j z = coupling (a j) (b j) (c j) 1 z :=
  operatorCurve_zero (positive j).1.le (positive j).2.1.le (positive j).2.2.le
    (admissible j).2.2.2 _ z

theorem C_nonneg (j : Index) (z : Site) : 0 ≤ C j z := by
  rw [component_zero_apply]
  exact coupling_nonneg (positive j).1.le (positive j).2.1.le (positive j).2.2.le zero_lt_one z

private theorem R_eq (j : Index) (k : Momentum) :
    R (parameter j) (momentumCosine k) = (1-fourierStep (a j) (b j) (c j) k)⁻¹ := by
  rw [R_apply_of_good (parameter j) j.1.property (momentumCosine k),symbol_apply,fourierStep_eq]
  congr 2
  simp [a,b,c,coord,momentumCosine]
  ring

theorem physical_generator (j : Index) :
    ∃ D : LatticeL1, HasDerivAt (component j) D 0 ∧ ∀ k : Momentum,
      interactionMultiplier D (l1_abs_summable D) k =
        multiplicity j.2 * generator j (momentumCosine k) := by
  obtain ⟨D,hD,hk⟩ := physical_orbit_variation (positive j).1.le (positive j).2.1.le
    (positive j).2.2.le (admissible j).2.2.2 (sites j.2)
  refine ⟨D,hD,fun k => ?_⟩
  rw [hk]
  change _ = multiplicity j.2 * (coeff j (momentumCosine k) *
    (R (parameter j) (momentumCosine k))^2)
  rw [R_eq]
  rcases j with ⟨p,i⟩
  fin_cases i <;> simp [sites,multiplicity,coeff,coord,momentumCosine] <;> ring

def tangent (j : Index) : LatticeL1 := (physical_generator j).choose

theorem tangent_deriv (j : Index) : HasDerivAt (component j) (tangent j) 0 :=
  (physical_generator j).choose_spec.1

theorem tangent_fourier (j : Index) (k : Momentum) :
    interactionMultiplier (tangent j) (l1_abs_summable _) k =
      multiplicity j.2 * generator j (momentumCosine k) :=
  (physical_generator j).choose_spec.2 k

private noncomputable instance : Encodable Index := Encodable.ofCountable _

def envelope (j : Index) : ℝ := (1/2:ℝ)^(Encodable.encode j)
def alpha (j : Index) : ℝ := envelope j / (1+‖C j‖)

theorem alpha_pos (j : Index) : 0<alpha j := div_pos (by dsimp [envelope]; positivity) (by positivity)

theorem weighted_summable : Summable (fun j => alpha j • C j) := by
  apply (summable_geometric_two_encode (ι := Index)).of_norm_bounded
  intro j
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (alpha_pos j)]
  change envelope j / (1 + ‖C j‖) * ‖C j‖ ≤ envelope j
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<1+‖C j‖)]
  have he : 0<envelope j := by dsimp [envelope]; positivity
  linarith

theorem alpha_mass_summable : Summable (fun j => alpha j * (1+‖C j‖)) := by
  have h (j : Index) : alpha j * (1+‖C j‖) = envelope j :=
    div_mul_cancel₀ _ (by positivity)
  simpa only [h,envelope] using (summable_geometric_two_encode (ι := Index))

def nearest (β : ℝ) : LatticeL1 :=
  ⟨LocalGibbs.nearestCoupling β, (memℓp_gen_iff (by norm_num : 0<(1:ℝ≥0∞).toReal)).2
    (by simpa [Real.norm_eq_abs] using LocalGibbs.summable_abs_nearest β)⟩

def mixture : LatticeL1 := ∑' j, alpha j • C j
def J (β δ : ℝ) : LatticeL1 := nearest β + δ • mixture

theorem J_tendsto_nearest (β : ℝ) : Tendsto (J β) (𝓝 0) (𝓝 (nearest β)) := by
  change Tendsto (fun t : ℝ => nearest β + t • mixture) _ _
  simpa using (show Continuous (fun t : ℝ => nearest β+t • mixture) by fun_prop).tendsto 0

/-- The increments of mass and of the seven original hopping orbits. -/
def dm : Fin 3 → ℝ := ![1,0,0]
def dw (i : Fin 3) (j : Fin 7) : ℝ :=
  if (i=1 ∧ j=2) ∨ (i=2 ∧ j=3) then 1 else 0

theorem slot_operator (i : Fin 3) : orbitOperator (sites i) =
    dm i • (1:Operator) + hopping (dw i) := by
  fin_cases i <;> simp [sites,dm,dw,hopping,directions,orbitOperator]

def slotWeights (j : Index) (s : ℝ) (i : Fin 7) :=
  weight (a j) (b j) (c j) i + s * dw j.2 i

/-- The precise strict seam margins, mass gap, pointwise positivity and
oblique swap symmetries for the actual perturbed component. -/
def Allowed (j : Index) (s : ℝ) : Prop :=
  (∀ i, 0 ≤ slotWeights j s i) ∧
  (∑ i, slotWeights j s i * (2:ℝ)^(directions i).length < 1-s*dm j.2) ∧
  ‖walkOperator (a j) (b j) (c j) + s • (dm j.2 • (1:Operator) + hopping (dw j.2))‖ < 1 ∧
  2*slotWeights j s 6 < slotWeights j s 3 ∧
  2*slotWeights j s 3+2*slotWeights j s 4+4*slotWeights j s 6 < slotWeights j s 0 ∧
  slotWeights j s 0 = slotWeights j s 1 ∧ slotWeights j s 4 = slotWeights j s 5 ∧
  ∀ z, 0 ≤ component j s z

theorem eventually_allowed (j : Index) : ∀ᶠ s in 𝓝 (0:ℝ), Allowed j s := by
  obtain ⟨hc,hb,ha,hgap⟩ := admissible j
  obtain ⟨ha',hb',hc'⟩ := positive j
  have h := PeriodizedWalk.eventually_admissible_weights ha' hb' hc' hgap (dm j.2) (dw j.2)
  have hnn := affine_curve_nonneg ha' hb' hc' hgap (dm j.2) (dw j.2)
  have ob : ∀ᶠ s in 𝓝 (0:ℝ), 2*slotWeights j s 6 < slotWeights j s 3 :=
    (isOpen_lt (show Continuous (fun s => 2*slotWeights j s 6) by unfold slotWeights; fun_prop)
      (show Continuous (fun s => slotWeights j s 3) by unfold slotWeights; fun_prop)).mem_nhds
      (by simpa [slotWeights,weight] using hb)
  have ax : ∀ᶠ s in 𝓝 (0:ℝ), 2*slotWeights j s 3+2*slotWeights j s 4+4*slotWeights j s 6 <
      slotWeights j s 0 :=
    (isOpen_lt (show Continuous (fun s => 2*slotWeights j s 3+2*slotWeights j s 4+
      4*slotWeights j s 6) by unfold slotWeights; fun_prop)
      (show Continuous (fun s => slotWeights j s 0) by unfold slotWeights; fun_prop)).mem_nhds
      (by simp [slotWeights,weight]; linarith)
  filter_upwards [h,hnn,ob,ax] with s hs hh ho hx
  refine ⟨hs.1,hs.2.1,hs.2.2,ho,hx,?_,?_,?_⟩
  · simp [slotWeights,dw,weight]
  · simp [slotWeights,dw,weight]
  · simpa only [component,slot_operator] using hh

def speed (δ : ℝ) (d : Index →₀ ℝ) (j : Index) : ℝ :=
  d j / ((δ*alpha j)*multiplicity j.2)

def remainder (S : Finset Index) : LatticeL1 :=
  ∑' j : {j : Index // j ∉ S}, alpha j.1 • C j.1

def perturbed (β δ : ℝ) (d : Index →₀ ℝ) (t : ℝ) : LatticeL1 :=
  nearest β + δ • remainder d.support +
    ∑ j ∈ d.support, (δ*alpha j) • component j (speed δ d j * t)

def derivative (d : Index →₀ ℝ) : LatticeL1 :=
  ∑ j ∈ d.support, (d j / multiplicity j.2) • tangent j

theorem perturbed_zero (β δ : ℝ) (d : Index →₀ ℝ) :
    perturbed β δ d 0 = J β δ := by
  have ht := weighted_summable.sum_add_tsum_subtype_compl d.support
  change (∑ j ∈ d.support, alpha j • C j) + remainder d.support = mixture at ht
  rw [J,←ht,smul_add,Finset.smul_sum]
  simp only [perturbed,mul_zero,component_zero,smul_smul]
  abel

private theorem multiplicity_pos (i : Fin 3) : 0 < multiplicity i := by
  fin_cases i <;> norm_num [multiplicity]

theorem perturbed_hasDerivAt (β : ℝ) {δ : ℝ} (hδ : 0<δ) (d : Index →₀ ℝ) :
    HasDerivAt (perturbed β δ d) (derivative d) 0 := by
  have each (j : Index) : HasDerivAt (fun t : ℝ =>
      (δ*alpha j) • component j (speed δ d j * t)) ((d j / multiplicity j.2) • tangent j) 0 := by
    have ht : HasDerivAt (fun t : ℝ => speed δ d j * t) (speed δ d j) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul (speed δ d j)
    have hD := ((tangent_deriv j).scomp_of_eq 0 ht (by simp)).const_smul (δ*alpha j)
    have hc : (δ*alpha j)*speed δ d j = d j / multiplicity j.2 := by
      unfold speed
      field_simp [hδ.ne', (alpha_pos j).ne', (multiplicity_pos j.2).ne']
    rw [←hc,←smul_smul]
    exact hD
  exact (HasDerivAt.fun_sum fun j _ => each j).const_add (nearest β + δ • remainder d.support)

theorem all_components_allowed (δ : ℝ) (d : Index →₀ ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ j : Index, Allowed j (speed δ d j*t) := by
  have h (j : Index) : ∀ᶠ t in 𝓝 (0:ℝ), Allowed j (speed δ d j*t) := by
    have hc : Tendsto (fun t : ℝ => speed δ d j*t) (𝓝 0) (𝓝 0) := by
      simpa using (show Continuous (fun t : ℝ => speed δ d j*t) by fun_prop).tendsto 0
    exact hc (eventually_allowed j)
  have hall := (Filter.eventually_all_finset d.support).mpr (fun j _ => h j)
  filter_upwards [hall] with t ht j
  by_cases hj : j ∈ d.support
  · exact ht j hj
  · have h0 := mem_of_mem_nhds (eventually_allowed j)
    simpa [speed,Finsupp.notMem_support_iff.mp hj] using h0

private theorem summable_character (v : LatticeL1) (k : Momentum) :
    Summable (fun z => v z * realCharacter z k) := by
  apply (l1_abs_summable v).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_realCharacter_le_one z k)

def fourierAt (k : Momentum) : LatticeL1 →ₗ[ℝ] ℝ where
  toFun v := ∑' z, v z * realCharacter z k
  map_add' f g := by
    change (∑' z, (f z + g z)*realCharacter z k) = _
    simp only [add_mul]
    exact (summable_character f k).tsum_add (summable_character g k)
  map_smul' s f := by
    change (∑' z, (s*f z)*realCharacter z k) = s * _
    simp only [mul_assoc, tsum_mul_left]

theorem derivative_fourier (d : Index →₀ ℝ) (k : Momentum) :
    interactionMultiplier (derivative d) (l1_abs_summable _) k =
      (d.sum fun j s => s • generator j) (momentumCosine k) := by
  change fourierAt k (∑ j ∈ d.support, (d j/multiplicity j.2) • tangent j) = _
  rw [map_sum, Finsupp.sum, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change (d j / multiplicity j.2) *
    interactionMultiplier (tangent j) (l1_abs_summable _) k = d j * generator j (momentumCosine k)
  rw [tangent_fourier]
  field_simp [(multiplicity_pos j.2).ne']

/-- Every member of the already proved *dense* span is the exact multiplier
of a two-sided, physically admissible curve based at this one interaction. -/
theorem realizes_span (β : ℝ) {δ : ℝ} (hδ : 0<δ) {F : Alg}
    (hF : F ∈ Submodule.span ℝ variations) :
    ∃ d : Index →₀ ℝ, perturbed β δ d 0 = J β δ ∧
      HasDerivAt (perturbed β δ d) (derivative d) 0 ∧
      (∀ k : Momentum, interactionMultiplier (derivative d) (l1_abs_summable _) k =
        F (momentumCosine k)) ∧
      ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, Allowed j (speed δ d j*t) := by
  rw [variations_eq_range] at hF
  obtain ⟨d,hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hF
  exact ⟨d,perturbed_zero ..,perturbed_hasDerivAt β hδ d,fun k => (derivative_fourier d k).trans
    (congrArg (fun f : Alg => f (momentumCosine k)) hd),all_components_allowed ..⟩

theorem summable_components (δ : ℝ) (d : Index →₀ ℝ) (t : ℝ) :
    Summable (fun j => alpha j • component j (speed δ d j*t)) := by
  apply weighted_summable.congr_cofinite
  filter_upwards [d.support.finite_toSet.compl_mem_cofinite] with j hj
  have hz : d j = 0 := Finsupp.notMem_support_iff.mp hj
  simp [speed,hz,C]

theorem perturbed_eq_tsum (β δ : ℝ) (d : Index →₀ ℝ) (t : ℝ) :
    perturbed β δ d t = nearest β + δ • ∑' j, alpha j • component j (speed δ d j*t) := by
  have h := (summable_components δ d t).sum_add_tsum_subtype_compl d.support
  have he : (∑' j : {j : Index // j ∉ d.support}, alpha j.1 • component j.1 (speed δ d j.1*t))
      = remainder d.support := by
    apply tsum_congr
    intro j
    have hz := Finsupp.notMem_support_iff.mp j.2
    simp [speed,hz,C]
  rw [←h,he,smul_add,Finset.smul_sum]
  simp only [perturbed,smul_smul]
  abel

theorem perturbed_apply (β δ : ℝ) (d : Index →₀ ℝ) (t : ℝ) (z : Site) :
    perturbed β δ d t z = LocalGibbs.nearestCoupling β z +
      δ * ∑' j, alpha j * component j (speed δ d j*t) z := by
  rw [perturbed_eq_tsum]
  change _ + δ * _ = _ + δ * _
  congr 2
  exact (lp.evalCLM ℝ (fun _ : Site => ℝ) 1 z).map_tsum (summable_components δ d t)

theorem J_apply (β δ : ℝ) (z : Site) : J β δ z = LocalGibbs.nearestCoupling β z +
    δ * ∑' j, alpha j * coupling (a j) (b j) (c j) 1 z := by
  rw [←perturbed_zero β δ (0 : Index →₀ ℝ),perturbed_apply]
  simp only [mul_zero,component_zero,component_zero_apply]

theorem eventually_perturbed_nonneg {β δ : ℝ} (hβ : 0≤β) (hδ : 0≤δ) (d : Index →₀ ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ z, 0≤perturbed β δ d t z := by
  filter_upwards [all_components_allowed δ d] with t ht z
  rw [perturbed_apply]
  exact add_nonneg (by unfold LocalGibbs.nearestCoupling; split <;> positivity)
    (mul_nonneg hδ (tsum_nonneg fun j => mul_nonneg (alpha_pos j).le
      ((ht j).2.2.2.2.2.2.2 z)))

private theorem norm_one (v : LatticeL1) : ‖v‖ = ∑' z, |v z| := by
  simpa [Real.norm_eq_abs] using (lp.norm_eq_tsum_rpow (by norm_num : 0<(1:ℝ≥0∞).toReal) v)

/-- The scalar summability hypothesis for taking the sum of the individual
periodized reflected covariances, including all modified components. -/
theorem summable_alpha_l1 (δ : ℝ) (d : Index →₀ ℝ) (t : ℝ) :
    Summable (fun j => alpha j * ∑' z, |component j (speed δ d j*t) z|) := by
  have hs : Summable (fun j => alpha j * ‖C j‖) := by
    apply alpha_mass_summable.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (alpha_pos j).le (norm_nonneg _))]
    nlinarith [alpha_pos j]
  apply hs.congr_cofinite
  filter_upwards [d.support.finite_toSet.compl_mem_cofinite] with j hj
  have hz : d j = 0 := Finsupp.notMem_support_iff.mp hj
  simp only [speed,hz,zero_div,zero_mul,component_zero,norm_one]

theorem J_l1_nearest (β : ℝ) :
    Tendsto (fun δ : ℝ => ∑' z, |J β δ z - LocalGibbs.nearestCoupling β z|)
      (𝓝 0) (𝓝 0) := by
  have h := ((J_tendsto_nearest β).sub (tendsto_const_nhds (x := nearest β))).norm
  simpa only [sub_self,norm_zero,norm_one,lp.coeFn_sub,Pi.sub_apply,nearest] using h

/-- Exactly the lattice derivative norm used in the periodic Gibbs pressure
comparison, including the original fixed nearest-neighbour background. -/
theorem perturbed_l1_slope (β : ℝ) {δ : ℝ} (hδ : 0<δ) (d : Index →₀ ℝ) :
    Tendsto (fun t : ℝ => ∑' z, |(perturbed β δ d t z - J β δ z)/t-derivative d z|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h := (perturbed_hasDerivAt β hδ d).tendsto_slope_zero
  have hm := (h.sub (tendsto_const_nhds (x := derivative d))).norm
  simpa only [zero_add,sub_self,norm_zero,perturbed_zero,norm_one,lp.coeFn_sub,
    lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,div_eq_inv_mul] using hm

/-- A genuinely positive sequence of perturbations for the pressure
comparison. Every size and every component is admissible already at its
first term. The fixed background does not depend on the chosen probe. -/
theorem pressure_sequence (β : ℝ) {δ : ℝ} (hδ : 0<δ) {F : Alg}
    (hF : F ∈ Submodule.span ℝ variations) :
    ∃ (d : Index →₀ ℝ) (t : ℕ → ℝ), (∀ n, 0<t n) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ n j, Allowed j (speed δ d j*t n)) ∧
      (∀ k : Momentum, interactionMultiplier (derivative d) (l1_abs_summable _) k =
        F (momentumCosine k)) ∧
      Tendsto (fun n => ∑' z, |(perturbed β δ d (t n) z-J β δ z)/t n-derivative d z|)
        atTop (𝓝 0) := by
  obtain ⟨d,_,_,hF',ha⟩ := realizes_span β hδ hF
  let u (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp (n : ℕ) : 0<u n := by dsimp [u]; positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hu ha)
  have ht := hu.comp (tendsto_add_atTop_nat k)
  have ht' : Tendsto (fun n => u (n+k)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall fun n => (hp _).ne'⟩
  refine ⟨d,fun n => u (n+k),fun n => hp _,ht,fun n => hk (n+k) (by omega),hF',?_⟩
  exact (perturbed_l1_slope β hδ d).comp ht'

/-- From a finite reflected spin test to its actual lattice perturbation,
with the negative sign required by the variational comparison. -/
theorem reflected_test_sequence (β : ℝ) {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε)
    {ι : Type*} [Fintype ι] (r : Site → Site) (x : ι → Site) (v : ι → ℝ) :
    ∃ (d : Index →₀ ℝ) (t : ℕ → ℝ), (∀ n, 0<t n) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ n j, Allowed j (speed δ d j*t n)) ∧
      (∀ k : Momentum, |interactionMultiplier (derivative d) (l1_abs_summable _) k +
        horizontalMean (reflectedTest r x v) k| < ε) ∧
      Tendsto (fun n => ∑' z, |(perturbed β δ d (t n) z-J β δ z)/t n-derivative d z|)
        atTop (𝓝 0) := by
  obtain ⟨F,hF,hnear⟩ := horizontalMean_approx_variation r x v hε
  obtain ⟨d,t,ht,h0,ha,hSym,hL⟩ := pressure_sequence β hδ
    ((Submodule.span ℝ variations).neg_mem hF)
  refine ⟨d,t,ht,h0,ha,fun k => ?_,hL⟩
  rw [hSym,ContinuousMap.neg_apply]
  simpa only [sub_eq_add_neg,add_comm] using hnear k

#print axioms reflected_test_sequence
#print axioms pressure_sequence
#print axioms realizes_span
#print axioms perturbed_apply
#print axioms perturbed_l1_slope
end IsingScaling.Rotor.PressureSelection.PhysicalVariations
