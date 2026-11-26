import MathlibProbe.RotorHeisenbergComplexPartition
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Euler limit of the classical finite-graph Heisenberg spinor integral

One exchange factor is assigned to each matrix entry with coupling
half the corresponding matrix entry. The two-spin overlap is
one half times one plus the real spin dot. The extra scalar in the
exponential limit is consequently the exponential of half the sum of
the coupling matrix. No uniformity in the size of the graph is required.
-/

noncomputable section
open MeasureTheory Finset Filter Set
open scoped Topology InnerProductSpace
namespace IsingScaling.Rotor.HeisenbergField.ClassicalEuler
open ComplexPartition PressureSelection

variable {V : Type*} [Fintype V]

abbrev Labels (V : Type*) := (V × V) ⊕ V

def offset (J : V → V → ℝ) : ℝ := (∑ x : V, ∑ y : V, J x y) / 2

def coefficient (J : V → V → ℝ) (H : ComplexPartition.Field V) : Labels V → Config V → ℂ
  | .inl (x,y), s => ((J x y / 2 * (1 + ⟪(s x).val,(s y).val⟫_ℝ) : ℝ) : ℂ)
  | .inr x, s => ∑ i : Fin 3, H x i * ((s x).val i : ℂ)

def eulerWeight (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) (s : Config V) : ℂ :=
  ∏ i : Labels V, (1 + coefficient J H i s / (n : ℂ)) ^ n

def approximant (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) : ℂ :=
  ∫ s, eulerWeight J H n s ∂surfaceProduct V

/-- The bond shift accounts for the identity component of the spinor overlap. -/
theorem exp_coefficients (J : V → V → ℝ) (H : ComplexPartition.Field V) (s : Config V) :
    (∏ i : Labels V, Complex.exp (coefficient J H i s)) =
      (Real.exp (offset J) : ℂ) * weight J H s := by
  have hb : (∑ q : V × V, J q.1 q.2 / 2 *
      (1 + ⟪(s q.1).val,(s q.2).val⟫_ℝ)) = offset J + PressureSelection.energy J s := by
    rw [Fintype.sum_prod_type]
    simp only [offset,PressureSelection.energy,mul_add,mul_one,Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_div]
    · simp_rw [div_mul_eq_mul_div]
      simp only [Finset.sum_div]
  change (∏ i : Labels V, Complex.exp (coefficient J H i s)) =
    (Real.exp (offset J) : ℂ) * Complex.exp ((PressureSelection.energy J s : ℝ) +
      ∑ x : V, ∑ i : Fin 3, H x i * ((s x).val i : ℂ))
  rw [← Complex.exp_sum, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [Fintype.sum_sum_type]
  change (∑ q : V × V, ((J q.1 q.2 / 2 * (1+⟪(s q.1).val,(s q.2).val⟫_ℝ) : ℝ) : ℂ)) + _ = _
  rw [← Complex.ofReal_sum,hb,Complex.ofReal_add,add_assoc]
  rfl

/-- Euler's complex exponential limit with both its input and integer
parameter varying along the same filter. This permits uniformity on compacts. -/
private theorem euler_tendsto {T : Type*} {p : Filter T} {n : T → ℕ} {v : T → ℂ} {v₀ : ℂ}
    (hn : Tendsto n p atTop) (hv : Tendsto v p (𝓝 v₀)) :
    Tendsto (fun a => (1 + v a / (n a : ℂ)) ^ n a) p (𝓝 (Complex.exp v₀)) := by
  let f : ℂ → ℂ := fun z => Complex.log (1+z)
  let L := dslope f 0
  have hder : HasDerivAt f 1 0 := by
    have hs : (1 + (0 : ℂ)) ∈ Complex.slitPlane := by simp
    simpa [f,Function.comp_def] using! ((hasDerivAt_id (0 : ℂ)).const_add (1 : ℂ)).clog hs
  have hL : Tendsto L (𝓝 0) (𝓝 1) := by
    have hc := (continuousAt_dslope_same.mpr hder.differentiableAt).tendsto
    simpa only [L,dslope_same,hder.deriv] using hc
  have hinv : Tendsto (fun a => (n a : ℂ)⁻¹) p (𝓝 0) := by
    have hr : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using (hr.comp hn).ofReal
  have hsmall : Tendsto (fun a => v a / (n a : ℂ)) p (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hv.mul hinv
  have harg : Tendsto (fun a => v a * L (v a/(n a : ℂ))) p (𝓝 v₀) := by
    simpa only [mul_one,Function.comp_apply] using hv.mul (hL.comp hsmall)
  apply ((Complex.continuous_exp.tendsto _).comp harg).congr'
  have hne : ∀ᶠ a in p, 1+v a/(n a : ℂ) ≠ 0 :=
    (show Tendsto (fun a => 1+v a/(n a : ℂ)) p (𝓝 1) by simpa using hsmall.const_add 1).eventually_ne one_ne_zero
  filter_upwards [hn.eventually (eventually_ne_atTop 0),hne] with a ha hza
  have hnc : (n a : ℂ) ≠ 0 := by exact_mod_cast ha
  let z := v a / (n a : ℂ)
  have hlog : z * L z = Complex.log (1+z) := by
    simpa [L,f,smul_eq_mul] using sub_smul_dslope f 0 z
  change Complex.exp (v a * L z) = (1+z) ^ n a
  have he : v a * L z = (n a : ℂ) * Complex.log (1+z) := by
    rw [← hlog,← mul_assoc]
    congr 1
    dsimp [z]
    field_simp
  rw [he,Complex.exp_nat_mul,Complex.exp_log hza]

omit [Fintype V] in
private theorem coeff_cont {X : Type*} [TopologicalSpace X]
    (J : V → V → ℝ) (H : X → ComplexPartition.Field V) (hH : ∀ x i, Continuous (fun z => H z x i))
    (i : Labels V) : Continuous (fun p : X × Config V => coefficient J (H p.1) i p.2) := by
  cases i with
  | inl q => rcases q with ⟨x,y⟩; unfold coefficient; fun_prop
  | inr x =>
    exact continuous_finsetSum _ fun j _ => ((hH x j).comp continuous_fst).mul (by fun_prop)

private theorem uniform_weights {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (J : V → V → ℝ) (H : X → ComplexPartition.Field V) (hH : ∀ x i, Continuous (fun z => H z x i)) :
    TendstoUniformly (fun n (p : X × Config V) => eulerWeight J (H p.1) n p.2)
      (fun p => (Real.exp (offset J) : ℂ) * weight J (H p.1) p.2) atTop := by
  simp_rw [← exp_coefficients]
  apply tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro p
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 p
  have hcon (i : Labels V) : Tendsto (fun z : ℕ × (X × Config V) =>
      coefficient J (H z.2.1) i z.2.2) l (𝓝 (coefficient J (H p.1) i p.2)) :=
    ((coeff_cont J H hH i).tendsto _).comp tendsto_snd
  let v₀ := ∏ i : Labels V, Complex.exp (coefficient J (H p.1) i p.2)
  have hlim : Tendsto (fun z : ℕ × X × Config V =>
      ∏ i : Labels V, Complex.exp (coefficient J (H z.2.1) i z.2.2)) l (𝓝 v₀) :=
    tendsto_finsetProd _ fun i _ => (Complex.continuous_exp.tendsto _).comp (hcon i)
  have heul : Tendsto (fun z : ℕ × X × Config V => eulerWeight J (H z.2.1) z.1 z.2.2) l (𝓝 v₀) :=
    tendsto_finsetProd _ fun i _ => euler_tendsto tendsto_fst (hcon i)
  exact (hlim.prodMk_nhds heul).mono_right (nhds_le_uniformity v₀)

private theorem euler_continuous (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) :
    Continuous (eulerWeight J H n) := by
  apply continuous_finsetProd
  intro i _
  have hc := (coeff_cont J (X := Unit) (fun _ => H) (fun _ _ => continuous_const) i).comp
    (continuous_const.prodMk continuous_id : Continuous (fun s : Config V => ((),s)))
  exact (continuous_const.add (hc.div_const _)).pow n

private theorem uniform_integrals {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (J : V → V → ℝ) (H : X → ComplexPartition.Field V) (hH : ∀ x i, Continuous (fun z => H z x i)) :
    TendstoUniformly (fun n z => approximant J (H z) n)
      (fun z => (Real.exp (offset J) : ℂ) * partition J (H z)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp (uniform_weights J H hH)) (ε/2) (half_pos hε)
  filter_upwards [h] with n hn
  intro z
  have h1 : Integrable (fun s => (Real.exp (offset J) : ℂ) * weight J (H z) s) (surfaceProduct V) :=
    ((weight J (H z)).continuous.const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (eulerWeight J (H z) n) (surfaceProduct V) :=
    (euler_continuous J (H z) n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change dist ((Real.exp (offset J) : ℂ) * ∫ s, weight J (H z) s ∂surfaceProduct V)
    (∫ s, eulerWeight J (H z) n s ∂surfaceProduct V) < ε
  rw [dist_eq_norm,← integral_const_mul,← integral_sub h1 h2]
  have bd := norm_integral_le_of_norm_le_const (ae_of_all (surfaceProduct V)
    (fun s => (show ‖(Real.exp (offset J) : ℂ)*weight J (H z) s-eulerWeight J (H z) n s‖ < ε/2 by
      simpa only [dist_eq_norm] using hn (z,s)).le))
  simp only [probReal_univ,mul_one] at bd
  exact bd.trans_lt (half_lt_self hε)

/-- Locally uniform on the full complex parameter plane of an arbitrary
finite-graph affine family, before enforcing any Lee–Yang cone restriction. -/
theorem locallyUniform_approximant_affine (J : V → V → ℝ) (H D : ComplexPartition.Field V) :
    TendstoLocallyUniformly (fun n z => approximant J (affine H D z) n)
      (fun z => (Real.exp (offset J) : ℂ) * partition J (affine H D z)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  exact uniform_integrals J (fun z : K => affine H D z.val) (fun x i => by unfold affine; fun_prop)

private def realCoefficient (J : V → V → ℝ) (a : ℝ) : Labels V → Config V → ℝ
  | .inl (x,y), s => J x y / 2 * (1 + ⟪(s x).val,(s y).val⟫_ℝ)
  | .inr x, s => siteField a (s x)

omit [Fintype V] in
private theorem coeff_uniform (J : V → V → ℝ) (a : ℝ) (i : Labels V) (s : Config V) :
    coefficient J (uniform (a : ℂ)) i s = (realCoefficient J a i s : ℂ) := by
  cases i with
  | inl q => rcases q with ⟨x,y⟩; rfl
  | inr x => simp [coefficient,realCoefficient,uniform,siteField,ite_mul]

/-- Strict positive real part at the real uniform anchor for every n larger
than the field strength. The bound holds for every nonnegative coupling matrix. -/
theorem approximant_uniform_real_pos (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y)
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (han : a < (n : ℝ)) :
    0 < (approximant J (uniform (a : ℂ)) n).re := by
  let f (s : Config V) : ℝ := ∏ i : Labels V, (1 + realCoefficient J a i s / (n : ℝ))^n
  have hne : 0 < (n : ℝ) := lt_of_le_of_lt ha han
  have hc : Continuous f := by
    apply continuous_finsetProd
    intro i _
    apply Continuous.pow
    apply Continuous.add continuous_const
    apply Continuous.div_const
    cases i with
    | inl q => rcases q with ⟨x,y⟩; unfold realCoefficient; fun_prop
    | inr x => unfold realCoefficient siteField; fun_prop
  have hp (s : Config V) : 0 < f s := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    cases i with
    | inl q =>
      rcases q with ⟨x,y⟩
      have hdot : |⟪(s x).val,(s y).val⟫_ℝ| ≤ 1 := by
        simpa [Real.norm_eq_abs,norm_eq_of_mem_sphere] using norm_inner_le_norm (𝕜 := ℝ) (s x).val (s y).val
      have hdot' : 0 ≤ 1 + ⟪(s x).val,(s y).val⟫_ℝ := by linarith [(abs_le.mp hdot).1]
      change 0 < 1 + (J x y / 2 * (1+⟪(s x).val,(s y).val⟫_ℝ)) / (n : ℝ)
      positivity [hJ x y]
    | inr x =>
      have hx := abs_siteField_le a (s x)
      rw [abs_of_nonneg ha] at hx
      have hneg := (abs_le.mp hx).1
      change 0 < 1 + siteField a (s x) / (n : ℝ)
      rw [add_div' _ _ _ hne.ne', one_mul, div_pos_iff_of_pos_right hne]
      linarith
  have hw (s : Config V) : eulerWeight J (uniform (a : ℂ)) n s = (f s : ℂ) := by
    simp [f,eulerWeight, coeff_uniform]
  unfold approximant
  simp_rw [hw]
  rw [integral_complex_ofReal]
  apply (integral_pos_iff_support_of_nonneg (fun s => (hp s).le)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have hs : Function.support f = Set.univ := by ext s; simp [(hp s).ne']
  simp [hs]

/-- The two real anchor values and the locally uniform outer limit for the
actual Euler integrals used in the two Hurwitz steps, starting at field one. -/
theorem real_anchor_hurwitz_data (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y)
    (D : ComplexPartition.Field V) (U : Set ℂ) :
    partition J (uniform 1) ≠ 0 ∧
    (∀ᶠ n : ℕ in atTop, approximant J (affine (uniform 1) D 0) n ≠ 0) ∧
    TendstoLocallyUniformlyOn (fun n z => approximant J (affine (uniform 1) D z) n)
      (fun z => (Real.exp (offset J) : ℂ) * partition J (affine (uniform 1) D z)) atTop U := by
  have r : 0 < (partition J (uniform 1)).re := by simpa using partition_uniform_real_pos J 1
  have h0 : affine (uniform (V := V) 1) D 0 = uniform 1 := by funext x j; simp [affine]
  refine ⟨fun h => by simp [h] at r, ?_, (locallyUniform_approximant_affine J (uniform 1) D).tendstoLocallyUniformlyOn⟩
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < (approximant J (uniform 1) n).re := by
    simpa using approximant_uniform_real_pos J hJ 1 zero_le_one n hn'
  rw [h0]
  intro h
  simp [h] at hr

end IsingScaling.Rotor.HeisenbergField.ClassicalEuler
