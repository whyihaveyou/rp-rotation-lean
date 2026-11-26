import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Sequences
import MathlibProbe.RotorObliqueTestPolynomials

/-! # Resolvent variations on the physical cosine cube

Fix mass one and write a=(2a_nn,4a_face,8a_body). The rational cone
used below lies in the strict mass-gap and positive mirror-crossing
region. A derivative in coordinate i of an inverse power multiplies it
by the elementary polynomial e_i and raises the inverse power by one.
All difference quotients are limits of linear combinations of the
permitted squared resolvents. The mass-one kernels tend uniformly to one
as their walk weights decrease to zero within the cone. This extracts
the actual elementary-coordinate monomials, with uniform closure
throughout the calculation.
-/

noncomputable section
open Filter Set Finset
open scoped Topology
namespace MathlibProbe.RotorResolventTestApproximation
open RotorObliqueTestPolynomials

abbrev CosineCube := Fin 3 → Set.Icc (-1:ℝ) 1
abbrev Alg := C(CosineCube, ℝ)
abbrev Parameter := Fin 3 → ℝ

def coord (i : Fin 3) : Alg :=
  ⟨fun x => (x i : ℝ), continuous_subtype_val.comp (continuous_apply i)⟩

def elem : Fin 3 → Alg :=
  ![coord 0+coord 1+coord 2, coord 0*coord 1+coord 0*coord 2+coord 1*coord 2,
    coord 0*coord 1*coord 2]

def symbol (p : Parameter) : Alg := ∑ i, p i • elem i

def Good (p : Parameter) : Prop :=
  0 < p 2 ∧ p 2 < p 1 ∧ 2*p 1+p 2 < p 0 ∧ 3*p 0+3*p 1+p 2 < 1

private theorem good_open : IsOpen {p | Good p} := by
  change IsOpen ({p : Parameter | 0 < p 2} ∩
    ({p : Parameter | p 2 < p 1} ∩
      ({p : Parameter | 2*p 1+p 2 < p 0} ∩ {p : Parameter | 3*p 0+3*p 1+p 2 < 1})))
  repeat' apply IsOpen.inter
  all_goals apply isOpen_lt <;> fun_prop

private theorem symbol_continuous : Continuous symbol := by unfold symbol; fun_prop

private theorem coord_abs (x : CosineCube) (i : Fin 3) : |coord i x| ≤ 1 :=
  abs_le.mpr (x i).property

private theorem elem_bounds (x : CosineCube) :
    elem 0 x ≤ 3 ∧ elem 1 x ≤ 3 ∧ elem 2 x ≤ 1 := by
  have hc (i : Fin 3) : coord i x ≤ 1 := (abs_le.mp (coord_abs x i)).2
  have hp (i j : Fin 3) : |coord i x*coord j x| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (coord_abs x i) (coord_abs x j) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hpair (i j : Fin 3) : coord i x*coord j x ≤ 1 := (abs_le.mp (hp i j)).2
  have htriple : |coord 0 x*coord 1 x*coord 2 x| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (hp 0 1) (coord_abs x 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  change coord 0 x+coord 1 x+coord 2 x ≤ 3 ∧
    coord 0 x*coord 1 x+coord 0 x*coord 2 x+coord 1 x*coord 2 x ≤ 3 ∧ _
  exact ⟨by linarith [hc 0,hc 1,hc 2], by linarith [hpair 0 1,hpair 0 2,hpair 1 2],
    (abs_le.mp htriple).2⟩

private theorem gap {p : Parameter} (hp : Good p) : (1:ℝ) ∈ resolventSet ℝ (symbol p) := by
  change IsUnit (algebraMap ℝ Alg 1 - symbol p)
  rw [ContinuousMap.isUnit_iff_forall_ne_zero]
  intro x
  obtain ⟨h₂,h₁,h₀,hM⟩ := hp
  obtain ⟨b₀,b₁,b₂⟩ := elem_bounds x
  have hpos₁ : 0 ≤ p 1 := by linarith
  have hpos₀ : 0 ≤ p 0 := by linarith
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left b₀ hpos₀)
    (mul_le_mul_of_nonneg_left b₁ hpos₁)) (mul_le_mul_of_nonneg_left b₂ h₂.le)
  simp only [symbol, Fin.sum_univ_three,ContinuousMap.sub_apply,ContinuousMap.add_apply,
    ContinuousMap.smul_apply,smul_eq_mul,map_one,ContinuousMap.one_apply]
  linarith only [h,hM]

def R (p : Parameter) : Alg := resolvent (symbol p) (1:ℝ)

/-- Only rational admissible walk coefficients occur among the
generators, with physical mass M fixed at one. -/
def gens : Set Alg := {f | ∃ a : Fin 3 → ℚ, Good (fun i => (a i:ℝ)) ∧
  f = R (fun i => (a i:ℝ)) ^ 2}

def V : Submodule ℝ Alg := (Submodule.span ℝ gens).topologicalClosure

private theorem r_cont {p : Parameter} (hp : (1:ℝ) ∈ resolventSet ℝ (symbol p)) :
    ContinuousAt R p :=
  (spectrum.hasFDerivAt_resolvent (𝕜 := ℝ) hp).continuousAt.comp symbol_continuous.continuousAt

private theorem real_generator {p : Parameter} (hp : Good p) : R p ^ 2 ∈ V := by
  let rat (a : Fin 3 → ℚ) : Parameter := fun i => (a i:ℝ)
  have hd : DenseRange rat := DenseRange.piMap (fun _ : Fin 3 => Rat.denseRange_cast)
  obtain ⟨a',hmem,ha'⟩ := mem_closure_iff_seq_limit.mp (hd p)
  choose a hab using hmem
  have ha : Tendsto (fun n => rat (a n)) atTop (𝓝 p) := by simpa only [hab] using ha'
  have hgood : ∀ᶠ n in atTop, Good (rat (a n)) := ha (good_open.mem_nhds hp)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (((r_cont (gap hp)).pow 2).tendsto.comp ha)
  filter_upwards [hgood] with n hn
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨a n,hn,rfl⟩

private theorem symbol_shift (a : Parameter) (i : Fin 3) (t : ℝ) :
    symbol (a+Pi.single i t) = symbol a + t • elem i := by
  classical
  simp [symbol, Pi.add_apply,Pi.single_apply,add_smul,Finset.sum_add_distrib,
    ite_smul]

private theorem slope_mem_closed {F : ℝ → Alg} {b : Alg} (h : HasDerivAt F b 0)
    (hi : ∀ᶠ t in 𝓝 (0:ℝ), F t ∈ V) : b ∈ V := by
  have h₀ := mem_of_mem_nhds hi
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h.tendsto_slope
  filter_upwards [hi.filter_mono nhdsWithin_le_nhds] with t ht
  rw [slope_def_module]
  exact V.smul_mem _ (V.sub_mem ht h₀)

private theorem resolvent_directional (a : Parameter) (ha : Good a) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => R (a+Pi.single i t)) (R a ^ 2 * elem i) 0 := by
  have hD : HasDerivAt (fun t : ℝ => symbol a + t • elem i) (elem i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (elem i)).const_add (symbol a)
  have hr := (spectrum.hasFDerivAt_resolvent (𝕜 := ℝ) (gap ha)).comp_hasDerivAt_of_eq
    0 hD (by simp)
  simp only [Function.comp_def] at hr
  simp only [R,symbol_shift]
  apply hr.congr_deriv
  simp [ContinuousLinearMap.mulLeftRight_apply, sq] <;> ring

private theorem monomial_resolvent (l : List (Fin 3)) (a : Parameter) (ha : Good a) :
    (l.map elem).prod * R a ^ (l.length+2) ∈ V := by
  induction l generalizing a with
  | nil => simpa using real_generator ha
  | cons i l ih =>
    let P := (l.map elem).prod
    let m := l.length+2
    have hm : (0:ℝ) < (m:ℝ) := by dsimp [m]; positivity
    let F (t : ℝ) : Alg := P * R (a+Pi.single i t)^m
    have hF : HasDerivAt F ((m:ℝ) • (P*elem i*R a^(m+1))) 0 := by
      have D := ((resolvent_directional a ha i).fun_pow m).const_mul P
      apply D.congr_deriv
      have hd : m-1+2 = m+1 := by dsimp only [m]; omega
      ext x
      simp only [Pi.single_zero,add_zero, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
        ContinuousMap.natCast_apply,ContinuousMap.pow_apply,smul_eq_mul]
      rw [← hd,pow_add]
      ring
    have hparam : Continuous (fun t : ℝ => a+Pi.single i t) := by
      apply continuous_const.add
      apply continuous_pi
      intro j
      by_cases hj : j = i <;> simp [hj] <;> fun_prop
    have hi : ∀ᶠ t in 𝓝 (0:ℝ), Good (a+Pi.single i t) :=
      hparam.continuousAt (good_open.mem_nhds (by simpa using ha))
    have H := slope_mem_closed hF (hi.mono fun t ht => ih _ ht)
    have H' := V.smul_mem ((m:ℝ)⁻¹) H
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hm.ne', one_smul] at H'
    simpa [m,P,add_assoc,mul_comm] using H'

private theorem ray_good {t : ℝ} (h₁ : 0 < t) (h₂ : t < 1/40) :
    Good ![10*t,3*t,t] := by
  change 0<t ∧ t<3*t ∧ 2*(3*t)+t<10*t ∧ 3*(10*t)+3*(3*t)+t<1
  exact ⟨h₁,by linarith,by linarith,by linarith⟩

theorem elementary_product_mem (l : List (Fin 3)) : (l.map elem).prod ∈ V := by
  let ray (t : ℝ) : Parameter := ![10*t,3*t,t]
  have hz : symbol 0 = 0 := by simp [symbol]
  have hR : R 0 = 1 := by simp [R,hz,resolvent]
  have hgap : (1:ℝ) ∈ resolventSet ℝ (symbol 0) := by
    change IsUnit (algebraMap ℝ Alg 1-symbol 0)
    simp [hz]
  have hray : Continuous ray := by
    apply continuous_pi; intro i; fin_cases i <;> dsimp [ray] <;> fun_prop
  have hzero : ray 0 = 0 := by ext i; fin_cases i <;> simp [ray]
  have ht : Tendsto ray (𝓝[>] (0:ℝ)) (𝓝 0) :=
    hzero ▸ hray.continuousAt.continuousWithinAt
  have hlat := (r_cont hgap).tendsto.comp ht
  rw [hR] at hlat
  have H := (tendsto_const_nhds (x := (l.map elem).prod)).mul (hlat.pow (l.length+2))
  simp only [one_pow,mul_one] at H
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto H
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1/40 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/40)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht₁ ht₂
  exact monomial_resolvent l _ (ray_good ht₁ ht₂)

/-- Evaluation of the Banach-algebra resolvent is the physical scalar symbol. -/
theorem R_apply_of_good (p : Parameter) (hp : Good p) (x : CosineCube) :
    R p x = (1 - symbol p x)⁻¹ := by
  have hm := congrArg (fun f : Alg => f x)
    (Ring.inverse_mul_cancel (algebraMap ℝ Alg 1 - symbol p) (gap hp))
  apply eq_inv_of_mul_eq_one_left
  simpa only [R,resolvent, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply,map_one] using hm

/-- In the manuscript's nearest-, face-, and body-diagonal coefficients, the
admissible cone includes exactly the stated inequalities at mass one. -/
theorem good_walk_coefficients_iff (a b c : ℝ) :
    Good ![2*a,4*b,8*c] ↔
      0 < c ∧ 2*c < b ∧ 4*b+4*c < a ∧ 6*a+12*b+8*c < 1 := by
  change (0 < 8*c ∧ 8*c < 4*b ∧ 2*(4*b)+8*c < 2*a ∧
    3*(2*a)+3*(4*b)+8*c < 1) ↔ _
  constructor <;> rintro ⟨h₁,h₂,h₃,h₄⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem symbol_apply (p : Parameter) (x : CosineCube) :
    symbol p x = p 0 * (coord 0 x+coord 1 x+coord 2 x)
      + p 1 * (coord 0 x*coord 1 x+coord 0 x*coord 2 x+coord 1 x*coord 2 x)
      + p 2 * (coord 0 x*coord 1 x*coord 2 x) := by
  simp only [symbol,Fin.sum_univ_three, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  rfl

def poly : Poly →+* Alg := MvPolynomial.eval₂Hom (algebraMap ℝ Alg) elem

private theorem poly_mul_product_mem (p : Poly) (l : List (Fin 3)) :
    poly p * (l.map elem).prod ∈ V := by
  induction p using MvPolynomial.induction_on generalizing l with
  | C c =>
      change MvPolynomial.eval₂Hom _ _ _ * _ ∈ _
      rw [MvPolynomial.eval₂Hom_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact V.smul_mem c (elementary_product_mem l)
  | add f g hf hg =>
      rw [map_add,add_mul]
      exact V.add_mem (hf l) (hg l)
  | mul_X f i hf =>
      rw [map_mul, mul_assoc]
      have hx : poly (MvPolynomial.X i) = elem i := MvPolynomial.eval₂Hom_X' _ _ _
      simpa only [hx,List.map_cons,List.prod_cons] using hf (i::l)

/-- Every elementary-coordinate polynomial is a uniform limit of finite
linear combinations of rational admissible squared resolvents. -/
theorem poly_mem (p : Poly) : poly p ∈ V := by simpa using poly_mul_product_mem p []

theorem poly_apply (p : Poly) (x : CosineCube) :
    poly p x = MvPolynomial.eval (elementary (coord 0 x) (coord 1 x) (coord 2 x)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [poly]
  | add f g hf hg => simp only [map_add, ContinuousMap.add_apply,hf,hg]
  | mul_X f i hf =>
      simp only [map_mul, ContinuousMap.mul_apply,hf,MvPolynomial.eval_X]
      congr 1
      change (MvPolynomial.eval₂Hom _ elem (MvPolynomial.X i)) x = _
      rw [MvPolynomial.eval₂Hom_X']
      fin_cases i <;> rfl

/-- The three physical first variations, with multipliers one, the third
coordinate cosine, and the product of the first two cosines. -/
def variations : Set Alg := {g | g ∈ gens ∨ (∃ f ∈ gens, g = coord 2 * f) ∨
    (∃ f ∈ gens, g = (coord 0 * coord 1) * f)}

private theorem strict_mul_mem {w : Alg} (h : ∀ f ∈ gens, w*f ∈ variations)
    {f : Alg} (hf : f ∈ Submodule.span ℝ gens) : w*f ∈ Submodule.span ℝ variations := by
  induction hf using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (h v hv)
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using (Submodule.span ℝ variations).add_mem hx hy
  | smul k x _ hx =>
      simpa only [mul_smul_comm] using (Submodule.span ℝ variations).smul_mem k hx

private theorem closure_mul_mem {w : Alg} (h : ∀ f ∈ gens, w*f ∈ variations)
    {f : Alg} (hf : f ∈ V) : w*f ∈ (Submodule.span ℝ variations).topologicalClosure := by
  let S := (Submodule.span ℝ variations).topologicalClosure
  have hc : IsClosed {z : Alg | w*z ∈ S} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)
  have hsub : (Submodule.span ℝ gens : Set Alg) ⊆ {z : Alg | w*z ∈ S} :=
    fun z hz => Submodule.le_topologicalClosure (Submodule.span ℝ variations) (strict_mul_mem h hz)
  exact (closure_minimal hsub hc) hf

/-- Uniform approximation of the horizontally symmetric three-coefficient
polynomial by the linear span of *physical* variations on the full cube. -/
theorem approximate_three_polynomials (a b c : Poly) {ε : ℝ} (hε : 0 < ε) :
    ∃ F ∈ Submodule.span ℝ variations, ∀ x : CosineCube,
    |(MvPolynomial.eval (elementary (coord 0 x) (coord 1 x) (coord 2 x)) a +
      coord 2 x * MvPolynomial.eval (elementary (coord 0 x) (coord 1 x) (coord 2 x)) b +
      (coord 0 x*coord 1 x) * MvPolynomial.eval (elementary (coord 0 x) (coord 1 x) (coord 2 x)) c)
      - F x| < ε := by
  let S := (Submodule.span ℝ variations).topologicalClosure
  have ha : poly a ∈ S := by
    simpa only [one_mul] using closure_mul_mem (w := 1)
      (fun f hf => Or.inl (by simpa only [one_mul] using hf)) (poly_mem a)
  have hb : coord 2 * poly b ∈ S :=
    closure_mul_mem (fun f hf => Or.inr (Or.inl ⟨f,hf,rfl⟩)) (poly_mem b)
  have hc : (coord 0*coord 1) * poly c ∈ S :=
    closure_mul_mem (fun f hf => Or.inr (Or.inr ⟨f,hf,rfl⟩)) (poly_mem c)
  let T := poly a + coord 2 * poly b + (coord 0*coord 1) * poly c
  have hT : T ∈ closure (Submodule.span ℝ variations : Set Alg) := S.add_mem (S.add_mem ha hb) hc
  obtain ⟨F,hF,hnear⟩ := Metric.mem_closure_iff.mp hT ε hε
  refine ⟨F,hF,fun x => ?_⟩
  have hnorm : ‖T - F‖ < ε := by
    simpa only [dist_eq_norm,norm_sub_rev F T] using hnear
  have h := ((T-F).norm_coe_le_norm x).trans_lt hnorm
  simpa only [T,ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.sub_apply,
    Real.norm_eq_abs, poly_apply] using h

private def coordinates : Poly →ₐ[ℝ] Alg := MvPolynomial.aeval coord

private theorem coordinates_separate : coordinates.range.SeparatesPoints := by
  intro x y hxy
  have hh : ∃ i : Fin 3, coord i x ≠ coord i y := by
    by_contra! h
    apply hxy
    funext i
    exact Subtype.ext (h i)
  obtain ⟨i,hi⟩ := hh
  refine ⟨(coord i : CosineCube → ℝ),
    ⟨coord i,⟨MvPolynomial.X i,?_⟩,rfl⟩,hi⟩
  exact MvPolynomial.aeval_X _ _

def swapCube (x : CosineCube) : CosineCube := ![x 1, x 0, x 2]

private theorem coords_apply (p : Poly) (x : CosineCube) :
    coordinates p x = MvPolynomial.eval
      (RotorObliqueTestPolynomials.nodes (coord 0 x) (coord 1 x) (coord 2 x)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [coordinates]
  | add f g hf hg => simp only [map_add,ContinuousMap.add_apply,hf,hg]
  | mul_X f i hf =>
      simp only [map_mul,ContinuousMap.mul_apply,hf,MvPolynomial.eval_X]
      congr 1
      change (MvPolynomial.aeval coord (MvPolynomial.X i : Poly)) x = _
      rw [MvPolynomial.aeval_X]
      fin_cases i <;> rfl

/-- The physical mass-one variations uniformly approximate every continuous
cosine-cube test invariant under the horizontal swap. -/
theorem approximate_symmetric_continuous (T : Alg)
    (hT : ∀ x, T (swapCube x) = T x) {ε : ℝ} (hε : 0 < ε) :
    ∃ F ∈ Submodule.span ℝ variations, ∀ x : CosineCube, |T x - F x| < ε := by
  obtain ⟨⟨P,⟨p,hp⟩⟩,hn⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      coordinates.range coordinates_separate T (ε/2) (by linarith)
  subst P
  have hp' (x : CosineCube) : |coordinates p x - T x| < ε/2 := by
    exact ((coordinates p - T).norm_coe_le_norm x).trans_lt hn
  obtain ⟨a,b,c,he⟩ := averaged_test_representation p
  obtain ⟨F,hF,hF'⟩ := approximate_three_polynomials a b c
    (ε := ε/2) (by linarith)
  refine ⟨F,hF,fun x => ?_⟩
  have hx := hp' x
  have hs := hp' (swapCube x)
  rw [hT] at hs
  have hpt := hF' x
  rw [← he] at hpt
  have hes : coordinates p (swapCube x) =
      MvPolynomial.eval
        (RotorObliqueTestPolynomials.nodes (coord 1 x) (coord 0 x) (coord 2 x)) p :=
    coords_apply p (swapCube x)
  rw [← coords_apply, ← hes] at hpt
  rcases abs_lt.mp hx with ⟨hx₁,hx₂⟩
  rcases abs_lt.mp hs with ⟨hs₁,hs₂⟩
  rcases abs_lt.mp hpt with ⟨hf₁,hf₂⟩
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

#print axioms elementary_product_mem
#print axioms approximate_three_polynomials

end MathlibProbe.RotorResolventTestApproximation
