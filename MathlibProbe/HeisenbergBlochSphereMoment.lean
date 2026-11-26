import MathlibProbe.RotorHeisenbergSingleSiteLeeYang
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Coherent-state resolution on the physical Heisenberg sphere

Write the three spin components in the order z, x, y. A bit equal to false
labels an up spin. For the rank-one projection P = (1 + S·σ)/2, a rotation
by a unit phase ζ around the z axis multiplies P₁₀ by ζ and P₀₁ by its
inverse. Consequently the tensor matrix element indexed by I,J, after
integration, satisfies ζ^|J| M = ζ^|I| M. Taking a primitive (d+1)-st
root gives zero when the weights differ.

Under equal weights the product contains equally many P₀₁ and P₁₀.
The unit sphere identity P₀₁ P₁₀ = P₀₀ P₁₁ leaves precisely
P₁₁^k P₀₀^(d-k), where k is the common weight. The axial sphere integral
is k! (d-k)!/(d+1)!. Thus the moment matrix is the symmetric projection
divided by d+1.
-/

noncomputable section

open MeasureTheory Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace IsingScaling.Rotor.HeisenbergField.BlochSphere

private abbrev V := EuclideanSpace ℝ (Fin 3)
private abbrev θ := SiteReflection.surfacePrior 3

def up (s : Spin 3) : ℝ := (1+s.val 0)/2
def down (s : Spin 3) : ℝ := (1-s.val 0)/2
def minus (s : Spin 3) : ℂ := ((s.val 1 : ℂ)-(s.val 2 : ℂ)*Complex.I)/2
def plus (s : Spin 3) : ℂ := ((s.val 1 : ℂ)+(s.val 2 : ℂ)*Complex.I)/2

/-- Entries of the physical two-state projection in the σz eigenbasis. -/
def entry (s : Spin 3) : Bool → Bool → ℂ
  | false, false => up s
  | false, true  => minus s
  | true, false  => plus s
  | true, true   => down s

/-- The physical projector has trace one. -/
theorem trace_entry (s : Spin 3) : entry s false false + entry s true true = 1 := by
  simp only [entry, up, down]
  push_cast
  ring

theorem z_component (s : Spin 3) :
    entry s false false - entry s true true = (s.val 0 : ℂ) := by
  simp only [entry, up, down]
  push_cast
  ring

theorem x_component (s : Spin 3) :
    entry s true false + entry s false true = (s.val 1 : ℂ) := by
  simp only [entry, plus, minus]
  ring

theorem y_component (s : Spin 3) :
    Complex.I * (entry s false true - entry s true false) = (s.val 2 : ℂ) := by
  simp only [entry, minus, plus]
  linear_combination -(s.val 2 : ℂ) * Complex.I_sq

/-- Resolving a single transposition against the two physical coherent states
gives the classical Heisenberg dot interaction, with its scalar constant. -/
theorem two_trace_entry_mul (s t : Spin 3) :
    2 * (∑ i : Bool, ∑ j : Bool, entry s i j * entry t j i) =
      1 + (⟪s.val,t.val⟫_ℝ : ℂ) := by
  simp only [Fintype.sum_bool, entry, up, down, minus, plus, PiLp.inner_apply,
    Real.inner_apply, Fin.sum_univ_three]
  push_cast
  linear_combination -(s.val 2 : ℂ) * (t.val 2 : ℂ) * Complex.I_sq

/-- Number of down spins in the labelled word. -/
def weight {d : ℕ} (I : Fin d → Bool) : ℕ := ∑ k, (I k).toNat

def tensorEntry {d : ℕ} (I J : Fin d → Bool) (s : Spin 3) : ℂ :=
  ∏ k, entry s (I k) (J k)

/-- The sites in this moment are tensor copies of one spin, integrated once. -/
def tensorMoment {d : ℕ} (I J : Fin d → Bool) : ℂ :=
  ∫ s : Spin 3, tensorEntry I J s ∂θ

private theorem sq_transverse (s : Spin 3) :
    (s.val 0)^2 + (s.val 1)^2 + (s.val 2)^2 = 1 := by
  have h := (EuclideanSpace.real_norm_sq_eq s.val).symm
  simpa only [Fin.sum_univ_three, mem_sphere_zero_iff_norm.mp s.property, one_pow] using h

theorem minus_mul_plus (s : Spin 3) :
    minus s * plus s = (up s : ℂ) * (down s : ℂ) := by
  have h : (s.val 0 : ℂ)^2+(s.val 1 : ℂ)^2+(s.val 2 : ℂ)^2=1 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] using
      congrArg Complex.ofReal (sq_transverse s)
  unfold minus plus up down
  push_cast
  linear_combination h / 4 - (s.val 2 : ℂ)^2 / 4 * Complex.I_sq

private def rotateRaw (ζ : ℂ) (x : V) : V :=
  WithLp.toLp 2 ![x 0, ζ.re*x 1-ζ.im*x 2, ζ.im*x 1+ζ.re*x 2]

private def rotateLinear (ζ : ℂ) : V →ₗ[ℝ] V where
  toFun := rotateRaw ζ
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rotateRaw] <;> ring
  map_smul' t x := by
    ext i
    fin_cases i <;> simp [rotateRaw] <;> ring

private theorem unit_coords {ζ : ℂ} (hz : ‖ζ‖=1) : ζ.re^2 + ζ.im^2=1 := by
  have h := Complex.sq_norm ζ
  rw [hz, one_pow, Complex.normSq_apply] at h
  nlinarith

private def rotate (ζ : ℂ) (hz : ‖ζ‖ = 1) : V ≃ₗᵢ[ℝ] V :=
  let f : V →ₗᵢ[ℝ] V :=
    { toLinearMap := rotateLinear ζ
      norm_map' := fun x => by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          Fin.sum_univ_three, Fin.sum_univ_three]
        change (x 0)^2 + (ζ.re*x 1-ζ.im*x 2)^2 + (ζ.im*x 1+ζ.re*x 2)^2 =
          (x 0)^2 + (x 1)^2 + (x 2)^2
        linear_combination ((x 1)^2 + (x 2)^2) * unit_coords hz }
  f.toLinearIsometryEquiv rfl

private abbrev spinRotate (ζ : ℂ) (hz : ‖ζ‖=1) :=
  SiteReflection.SphereSign.sphereMap (rotate ζ hz)

private theorem gauge {ζ : ℂ} (hz : ‖ζ‖=1) (s : Spin 3) (i j : Bool) :
    entry (spinRotate ζ hz s) i j * ζ^j.toNat = ζ^i.toNat * entry s i j := by
  have h : ((ζ.re : ℂ)^2+(ζ.im : ℂ)^2)=1 := by exact_mod_cast unit_coords hz
  have hzform := (Complex.re_add_im ζ).symm
  cases i <;> cases j
  · change (up s : ℂ) * ζ^0 = ζ^0 * (up s : ℂ)
    exact mul_comm ..
  · change (((ζ.re*s.val 1-ζ.im*s.val 2 : ℝ) : ℂ) -
        ((ζ.im*s.val 1+ζ.re*s.val 2 : ℝ) : ℂ)*Complex.I)/2*ζ^1 =
        ζ^0*(((s.val 1:ℂ)-(s.val 2:ℂ)*Complex.I)/2)
    simp only [pow_one, pow_zero, one_mul]
    conv_lhs => rhs; rw [hzform]
    push_cast
    linear_combination ((s.val 1:ℂ)-(s.val 2:ℂ)*Complex.I)/2 * h -
      ((ζ.im:ℂ)*(s.val 1:ℂ)+(ζ.re:ℂ)*(s.val 2:ℂ))*(ζ.im:ℂ)/2 * Complex.I_sq
  · change (((ζ.re*s.val 1-ζ.im*s.val 2 : ℝ) : ℂ) +
        ((ζ.im*s.val 1+ζ.re*s.val 2 : ℝ) : ℂ)*Complex.I)/2*ζ^0 =
        ζ^1*(((s.val 1:ℂ)+(s.val 2:ℂ)*Complex.I)/2)
    simp only [pow_one,pow_zero,mul_one]
    conv_rhs => lhs; rw [hzform]
    push_cast
    linear_combination -((ζ.im:ℂ)*(s.val 2:ℂ))/2 * Complex.I_sq
  · change (down s : ℂ) * ζ^1 = ζ^1 * (down s : ℂ)
    exact mul_comm ..

theorem tensorMoment_gauge {d : ℕ} (I J : Fin d → Bool) {ζ : ℂ} (hz : ‖ζ‖=1) :
    tensorMoment I J * ζ^(weight J) = ζ^(weight I) * tensorMoment I J := by
  have hprod (s : Spin 3) :
      tensorEntry I J (spinRotate ζ hz s) * ζ^(weight J) =
        ζ^(weight I) * tensorEntry I J s := by
    have h := Finset.prod_congr (s₁ := Finset.univ) rfl (fun k _ => gauge hz s (I k) (J k))
    simpa only [tensorEntry, weight, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] using h
  have mp := (SiteReflection.SphereSign.sphereMap_preserving (rotate ζ hz)).integral_comp'
    (tensorEntry I J)
  unfold tensorMoment
  calc
    _ = (∫ s : Spin 3, tensorEntry I J (spinRotate ζ hz s) ∂θ) * ζ^(weight J) :=
      congrArg (fun v : ℂ => v * _) mp.symm
    _ = ∫ s : Spin 3, tensorEntry I J (spinRotate ζ hz s) * ζ^(weight J) ∂θ :=
      (integral_mul_const _ _).symm
    _ = ∫ s : Spin 3, ζ^(weight I) * tensorEntry I J s ∂θ :=
      integral_congr_ae (.of_forall hprod)
    _ = _ := integral_const_mul ..

theorem weight_le {d : ℕ} (I : Fin d → Bool) : weight I ≤ d := by
  calc weight I ≤ ∑ _ : Fin d, 1 := Finset.sum_le_sum (fun k _ => by cases I k <;> decide)
       _ = d := by simp

theorem tensorMoment_zero_of_weight_ne {d : ℕ} (I J : Fin d → Bool)
    (hne : weight I ≠ weight J) : tensorMoment I J = 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (d+1 : ℕ))
  have hζ : IsPrimitiveRoot ζ (d+1) := Complex.isPrimitiveRoot_exp _ (by omega)
  have h := tensorMoment_gauge I J (hζ.norm'_eq_one (by omega))
  by_contra hm
  rw [mul_comm (tensorMoment I J)] at h
  exact hne (hζ.pow_inj (Nat.lt_succ_of_le (weight_le I)) (Nat.lt_succ_of_le (weight_le J))
    (mul_right_cancel₀ hm h.symm))

private def multiplicity {d : ℕ} (I J : Fin d → Bool) (i j : Bool) : ℕ :=
  ∑ k, if I k = i ∧ J k = j then 1 else 0

private theorem sum_multiplicities {d : ℕ} (I J : Fin d → Bool) :
    multiplicity I J false false + multiplicity I J false true +
      multiplicity I J true false + multiplicity I J true true = d := by
  calc _ = ∑ _ : Fin d, (1 : ℕ) := by
         unfold multiplicity
         simp only [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro k _
         cases I k <;> cases J k <;> decide
       _ = _ := by simp

private theorem row_weight {d : ℕ} (I J : Fin d → Bool) :
    multiplicity I J true false + multiplicity I J true true = weight I := by
  simp only [multiplicity, weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases I k <;> cases J k <;> decide

private theorem column_weight {d : ℕ} (I J : Fin d → Bool) :
    multiplicity I J false true + multiplicity I J true true = weight J := by
  simp only [multiplicity, weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases I k <;> cases J k <;> decide

private theorem factor_tensorEntry {d : ℕ} (I J : Fin d → Bool) (s : Spin 3) :
    tensorEntry I J s = (up s : ℂ)^(multiplicity I J false false) *
      (minus s)^(multiplicity I J false true) *
      (plus s)^(multiplicity I J true false) *
      (down s : ℂ)^(multiplicity I J true true) := by
  let p (i j : Bool) (k : Fin d) : ℕ := if I k = i ∧ J k = j then 1 else 0
  calc tensorEntry I J s = ∏ k, ((up s : ℂ)^(p false false k) *
      (minus s)^(p false true k) * (plus s)^(p true false k) * (down s : ℂ)^(p true true k)) := by
         apply Finset.prod_congr rfl
         intro k _
         cases hi : I k <;> cases hj : J k <;> simp [p,hi,hj,entry]
       _ = _ := by
         simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, p, multiplicity]

/-- Equal-weight tensor entries reduce pointwise on the physical sphere to
a single real beta monomial. This includes the poles, where the off-diagonal
spin-coherent coordinates vanish. -/
theorem tensorEntry_eq_axial_of_weight_eq {d : ℕ} (I J : Fin d → Bool)
    (h : weight I = weight J) (s : Spin 3) :
    tensorEntry I J s = (((down s)^(weight I) * (up s)^(d-weight I) : ℝ) : ℂ) := by
  let a := multiplicity I J false false
  let b := multiplicity I J false true
  let c := multiplicity I J true false
  let e := multiplicity I J true true
  have habce : a+b+c+e=d := sum_multiplicities I J
  have hrow : c+e=weight I := row_weight I J
  have hcol : b+e=weight J := column_weight I J
  have hcb : c=b := by omega
  have hab : d-weight I = a+b := by omega
  have hbe : weight I = b+e := by omega
  rw [factor_tensorEntry, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
  change (up s : ℂ)^a * minus s^b * plus s^c * (down s : ℂ)^e =
    (down s : ℂ)^(weight I) * (up s : ℂ)^(d-weight I)
  rw [hcb, hab, hbe]
  calc _ = (up s : ℂ)^a * (minus s * plus s)^b * (down s : ℂ)^e := by rw [mul_pow]; ring
       _ = _ := by rw [minus_mul_plus, mul_pow, pow_add, pow_add]; ring

/-- Exact balanced entry before applying the scalar axial moment formula. -/
theorem tensorMoment_eq_axial_of_weight_eq {d : ℕ} (I J : Fin d → Bool) (h : weight I=weight J) :
    tensorMoment I J = ((∫ s : Spin 3, down s^(weight I) * up s^(d-weight I) ∂θ : ℝ) : ℂ) := by
  unfold tensorMoment
  simp_rw [tensorEntry_eq_axial_of_weight_eq I J h, integral_complex_ofReal]

private theorem factorial_div_eq_choose {d k : ℕ} (hk : k ≤ d) :
    (k.factorial : ℂ) * ((d-k).factorial : ℂ) / ((k+(d-k)+1).factorial : ℂ) =
      1 / (((d : ℂ)+1) * (d.choose k : ℂ)) := by
  have hcomb : (d.choose k : ℂ) * (k.factorial : ℂ) * ((d-k).factorial : ℂ) =
      (d.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hdf : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero d)
  have hc : (d.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hd : (d : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  rw [show k+(d-k)=d by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  apply (div_eq_div_iff (mul_ne_zero hd hdf) (mul_ne_zero hd hc)).mpr
  calc _ = ((d : ℂ)+1)*((d.choose k : ℂ)*(k.factorial : ℂ)*((d-k).factorial : ℂ)) := by ring
       _ = _ := by rw [hcomb, one_mul]

/-- The actual normalized S² integral in the ordered computational basis.
It equals the matrix element of the symmetric projector divided by d+1. -/
theorem tensorMoment_eq {d : ℕ} (I J : Fin d → Bool) :
    tensorMoment I J = if weight I = weight J then
      1 / (((d : ℂ)+1) * (d.choose (weight I) : ℂ)) else 0 := by
  by_cases h : weight I = weight J
  · rw [ite_eq_left h, tensorMoment_eq_axial_of_weight_eq I J h]
    unfold up down
    rw [SingleSiteLeeYang.bernoulli_axis_mixed]
    push_cast
    exact factorial_div_eq_choose (weight_le I)
  · rw [ite_eq_right h, tensorMoment_zero_of_weight_ne I J h]

#print axioms two_trace_entry_mul
#print axioms tensorMoment_eq

end IsingScaling.Rotor.HeisenbergField.BlochSphere
