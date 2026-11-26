import MathlibProbe.RotorPeriodicSpectralTest
import MathlibProbe.RotorObliqueTestPolynomials
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! The actual real character at each reflected lattice displacement,
after averaging over independent coordinate inversions, is the product
of three one-variable Chebyshev polynomials. The remaining horizontal
swap selects precisely the symmetric cosine polynomial of the rotor
resolvent argument. -/

noncomputable section
open Finset
namespace IsingScaling.Rotor.PressureSelection

private def reflectedCoordinate (s : Bool) (u : Circle) : Circle :=
  if s then u⁻¹ else u

private def invertCoordinates (s : Fin 3 → Bool) (k : Momentum) : Momentum :=
  fun i => reflectedCoordinate (s i) (k i)

private def swapCoordinates (k : Momentum) : Momentum := fun i => k ((Equiv.swap 0 1) i)

private lemma factor_sum (u : Circle) (n : ℤ) :
    (∑ s : Bool, ((reflectedCoordinate s u ^ n : Circle) : ℂ)) =
      (2 * ((u ^ n : Circle) : ℂ).re : ℝ) := by
  rw [Fintype.sum_bool]
  change ((u⁻¹ ^ n : Circle) : ℂ) + ((u ^ n : Circle) : ℂ) = _
  rw [inv_zpow, Circle.coe_inv_eq_conj, add_comm, Complex.add_conj]

private lemma sign_sum (z : Site) (k : Momentum) :
    (∑ a : Fin 3 → Bool, realCharacter z (invertCoordinates a k)) =
      8 * ∏ i, ((k i ^ z i : Circle) : ℂ).re := by
  let F (i : Fin 3) (v : Bool) : ℂ := ((reflectedCoordinate v (k i) ^ z i : Circle) : ℂ)
  have hex (a : Fin 3 → Bool) :
      realCharacter z (invertCoordinates a k) = (∏ i, F i (a i)).re := by
    change (Circle.coeHom (∏ i, reflectedCoordinate (a i) (k i) ^ z i)).re = _
    rw [map_prod]
    rfl
  simp_rw [hex]
  rw [← Complex.re_sum, ← Fintype.prod_sum F]
  have hf (i : Fin 3) : (∑ v, F i v) = ((2 * ((k i ^ z i : Circle) : ℂ).re : ℝ) : ℂ) :=
    factor_sum (k i) (z i)
  simp_rw [hf]
  rw [← Complex.ofReal_prod]
  change (∏ i, (2 * ((k i ^ z i : Circle) : ℂ).re : ℝ)) = _
  rw [Finset.prod_mul_distrib]
  norm_num

private lemma power_re (u : Circle) (n : ℤ) :
    ((u ^ n : Circle) : ℂ).re = (Polynomial.Chebyshev.T ℝ n).eval (u : ℂ).re := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective u
  rw [← Circle.exp_intCast_mul]
  have he (s : ℝ) : ((Circle.exp s : Circle) : ℂ).re = Real.cos s := by
    rw [Circle.coe_exp, Complex.exp_mul_I]
    simp
    rw [← Complex.ofReal_cos]
    rfl
  rw [he, he, Polynomial.Chebyshev.T_real_cos]

abbrev CosPoly := MvPolynomial (Fin 3) ℝ
abbrev cosineVariables (k : Momentum) (i : Fin 3) := (k i : ℂ).re

def displacementPolynomial (z : Site) : CosPoly :=
  ∏ i : Fin 3, Polynomial.aeval (MvPolynomial.X i : CosPoly) (Polynomial.Chebyshev.T ℝ (z i))

private lemma displacementPolynomial_eval (z : Site) (k : Momentum) :
    MvPolynomial.eval (cosineVariables k) (displacementPolynomial z) =
    ∏ i, ((k i ^ z i : Circle) : ℂ).re := by
  simp only [displacementPolynomial, map_prod]
  apply prod_congr rfl
  intro i _
  rw [power_re]
  have H := Polynomial.aeval_algHom_apply (MvPolynomial.aeval (R := ℝ) (cosineVariables k))
    (MvPolynomial.X i : CosPoly) (Polynomial.Chebyshev.T ℝ (z i))
  simpa [MvPolynomial.aeval_eq_eval₂Hom, Polynomial.aeval_def, cosineVariables] using H.symm

/-- The full stabilizer mean of one character agrees with the horizontal
swap average of its displacement polynomial. -/
theorem horizontalMean_character (z : Site) (k : Momentum) :
    horizontalMean (realCharacter z) k =
      (MvPolynomial.eval (cosineVariables k) (displacementPolynomial z) +
       MvPolynomial.eval (cosineVariables (swapCoordinates k)) (displacementPolynomial z)) / 2 := by
  have h (b : Bool) :
      (∑ a : Fin 3 → Bool, realCharacter z (horizontalAction (a,b) k)) =
        8 * MvPolynomial.eval (cosineVariables (if b then swapCoordinates k else k))
          (displacementPolynomial z) := by
    cases b
    · change (∑ a, realCharacter z (invertCoordinates a k)) = 8 * MvPolynomial.eval _ _
      rw [displacementPolynomial_eval]
      exact sign_sum z k
    · change (∑ a, realCharacter z (invertCoordinates a (swapCoordinates k))) = 8 * MvPolynomial.eval _ _
      rw [displacementPolynomial_eval]
      exact sign_sum z (swapCoordinates k)
  change (∑ a : HorizontalSymmetry, realCharacter z (horizontalAction a k)) / _ = _
  rw [Fintype.sum_prod_type_right]
  simp only [h, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  have hc : Fintype.card HorizontalSymmetry = 16 := by decide
  rw [hc]
  push_cast
  ring

def packetPolynomial {ι : Type*} [Fintype ι] (r : Site → Site) (x : ι → Site) (c : ι → ℝ) :
    CosPoly := ∑ i, ∑ j, MvPolynomial.C (c i * c j) * displacementPolynomial (x i - r (x j))

theorem horizontalMean_reflectedTest_polynomial {ι : Type*} [Fintype ι]
    (r : Site → Site) (x : ι → Site) (c : ι → ℝ) (k : Momentum) :
    horizontalMean (reflectedTest r x c) k =
      (MvPolynomial.eval (cosineVariables k) (packetPolynomial r x c) +
       MvPolynomial.eval (cosineVariables (swapCoordinates k)) (packetPolynomial r x c)) / 2 := by
  classical
  let g (i j : ι) := realCharacter (x i-r (x j))
  have hm : horizontalMean (reflectedTest r x c) k =
      ∑ i, ∑ j, (c i*c j) * horizontalMean (g i j) k := by
    change (∑ a : HorizontalSymmetry, ∑ i, ∑ j, c i*c j*g i j (horizontalAction a k)) / _ = _
    calc
      _ = (∑ i, ∑ j, ∑ a : HorizontalSymmetry, c i*c j*g i j (horizontalAction a k)) /
          (Fintype.card HorizontalSymmetry : ℝ) := by
        congr 1
        rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_comm
      _ = _ := by
        simp [horizontalMean, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [hm]
  simp only [g, horizontalMean_character, packetPolynomial, map_sum, map_mul, MvPolynomial.eval_C]
  simp only [Finset.sum_add_distrib, Finset.sum_div, add_div, mul_add, mul_div_assoc]

/-- The three coefficients are polynomials in elementary symmetric cosine
coordinates. The distinguished coordinate and the horizontal product
are exactly the three admissible multiplier families. -/
theorem horizontalMean_reflectedTest_elementary {ι : Type*} [Fintype ι]
    (r : Site → Site) (x : ι → Site) (c : ι → ℝ) :
    ∃ A B C : CosPoly, ∀ k : Momentum,
      let u := cosineVariables k 0
      let v := cosineVariables k 1
      let w := cosineVariables k 2
      let e := MathlibProbe.RotorObliqueTestPolynomials.elementary u v w
      horizontalMean (reflectedTest r x c) k = MvPolynomial.eval e A +
        w * MvPolynomial.eval e B + (u*v) * MvPolynomial.eval e C := by
  obtain ⟨A,B,C,h⟩ := MathlibProbe.RotorObliqueTestPolynomials.averaged_test_representation
    (packetPolynomial r x c)
  refine ⟨A,B,C,fun k => ?_⟩
  let u := cosineVariables k 0
  let v := cosineVariables k 1
  let w := cosineVariables k 2
  have hk : cosineVariables k = MathlibProbe.RotorObliqueTestPolynomials.nodes u v w := by
    funext i
    fin_cases i <;> rfl
  have hs : cosineVariables (swapCoordinates k) = MathlibProbe.RotorObliqueTestPolynomials.nodes v u w := by
    funext i
    fin_cases i <;> rfl
  rw [horizontalMean_reflectedTest_polynomial, hk, hs]
  exact h u v w

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.horizontalMean_reflectedTest_polynomial
#print axioms IsingScaling.Rotor.PressureSelection.horizontalMean_reflectedTest_elementary
