import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The three variables represent the cosines of the three Fourier coordinates.
For the oblique mirror selection argument the test polynomial is symmetric
in the first two cosines. Its three coefficient polynomials below are
evaluated only at the elementary symmetric polynomials of *all three*
cosines. The conclusion uses exactly the directions 1, w and u*v.
-/

noncomputable section

namespace MathlibProbe.RotorObliqueTestPolynomials

abbrev Poly := MvPolynomial (Fin 3) ℝ

def nodes (u v w : ℝ) : Fin 3 → ℝ := ![u, v, w]

def elementary (u v w : ℝ) : Fin 3 → ℝ :=
  ![u + v + w, u*v + u*w + v*w, u*v*w]

private structure Triple where
  a : Poly
  b : Poly
  c : Poly

private def Triple.val (A : Triple) (u v w : ℝ) : ℝ :=
  let ev := MvPolynomial.eval (elementary u v w)
  ev A.a + w * ev A.b + w^2 * ev A.c

private def Triple.const (k : ℝ) : Triple := ⟨MvPolynomial.C k, 0, 0⟩
private def Triple.add (A B : Triple) : Triple := ⟨A.a+B.a, A.b+B.b, A.c+B.c⟩
private def Triple.neg (A : Triple) : Triple := ⟨-A.a, -A.b, -A.c⟩
private def Triple.scale (A : Triple) (q : Poly) : Triple := ⟨q*A.a, q*A.b, q*A.c⟩

/-- Reduction of w cubed by the monic cubic having roots u, v and w. -/
private def Triple.timesW (A : Triple) : Triple :=
  ⟨MvPolynomial.X 2*A.c, A.a-MvPolynomial.X 1*A.c, A.b+MvPolynomial.X 0*A.c⟩

private def Triple.timesSum (A : Triple) : Triple :=
  (A.scale (MvPolynomial.X 0)).add A.timesW.neg

private def Triple.timesUV (A : Triple) : Triple :=
  ((A.scale (MvPolynomial.X 1)).add (A.scale (MvPolynomial.X 0)).timesW.neg).add A.timesW.timesW

@[simp] private theorem Triple.val_const (k u v w : ℝ) :
    (Triple.const k).val u v w = k := by simp [Triple.const, Triple.val]

@[simp] private theorem Triple.val_add (A B : Triple) (u v w : ℝ) :
    (A.add B).val u v w = A.val u v w + B.val u v w := by
  simp [Triple.add, Triple.val]
  ring

@[simp] private theorem Triple.val_neg (A : Triple) (u v w : ℝ) :
    A.neg.val u v w = -A.val u v w := by
  simp [Triple.neg, Triple.val]
  ring

@[simp] private theorem Triple.val_scale (A : Triple) (q : Poly) (u v w : ℝ) :
    (A.scale q).val u v w = MvPolynomial.eval (elementary u v w) q * A.val u v w := by
  simp [Triple.scale, Triple.val]
  ring

@[simp] private theorem Triple.val_timesW (A : Triple) (u v w : ℝ) :
    A.timesW.val u v w = w * A.val u v w := by
  simp [Triple.timesW, Triple.val, elementary]
  ring

@[simp] private theorem Triple.val_timesSum (A : Triple) (u v w : ℝ) :
    A.timesSum.val u v w = (u+v) * A.val u v w := by
  simp [Triple.timesSum, elementary]
  ring

@[simp] private theorem Triple.val_timesUV (A : Triple) (u v w : ℝ) :
    A.timesUV.val u v w = (u*v) * A.val u v w := by
  simp [Triple.timesUV, elementary]
  ring

private theorem Triple.val_swap (A : Triple) (u v w : ℝ) :
    A.val v u w = A.val u v w := by
  have eqn : elementary v u w = elementary u v w := by
    funext i
    fin_cases i
    · change v + u + w = u + v + w
      ring
    · change v*u + v*w + u*w = u*v + u*w + v*w
      ring
    · change v*u*w = u*v*w
      ring
  simp [Triple.val, eqn]

private theorem splitPolynomial (f : Poly) :
    ∃ A B : Triple, ∀ u v w : ℝ, MvPolynomial.eval (nodes u v w) f =
      A.val u v w + u * B.val u v w := by
  induction f using MvPolynomial.induction_on with
  | C k =>
    exact ⟨Triple.const k, Triple.const 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨A, B, hf⟩ := hf
    obtain ⟨C, D, hg⟩ := hg
    refine ⟨A.add C, B.add D, ?_⟩
    intro u v w
    simp [map_add, hf, hg]
    ring
  | mul_X f i hf =>
    obtain ⟨A, B, hf⟩ := hf
    fin_cases i
    · refine ⟨B.timesUV.neg, A.add B.timesSum, ?_⟩
      intro u v w
      rw [map_mul, hf]
      simp [nodes]
      ring
    · refine ⟨A.timesSum.add B.timesUV, A.neg, ?_⟩
      intro u v w
      rw [map_mul, hf]
      simp [nodes]
      ring
    · refine ⟨A.timesW, B.timesW, ?_⟩
      intro u v w
      rw [map_mul, hf]
      simp [nodes]
      ring

/-- The stabilizer average of every real test polynomial has the three
admissible directions of the oblique-mirror pressure argument. -/
theorem averaged_test_representation (f : Poly) :
    ∃ a b c : Poly, ∀ u v w : ℝ,
      (MvPolynomial.eval (nodes u v w) f + MvPolynomial.eval (nodes v u w) f) / 2 =
      MvPolynomial.eval (elementary u v w) a +
        w * MvPolynomial.eval (elementary u v w) b +
        (u*v) * MvPolynomial.eval (elementary u v w) c := by
  obtain ⟨A, B, h⟩ := splitPolynomial f
  let Q := A.add (B.timesSum.scale (MvPolynomial.C (1/2 : ℝ)))
  have hQ (u v w : ℝ) :
      (MvPolynomial.eval (nodes u v w) f + MvPolynomial.eval (nodes v u w) f) / 2 =
        Q.val u v w := by
    simp only [h, Triple.val_swap A u v w, Triple.val_swap B u v w]
    simp [Q]
    ring
  refine ⟨Q.a-MvPolynomial.X 1*Q.c, Q.b+MvPolynomial.X 0*Q.c, Q.c, ?_⟩
  intro u v w
  rw [hQ]
  simp [Triple.val, elementary]
  ring

/-- In particular the representation applies to a test already invariant
under exchange of the first two cosine coordinates. -/
theorem symmetric_test_representation (f : Poly)
    (hsymm : ∀ u v w : ℝ,
      MvPolynomial.eval (nodes u v w) f = MvPolynomial.eval (nodes v u w) f) :
    ∃ a b c : Poly, ∀ u v w : ℝ,
      MvPolynomial.eval (nodes u v w) f =
      MvPolynomial.eval (elementary u v w) a +
        w * MvPolynomial.eval (elementary u v w) b +
        (u*v) * MvPolynomial.eval (elementary u v w) c := by
  obtain ⟨a, b, c, h⟩ := averaged_test_representation f
  refine ⟨a, b, c, ?_⟩
  intro u v w
  have eqn := h u v w
  rw [← hsymm u v w] at eqn
  linarith only [eqn]

end MathlibProbe.RotorObliqueTestPolynomials
