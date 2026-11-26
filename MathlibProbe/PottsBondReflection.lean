import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Bond reflection for the free finite q-colour Potts Gibbs law. The graph
consists of two copies of the same finite half with identical interactions
and a bond from each vertex on the seam to its reflected image. In a
coordinate bond reflection of a nearest-neighbour box these are precisely
the crossing edges.
-/

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace IsingScaling.Potts

/-- Exact Gibbs factor of one Potts edge. -/
def edgeWeight {q : ℕ} (β : ℝ) (a b : Fin q) : ℝ :=
  Real.exp (if a = b then β else 0)

/-- One equal-colour interaction is a positive semidefinite matrix. -/
theorem edgeWeight_posSemidef (q : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Matrix.PosSemidef (Matrix.of (edgeWeight (q := q) β)) := by
  classical
  let ones : Fin q → ℝ := fun _ => 1
  have hJ := Matrix.posSemidef_vecMulVec_self_star ones
  have hI : (1 : Matrix (Fin q) (Fin q) ℝ).PosSemidef := .one
  have he : 0 ≤ Real.exp β - 1 := sub_nonneg.mpr (Real.one_le_exp hβ)
  have hrepr : Matrix.of (edgeWeight (q := q) β) =
      vecMulVec ones (star ones) + (Real.exp β - 1) • (1 : Matrix (Fin q) (Fin q) ℝ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [edgeWeight, ones, hij, Matrix.vecMulVec_apply]
  rw [hrepr]
  exact hJ.add (hI.smul he)

/-- Product of the physical crossing weights, indexed by complete
half-configurations. Each crossing bond can have its own interaction. -/
def crossingWeight {q : ℕ} {V : Type*} (S : Finset V) (β : V → ℝ)
    (σ τ : V → Fin q) : ℝ :=
  ∏ v ∈ S, edgeWeight (β v) (σ v) (τ v)

theorem crossingWeight_posSemidef {V : Type*} [Fintype V] (q : ℕ)
    (S : Finset V) (β : V → ℝ) (hβ : ∀ v ∈ S, 0 ≤ β v) :
    Matrix.PosSemidef (Matrix.of (crossingWeight (q := q) S β)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    let u : (V → Fin q) → ℝ := fun _ => 1
    have hbase : Matrix.of (crossingWeight (q := q) ∅ β) = vecMulVec u (star u) := by
      ext σ τ
      simp [crossingWeight, Matrix.vecMulVec_apply, u]
    rw [hbase]
    exact Matrix.posSemidef_vecMulVec_self_star u
  | @insert v S hv ih =>
    have hsite := (edgeWeight_posSemidef q (hβ v (by simp))).submatrix
      (fun σ : V → Fin q => σ v)
    have hrest := ih (fun u hu => hβ u (Finset.mem_insert_of_mem hu))
    have hins : Matrix.of (crossingWeight (q := q) (insert v S) β) =
        Matrix.hadamard ((Matrix.of (edgeWeight (q := q) (β v))).submatrix
          (fun σ : V → Fin q => σ v) (fun τ : V → Fin q => τ v))
          (Matrix.of (crossingWeight (q := q) S β)) := by
      ext σ τ
      simp [crossingWeight, Finset.prod_insert hv, Matrix.hadamard_apply]
    rw [hins]
    exact hsite.hadamard hrest

/-- Internal bonds of one half. Each edge is supplied once, and the
choice of the orientation of its displayed pair does not affect its weight. -/
def halfWeight {q : ℕ} {V : Type*} (E : Finset (V × V)) (J : V × V → ℝ)
    (σ : V → Fin q) : ℝ :=
  ∏ e ∈ E, edgeWeight (J e) (σ e.1) (σ e.2)

/-- Full unnormalized Gibbs weight for the two free reflected halves. -/
def reflectedGibbsWeight {q : ℕ} {V : Type*}
    (E : Finset (V × V)) (S : Finset V) (J : V × V → ℝ) (β : V → ℝ)
    (σ τ : V → Fin q) : ℝ :=
  halfWeight E J σ * halfWeight E J τ * crossingWeight S β σ τ

theorem reflectedGibbsWeight_pos {q : ℕ} {V : Type*}
    (E : Finset (V × V)) (S : Finset V) (J : V × V → ℝ) (β : V → ℝ)
    (σ τ : V → Fin q) : 0 < reflectedGibbsWeight E S J β σ τ := by
  unfold reflectedGibbsWeight halfWeight crossingWeight edgeWeight
  positivity

/-- The free finite-volume bond-reflected inequality for every real signed
observable on the entire half. Internal interactions may be arbitrary;
only the crossing interactions have to be ferromagnetic. -/
theorem reflectedGibbs_signed_test_nonneg {q : ℕ} [NeZero q]
    {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V)) (S : Finset V)
    (J : V × V → ℝ) (β : V → ℝ) (hβ : ∀ v ∈ S, 0 ≤ β v)
    (F : (V → Fin q) → ℝ) :
    0 ≤ (∑ σ, ∑ τ, reflectedGibbsWeight E S J β σ τ * (F σ * F τ)) /
        (∑ σ : V → Fin q, ∑ τ : V → Fin q, reflectedGibbsWeight E S J β σ τ) := by
  classical
  let f : (V → Fin q) → ℝ := fun σ => halfWeight E J σ * F σ
  have h := (crossingWeight_posSemidef q S β hβ).dotProduct_mulVec_nonneg f
  have hz : 0 < ∑ σ : V → Fin q, ∑ τ : V → Fin q, reflectedGibbsWeight E S J β σ τ :=
    Finset.sum_pos (fun σ _ => Finset.sum_pos (fun τ _ =>
      reflectedGibbsWeight_pos E S J β σ τ) Finset.univ_nonempty) Finset.univ_nonempty
  apply div_nonneg _ hz.le
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
    Matrix.of_apply] at h
  convert h using 1
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  unfold reflectedGibbsWeight f
  ring

/-- Coordinates on one half of a box with an even number of normal layers.
The other half uses the same coordinates after reflection. -/
abbrev HalfBox (m n l : ℕ) := Fin (m+1) × Fin (n+1) × Fin (l+1)

/-- All undirected nearest-neighbour edges of the half-box, recorded
once with positive orientation along the changing coordinate. -/
def boxEdges (m n l : ℕ) : Finset (HalfBox m n l × HalfBox m n l) :=
  Finset.univ.filter fun e =>
    let a := e.1
    let b := e.2
    (b.1.val = a.1.val + 1 ∧ a.2 = b.2) ∨
    (a.1 = b.1 ∧ b.2.1.val = a.2.1.val + 1 ∧ a.2.2 = b.2.2) ∨
    (a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ b.2.2.val = a.2.2.val + 1)

/-- Every site of the face at normal coordinate zero has exactly one
crossing bond to its reflected copy. -/
def boxSeam (m n l : ℕ) : Finset (HalfBox m n l) :=
  Finset.univ.filter fun a => a.1.val = 0

/-- Homogeneous free rectangular box on the cubic lattice, of full
dimensions 2(m+1) by (n+1) by (l+1), reflected across its central bond plane. -/
def cubicGibbsWeight {q : ℕ} (m n l : ℕ) (β : ℝ)
    (σ τ : HalfBox m n l → Fin q) : ℝ :=
  reflectedGibbsWeight (boxEdges m n l) (boxSeam m n l) (fun _ => β) (fun _ => β) σ τ

theorem cubicGibbs_signed_test_nonneg {q : ℕ} [NeZero q] (m n l : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) (F : (HalfBox m n l → Fin q) → ℝ) :
    0 ≤ (∑ σ, ∑ τ, cubicGibbsWeight m n l β σ τ * (F σ * F τ)) /
        (∑ σ : HalfBox m n l → Fin q, ∑ τ : HalfBox m n l → Fin q,
          cubicGibbsWeight m n l β σ τ) :=
  reflectedGibbs_signed_test_nonneg (boxEdges m n l) (boxSeam m n l)
    (fun _ => β) (fun _ => β) (fun _ _ => hβ) F


end IsingScaling.Potts
