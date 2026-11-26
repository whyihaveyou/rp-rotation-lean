import MathlibProbe.HeisenbergSymmetrizerExchange
import MathlibProbe.RotorHeisenbergComplexPartition
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Contraction of the classical Heisenberg integral on arbitrary finite site fibres

Each labelled tensor leg belongs to a physical vertex. All legs at that vertex
use one and the same spin in the product of probability surface measures. A gate
entry with row I and column J contracts against the physical projection with
row J and column I. The integral is therefore the trace of the sitewise symmetric
projection times the gate tensor, with the positive factor ∏ₓ 1/(dₓ+1).
-/

noncomputable section
open MeasureTheory Finset
open scoped Classical BigOperators

namespace IsingScaling.Rotor.HeisenbergField.EulerTensor
open ComplexPartition BlochSphere

variable {V L : Type*}
abbrev Fibre (loc : L → V) (x : V) := {l : L // loc l = x}

def degree [Fintype L] (loc : L → V) (x : V) := Fintype.card (Fibre loc x)

/-- A deterministic ordering is used only to index copies of the local spin. -/
def siteWord [Fintype L] (loc : L → V) (I : L → Bool) (x : V) : Fin (degree loc x) → Bool :=
  fun k => I ((Fintype.equivFin (Fibre loc x)).symm k).val

/-- A gate matrix uses the two spinor indices in the opposite order from the
physical Bloch projector. Vertices may repeat amongst the labels. -/
def evaluation [Fintype L] (loc : L → V) (M : Matrix (L → Bool) (L → Bool) ℂ)
    (s : Config V) : ℂ :=
  ∑ I, ∑ J, M I J * ∏ l, entry (s (loc l)) (J l) (I l)

private theorem continuous_entry (i j : Bool) :
    Continuous (fun s : Spin 3 => entry s i j) := by
  cases i <;> cases j <;> simp only [entry,up,down,minus,plus] <;> fun_prop

theorem product_entries [Fintype V] [Fintype L] (loc : L → V) (I J : L → Bool) (s : Config V) :
    (∏ l, entry (s (loc l)) (I l) (J l)) =
      ∏ x, tensorEntry (siteWord loc I x) (siteWord loc J x) (s x) := by
  rw [← Fintype.prod_fiberwise loc (fun l => entry (s (loc l)) (I l) (J l))]
  apply Finset.prod_congr rfl
  intro x _
  let f (l : Fibre loc x) := entry (s x) (I l.val) (J l.val)
  calc _ = ∏ l : Fibre loc x, f l := Finset.prod_congr rfl (fun l _ => by simp [f,l.property])
       _ = _ := ((Fintype.equivFin (Fibre loc x)).symm.prod_comp f).symm

/-- The actual independent physical sphere integrals, with one integral per
vertex regardless of how many legs revisit it. This includes isolated vertices. -/
theorem integral_product_entries [Fintype V] [Fintype L] (loc : L → V) (I J : L → Bool) :
    (∫ s : Config V, ∏ l, entry (s (loc l)) (I l) (J l) ∂surfaceProduct V) =
      ∏ x, tensorMoment (siteWord loc I x) (siteWord loc J x) := by
  simp only [product_entries loc I J]
  exact integral_fintype_prod_eq_prod (fun x => tensorEntry (siteWord loc I x) (siteWord loc J x))

/-- Each factor is a real, strictly positive local dimension normalization. -/
def dimensionFactor [Fintype V] [Fintype L] (loc : L → V) : ℝ :=
  ∏ x, ((degree loc x : ℝ)+1)⁻¹

theorem dimensionFactor_pos [Fintype V] [Fintype L] (loc : L → V) : 0 < dimensionFactor loc :=
  Finset.prod_pos (fun _ _ => by positivity)

/-- The sitewise Kronecker product of the actual local symmetric projections.
Each local factor is the finite exchange circuit on its physical fibre. -/
def siteSym [Fintype V] [Fintype L] (loc : L → V) : Matrix (L → Bool) (L → Bool) ℂ :=
  fun I J => ∏ x, ((SymmetrizerExchange.circuit (degree loc x)).map
    SymmetrizerExchange.gateMatrix).prod (siteWord loc I x) (siteWord loc J x)

theorem siteSym_apply [Fintype V] [Fintype L] (loc : L → V) (I J : L → Bool) :
    siteSym loc I J = ∏ x, if BlochSphere.weight (siteWord loc I x) =
        BlochSphere.weight (siteWord loc J x) then
      1 / ((degree loc x).choose (BlochSphere.weight (siteWord loc I x)) : ℂ)
    else 0 := by
  unfold siteSym
  apply Finset.prod_congr rfl
  exact fun x _ => SymmetrizerExchange.symmetrizer_eq_adjacent_product _ _ _

theorem integral_entries_sym [Fintype V] [Fintype L] (loc : L → V) (I J : L → Bool) :
    (∫ s : Config V, ∏ l, entry (s (loc l)) (I l) (J l) ∂surfaceProduct V) =
      (dimensionFactor loc : ℂ) * siteSym loc I J := by
  rw [integral_product_entries]
  simp only [SymmetrizerExchange.tensorMoment_eq_adjacent_product, div_eq_mul_inv,
    Finset.prod_mul_distrib,dimensionFactor,siteSym,Complex.ofReal_prod,Complex.ofReal_inv,
    Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
  ring

/-- No hypothesis on M is needed for the integration identity. The choice
of trace order is fixed by the reversed row/column indices of each projector. -/
theorem integral_evaluation [Fintype V] [Fintype L] (loc : L → V)
    (M : Matrix (L → Bool) (L → Bool) ℂ) :
    (∫ s : Config V, evaluation loc M s ∂surfaceProduct V) =
      (dimensionFactor loc : ℂ) * Matrix.trace (siteSym loc * M) := by
  have hInt (I J : L → Bool) : Integrable
      (fun s : Config V => M I J * ∏ l, entry (s (loc l)) (J l) (I l)) (surfaceProduct V) :=
    (continuous_const.mul (continuous_finsetProd _ (fun l _ =>
      (continuous_entry (J l) (I l)).comp (continuous_apply (loc l))))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold evaluation
  rw [integral_finsetSum _ (fun I _ => integrable_finsetSum _ (fun J _ => hInt I J))]
  simp_rw [integral_finsetSum _ (fun _ _ => hInt _ _), integral_const_mul, integral_entries_sym loc]
  rw [Finset.sum_comm]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  ring

variable {A : Type*} {P : A → Type*}

/-- Tensor product of disjoint gate occurrences with arbitrary individual arities. -/
def gateTensor [Fintype A] (G : ∀ a, Matrix (P a → Bool) (P a → Bool) ℂ) :
    Matrix ((Σ a, P a) → Bool) ((Σ a, P a) → Bool) ℂ :=
  fun I J => ∏ a, G a (fun p => I ⟨a,p⟩) (fun p => J ⟨a,p⟩)

private theorem sum_words [Fintype A] [∀ a, Fintype (P a)]
    (f : (a : A) → (P a → Bool) → ℂ) :
    (∑ I : (Σ a, P a) → Bool, ∏ a, f a (fun p => I ⟨a,p⟩)) =
      ∏ a, ∑ i : P a → Bool, f a i := by
  rw [Fintype.prod_sum]
  exact (Equiv.piCurry (fun a (_ : P a) => Bool)).sum_comp (fun g => ∏ a, f a (g a))

/-- Before site integration the global contraction is exactly the product of
the individual physical gate evaluations, even when their physical sites coincide. -/
theorem product_evaluation [Fintype A] [∀ a, Fintype (P a)]
    (loc : (Σ a, P a) → V) (G : ∀ a, Matrix (P a → Bool) (P a → Bool) ℂ)
    (s : Config V) :
    evaluation loc (gateTensor G) s = ∏ a, evaluation (fun p => loc ⟨a,p⟩) (G a) s := by
  let f (a : A) (i j : P a → Bool) :=
    G a i j * ∏ p, entry (s (loc ⟨a,p⟩)) (j p) (i p)
  calc evaluation loc (gateTensor G) s =
      ∑ I : (Σ a, P a) → Bool, ∑ J : (Σ a, P a) → Bool,
        ∏ a, f a (fun p => I ⟨a,p⟩) (fun p => J ⟨a,p⟩) := by
           unfold evaluation gateTensor
           apply Finset.sum_congr (by ext; simp)
           intro I _
           apply Finset.sum_congr (by ext; simp)
           intro J _
           rw [Fintype.prod_sigma,← Finset.prod_mul_distrib]
    _ = ∑ I : (Σ a, P a) → Bool,
        ∏ a, ∑ j : P a → Bool, f a (fun p => I ⟨a,p⟩) j :=
          Finset.sum_congr rfl fun I _ => sum_words (fun a => f a (fun p => I ⟨a,p⟩))
    _ = ∏ a, evaluation (fun p => loc ⟨a,p⟩) (G a) s :=
          sum_words (fun a i => ∑ j, f a i j)

#print axioms integral_product_entries
#print axioms integral_evaluation
#print axioms product_evaluation
end IsingScaling.Rotor.HeisenbergField.EulerTensor
