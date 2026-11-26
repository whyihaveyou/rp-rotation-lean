import MathlibProbe.HeisenbergAsanoWire
import MathlibProbe.HeisenbergEulerTensorIntegral

/-!
# Simultaneous site symmetrization of a finite spinor array

The two indices at a leg are the row and the column, in this order. Expose
the first gate of a site's local circuit. In the product over all sites this
changes just that site's row, since its two physical legs belong to it alone.
Factoring out all spectator sites identifies the operation with a convex
combination of two rows of the *entire* matrix, also after multiplying by the
original interaction array. The two-row polydisk theorem now applies. Finite
induction on the gates and the sites starts from the identity kernel and
gives exactly the tensor product of the independently ordered site circuits.
-/

noncomputable section
open scoped BigOperators Classical
namespace IsingScaling.Rotor.HeisenbergField.SiteSymmetrization

open MathlibProbe

variable {V L : Type*}
abbrev BitMatrix (L : Type*) := Matrix (L → Bool) (L → Bool) ℂ

/-- Reindex the given finite leg set for the dense paired-bit symbol. -/
def denseCoeff {n : ℕ} (e : Fin n ≃ L) (M : BitMatrix L) (b : Fin n → Bool × Bool) : ℂ :=
  M (fun l => (b (e.symm l)).1) (fun l => (b (e.symm l)).2)

/-- Disk stability tests independent row and column variables at every physical leg. -/
def Stable {n : ℕ} (e : Fin n ≃ L) (M : BitMatrix L) : Prop :=
  ∀ v : Fin n → ℂ × ℂ, (∀ i, ‖(v i).1‖ < 1 ∧ ‖(v i).2‖ < 1) →
    HeisenbergAsanoWire.denseSymbol n (denseCoeff e M) v ≠ 0

private def oddsMix (c : ℕ) (a b : ℂ) : ℂ := (a + (c:ℂ)*b) / ((c:ℂ)+1)

private theorem oddsMix_eq (c : ℕ) (a b : ℂ) :
    oddsMix c a b = HeisenbergAsanoWire.partialMix ((c:ℝ)/((c:ℝ)+1)) a b := by
  unfold oddsMix HeisenbergAsanoWire.partialMix
  push_cast
  have hd : (c:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
  field_simp
  ring

private theorem stable_mix {n : ℕ} (e : Fin n ≃ L) (M : BitMatrix L)
    (u v : L) (c : ℕ) (hM : Stable e M) :
    Stable e (fun I J => oddsMix c (M I J) (M (I ∘ Equiv.swap u v) J)) := by
  classical
  let θ : ℝ := (c:ℝ) / ((c:ℝ)+1)
  have hθ₀ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ₁ : θ ≤ 1 := by
    dsimp [θ]
    rw [div_le_one (by positivity : 0 < (c:ℝ)+1)]
    linarith
  have he : denseCoeff e (fun I J => oddsMix c (M I J) (M (I ∘ Equiv.swap u v) J)) =
      HeisenbergAsanoWire.partialRowExchange (e.symm u) (e.symm v) θ (denseCoeff e M) := by
    funext b
    have hb : (fun l => (b (e.symm l)).1) ∘ Equiv.swap u v =
        fun l => (b (Equiv.swap (e.symm u) (e.symm v) (e.symm l))).1 := by
      funext l
      simp only [Function.comp_apply, e.symm.injective.map_swap]
    simp only [denseCoeff, oddsMix_eq, HeisenbergAsanoWire.partialRowExchange,
      HeisenbergAsanoWire.swapRows, hb, θ]
  intro z hz
  rw [he]
  exact HeisenbergAsanoWire.denseSymbol_partialRowExchange_nonzero _ _ hθ₀ hθ₁ _ hM z hz

private def pair {d : ℕ} : SymmetrizerExchange.Gate d → Fin d × Fin d
  | .front _ => (0,1)
  | .shift g => ((pair g).1.succ, (pair g).2.succ)

private theorem apply_swap {d : ℕ} (g : SymmetrizerExchange.Gate d) (I : SymmetrizerExchange.Word d) (i : Fin d) :
    g.swap I i = I (Equiv.swap (pair g).1 (pair g).2 i) := by
  induction g with
  | @front n c =>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp [pair, SymmetrizerExchange.Gate.swap, SymmetrizerExchange.prepend, SymmetrizerExchange.rest, Fin.tail_def]
    · simp [pair, SymmetrizerExchange.Gate.swap, SymmetrizerExchange.prepend, SymmetrizerExchange.rest, Fin.tail_def, Fin.succ_zero_eq_one]
    · have h0 : k.succ.succ ≠ 0 := Fin.succ_ne_zero _
      have h1 : k.succ.succ ≠ 1 := by
        change k.succ.succ ≠ (0 : Fin (n+1)).succ
        exact fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h)
      simp [pair, SymmetrizerExchange.Gate.swap, SymmetrizerExchange.prepend, SymmetrizerExchange.rest, Fin.tail_def,
        Equiv.swap_apply_of_ne_of_ne h0 h1]
  | @shift n g ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pair, SymmetrizerExchange.Gate.swap, SymmetrizerExchange.prepend,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.succ_ne_zero (pair g).1))
          (Ne.symm (Fin.succ_ne_zero (pair g).2))]
    · simp only [pair, SymmetrizerExchange.Gate.swap, SymmetrizerExchange.prepend, Fin.cons_succ, ih, SymmetrizerExchange.rest, Fin.tail_def,
        (Fin.succ_injective _).map_swap]

variable [Fintype L]

private def slot (loc : L → V) (x : V) (i : Fin (EulerTensor.degree loc x)) : L :=
  ((Fintype.equivFin (EulerTensor.Fibre loc x)).symm i).val

private theorem slot_loc (loc : L → V) (x : V) (i : Fin (EulerTensor.degree loc x)) :
    loc (slot loc x i) = x := ((Fintype.equivFin (EulerTensor.Fibre loc x)).symm i).property

private theorem slot_injective (loc : L → V) (x : V) : Function.Injective (slot loc x) :=
  Subtype.val_injective.comp (Fintype.equivFin (EulerTensor.Fibre loc x)).symm.injective

private def physicalSwap (loc : L → V) (x : V) (g : SymmetrizerExchange.Gate (EulerTensor.degree loc x)) :
    Equiv.Perm L := Equiv.swap (slot loc x (pair g).1) (slot loc x (pair g).2)

private theorem siteWord_swap_self (loc : L → V) (x : V)
    (g : SymmetrizerExchange.Gate (EulerTensor.degree loc x)) (I : L → Bool) :
    EulerTensor.siteWord loc (I ∘ physicalSwap loc x g) x = g.swap (EulerTensor.siteWord loc I x) := by
  funext i
  rw [apply_swap]
  change I (physicalSwap loc x g (slot loc x i)) =
    I (slot loc x (Equiv.swap (pair g).1 (pair g).2 i))
  rw [(slot_injective loc x).map_swap]
  rfl

private theorem siteWord_swap_other (loc : L → V) {x y : V} (h : y ≠ x)
    (g : SymmetrizerExchange.Gate (EulerTensor.degree loc x)) (I : L → Bool) :
    EulerTensor.siteWord loc (I ∘ physicalSwap loc x g) y = EulerTensor.siteWord loc I y := by
  funext i
  have hd (j : Fin (EulerTensor.degree loc x)) : slot loc y i ≠ slot loc x j := by
    intro he
    exact h (by simpa only [slot_loc] using congrArg loc he)
  change I (Equiv.swap _ _ (slot loc y i)) = I (slot loc y i)
  rw [Equiv.swap_apply_of_ne_of_ne (hd _) (hd _)]

private theorem siteWord_ext (loc : L → V) {I J : L → Bool}
    (h : ∀ x, EulerTensor.siteWord loc I x = EulerTensor.siteWord loc J x) : I = J := by
  funext l
  let q : EulerTensor.Fibre loc (loc l) := ⟨l,rfl⟩
  have hq := congrFun (h (loc l)) ((Fintype.equivFin (EulerTensor.Fibre loc (loc l))) q)
  simpa only [EulerTensor.siteWord, Equiv.symm_apply_apply, q] using hq

private abbrev Programs (loc : L → V) := (x : V) → List (SymmetrizerExchange.Gate (EulerTensor.degree loc x))

private def siteEntry (loc : L → V) (P : Programs loc) (I K : L → Bool) (x : V) : ℂ :=
  SymmetrizerExchange.run (P x) (fun w => if w = EulerTensor.siteWord loc K x then 1 else 0) (EulerTensor.siteWord loc I x)

variable [Fintype V]

private def assembled (loc : L → V) (P : Programs loc) : BitMatrix L :=
  fun I K => ∏ x, siteEntry loc P I K x

private theorem empty_matrix (loc : L → V) : assembled loc (fun _ => []) = 1 := by
  classical
  ext I K
  by_cases h : I = K
  · subst K
    simp [assembled, siteEntry, SymmetrizerExchange.run]
  · obtain ⟨x,hx⟩ : ∃ x, EulerTensor.siteWord loc I x ≠ EulerTensor.siteWord loc K x := by
      by_contra! hn
      exact h (siteWord_ext loc hn)
    rw [Matrix.one_apply, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [siteEntry, SymmetrizerExchange.run, hx])

private theorem assemble_cons (loc : L → V) (P : Programs loc) (x : V)
    (g : SymmetrizerExchange.Gate (EulerTensor.degree loc x)) (I K : L → Bool) :
    assembled loc (Function.update P x (g::P x)) I K =
      oddsMix g.odds (assembled loc P I K) (assembled loc P (I ∘ physicalSwap loc x g) K) := by
  classical
  let E := Finset.univ.erase x
  let I' := I ∘ physicalSwap loc x g
  let P' := Function.update P x (g::P x)
  have splitAt (P₀ : Programs loc) (I₀ : L → Bool) : assembled loc P₀ I₀ K =
      (∏ y ∈ E, siteEntry loc P₀ I₀ K y) * siteEntry loc P₀ I₀ K x :=
    (Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ x)).symm
  have h₁ : (∏ y ∈ E, siteEntry loc P' I K y) = ∏ y ∈ E, siteEntry loc P I K y := by
    apply Finset.prod_congr rfl
    intro y hy
    simp [siteEntry, P', Function.update_of_ne (Finset.ne_of_mem_erase hy)]
  have h₂ : (∏ y ∈ E, siteEntry loc P I' K y) = ∏ y ∈ E, siteEntry loc P I K y := by
    apply Finset.prod_congr rfl
    intro y hy
    rw [siteEntry, siteEntry, show EulerTensor.siteWord loc I' y = EulerTensor.siteWord loc I y from
      siteWord_swap_other loc (Finset.ne_of_mem_erase hy) g I]
  have hx : siteEntry loc P' I K x =
      oddsMix g.odds (siteEntry loc P I K x) (siteEntry loc P I' K x) := by
    simp only [siteEntry, P', Function.update_self, SymmetrizerExchange.run, SymmetrizerExchange.gateAction, oddsMix,
      I', siteWord_swap_self]
  change assembled loc P' I K = oddsMix _ (assembled loc P I K) (assembled loc P I' K)
  rw [splitAt P' I, splitAt P I, splitAt P I', h₁, h₂, hx]
  unfold oddsMix
  ring

private theorem multiply_cons (loc : L → V) (P : Programs loc) (x : V)
    (g : SymmetrizerExchange.Gate (EulerTensor.degree loc x)) (M : BitMatrix L) :
    assembled loc (Function.update P x (g::P x)) * M =
      fun I J => oddsMix g.odds ((assembled loc P * M) I J)
        ((assembled loc P * M) (I ∘ physicalSwap loc x g) J) := by
  ext I J
  simp only [Matrix.mul_apply, assemble_cons, oddsMix, div_mul_eq_mul_div, add_mul,
    ← Finset.sum_div, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

private theorem stable_cons {n : ℕ} (e : Fin n ≃ L) (loc : L → V) (P : Programs loc)
    (x : V) (g : SymmetrizerExchange.Gate (EulerTensor.degree loc x)) (M : BitMatrix L)
    (hp : Stable e (assembled loc P * M)) :
    Stable e (assembled loc (Function.update P x (g::P x)) * M) := by
  rw [multiply_cons]
  exact stable_mix e _ (slot loc x (pair g).1) (slot loc x (pair g).2) g.odds hp

/-- Left multiplication by the physical tensor product of site symmetrizers
preserves disk stability of the full matrix symbol. The ordering e of all
legs is arbitrary, and the displayed site kernel is EulerTensor.siteSym_apply. -/
theorem siteSym_mul_stable {n : ℕ} (loc : L → V) (e : Fin n ≃ L) (M : BitMatrix L)
    (hM : Stable e M) : Stable e (EulerTensor.siteSym loc * M) := by
  classical
  let prog (s : Finset V) : Programs loc := fun x =>
    if x ∈ s then SymmetrizerExchange.circuit (EulerTensor.degree loc x) else []
  have hs (s : Finset V) : Stable e (assembled loc (prog s) * M) := by
    induction s using Finset.induction_on with
    | empty =>
      have hz : prog ∅ = fun _ => [] := by funext y; simp [prog]
      rwa [hz, empty_matrix, one_mul]
    | @insert x s hnot hi =>
      have hx : prog s x = [] := by simp [prog,hnot]
      have insertGates (gates : List (SymmetrizerExchange.Gate (EulerTensor.degree loc x))) :
          Stable e (assembled loc (Function.update (prog s) x gates) * M) := by
        induction gates with
        | nil => rwa [← hx, Function.update_eq_self]
        | cons g gs ih =>
          have h := stable_cons e loc (Function.update (prog s) x gs) x g M ih
          simpa only [Function.update_self, Function.update_idem] using h
      have he : prog (insert x s) = Function.update (prog s) x (SymmetrizerExchange.circuit (EulerTensor.degree loc x)) := by
        funext y
        by_cases h : y = x
        · subst y; simp [prog]
        · simp [prog,h]
      rw [he]
      exact insertGates _
  have hfull : assembled loc (prog Finset.univ) = EulerTensor.siteSym loc := by
    ext I J
    simp only [assembled, prog, Finset.mem_univ, ite_true, EulerTensor.siteSym, siteEntry,
      SymmetrizerExchange.product_entry]
  simpa only [hfull] using hs Finset.univ

#print axioms siteSym_mul_stable

end IsingScaling.Rotor.HeisenbergField.SiteSymmetrization
