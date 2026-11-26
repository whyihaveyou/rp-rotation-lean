import MathlibProbe.HeisenbergBlochSphereMoment
import MathlibProbe.HeisenbergSpinorGates
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# An explicit adjacent-exchange circuit for the binary symmetric projection

A gate is either a swap of the first two adjacent positions, with odds c,
or the same operation one position farther to the right. The ordered circuit
first draws a uniformly random bit to the head and then symmetrizes its tail.
To draw a bit from n+1 positions, first draw one from the last n, then take
that candidate with probability n/(n+1). This construction describes an
actual ordered product of matrices on all labelled bitstrings.

At fixed total weight k the probability that the new head is true is k/d.
Conditional on the head, the induction hypothesis symmetrizes the remaining
d-1 positions. The two binomial identities give mass 1 / choose(d,k) on
every output word of the same weight, also for repeated bits and d = 0.
-/

noncomputable section
open scoped BigOperators
namespace IsingScaling.Rotor.HeisenbergField.SymmetrizerExchange

abbrev Word (d : ℕ) := Fin d → Bool
abbrev prepend {n : ℕ} (b : Bool) (J : Word n) : Word (n+1) := Fin.cons b J
abbrev rest {n : ℕ} (I : Word (n+1)) : Word n := Fin.tail I

/-- Definitional agreement with the weight in the physical Bloch sphere moment. -/
def weight {d : ℕ} (I : Word d) : ℕ := ∑ i, (I i).toNat

private theorem weight_succ {n : ℕ} (I : Word (n+1)) :
    weight I = (I 0).toNat + weight (rest I) := by
  rw [weight, Fin.sum_univ_succ]
  rfl

private theorem weight_prepend {n : ℕ} (b : Bool) (I : Word n) :
    weight (prepend b I) = b.toNat + weight I := by
  rw [weight_succ]
  simp [prepend, rest]

private theorem weight_le {d : ℕ} (I : Word d) : weight I ≤ d := by
  calc weight I ≤ ∑ _ : Fin d, 1 := Finset.sum_le_sum (fun i _ => by cases I i <;> decide)
       _ = d := by simp

/-- A nearest-neighbour exchange and its nonnegative integer odds. -/
inductive Gate : ℕ → Type
  | front {n : ℕ} (odds : ℕ) : Gate (n+2)
  | shift {n : ℕ} (gate : Gate n) : Gate (n+1)

def Gate.odds {d : ℕ} : Gate d → ℕ
  | .front c => c
  | .shift g => g.odds

/-- Pull back an input word by the transposition of the specified neighbours. -/
def Gate.swap {d : ℕ} : Gate d → Word d → Word d
  | .front _, I => prepend ((rest I) 0) (prepend (I 0) (rest (rest I)))
  | .shift g, I => prepend (I 0) (g.swap (rest I))

theorem Gate.swap_swap {d : ℕ} (g : Gate d) (I : Word d) : g.swap (g.swap I) = I := by
  induction g with
  | front c =>
    simp [Gate.swap, prepend, rest, Fin.cons_self_tail]
  | shift g ih =>
    simp [Gate.swap, prepend, rest, ih, Fin.cons_self_tail]

private theorem Gate.swap_weight {d : ℕ} (g : Gate d) (I : Word d) :
    weight (g.swap I) = weight I := by
  induction g with
  | front c =>
    simp only [Gate.swap, weight_prepend]
    rw [weight_succ I, weight_succ (rest I)]
    omega
  | shift g ih =>
    simp only [Gate.swap, weight_prepend, ih, weight_succ I]

def gateAction {d : ℕ} (g : Gate d) (F : Word d → ℂ) (I : Word d) : ℂ :=
  (F I + (g.odds : ℂ) * F (g.swap I)) / ((g.odds : ℂ) + 1)

/-- Row I, column J. These are the entries of the normalized identity plus swap. -/
def gateMatrix {d : ℕ} (g : Gate d) : Matrix (Word d) (Word d) ℂ :=
  fun I J =>
    (if I = J then 1 / ((g.odds : ℂ)+1) else 0) +
    (if g.swap I = J then (g.odds : ℂ) / ((g.odds : ℂ)+1) else 0)

def run {d : ℕ} : List (Gate d) → (Word d → ℂ) → Word d → ℂ
  | [], F => F
  | g :: gs, F => gateAction g (run gs F)

private theorem run_append {d : ℕ} (l r : List (Gate d)) (F : Word d → ℂ) :
    run (l ++ r) F = run l (run r F) := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, run, ih]

private theorem run_const {d : ℕ} (l : List (Gate d)) (c : ℂ) (I : Word d) :
    run l (fun _ => c) I = c := by
  induction l generalizing I with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, gateAction, ih]
    have hn : (g.odds : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero g.odds
    field_simp
    ring

private theorem run_affine {d : ℕ} (l : List (Gate d)) (a b : ℂ)
    (F : Word d → ℂ) (I : Word d) :
    run l (fun J => a + b*F J) I = a + b*run l F I := by
  induction l generalizing I with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, gateAction, ih]
    have hn : (g.odds : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero g.odds
    field_simp
    ring

private theorem run_weight {d : ℕ} (l : List (Gate d)) (k : ℕ)
    (F : Word d → ℂ) (I : Word d) :
    run l (fun J => if weight J = k then F J else 0) I =
      if weight I = k then run l F I else 0 := by
  induction l generalizing I with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, gateAction, ih, Gate.swap_weight]
    split <;> simp_all

private theorem run_shift_cons {n : ℕ} (gs : List (Gate n)) (F : Word (n+1) → ℂ)
    (b : Bool) (I : Word n) :
    run (gs.map Gate.shift) F (prepend b I) =
      run gs (fun J => F (prepend b J)) I := by
  induction gs generalizing I with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, run, gateAction, Gate.swap, Gate.odds, prepend, rest,
      Fin.cons_zero, Fin.tail_cons, ih]

private theorem run_shift {n : ℕ} (gs : List (Gate n)) (F : Word (n+1) → ℂ)
    (I : Word (n+1)) :
    run (gs.map Gate.shift) F I =
      run gs (fun J => F (prepend (I 0) J)) (rest I) := by
  simpa only [prepend, rest, Fin.cons_self_tail] using run_shift_cons gs F (I 0) (rest I)

/-- Starting from n+1 labelled bits, draw one uniformly to the head. -/
def draw : (n : ℕ) → List (Gate (n+1))
  | 0 => []
  | n+1 => (draw n).map Gate.shift ++ [Gate.front (n+1)]

theorem draw_head (n : ℕ) (f : Bool → ℂ) (I : Word (n+1)) :
    run (draw n) (fun J => f (J 0)) I = (∑ i, f (I i)) / ((n : ℂ)+1) := by
  induction n with
  | zero => simp [draw, run]
  | succ n ih =>
    rw [draw, run_append, run_shift]
    let A := f (I 0) / ((n : ℂ)+2)
    let B := ((n : ℂ)+1) / ((n : ℂ)+2)
    have hf : (fun J : Word (n+1) =>
        run [Gate.front (n+1)] (fun K => f (K 0)) (prepend (I 0) J)) =
        (fun J => A + B * f (J 0)) := by
      funext J
      simp only [run, gateAction, Gate.swap, Gate.odds, prepend, rest,
        Fin.cons_zero, Fin.tail_cons, Nat.cast_add, Nat.cast_one, A, B]
      ring
    rw [hf, run_affine, ih]
    rw [Fin.sum_univ_succ (fun i => f (I i))]
    dsimp only [A, B, rest, Fin.tail]
    push_cast
    rw [show (n:ℂ)+1+1 = (n:ℂ)+2 by ring]
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn₂ : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
    field_simp

/-- A concrete finite list of adjacent binary gates. -/
def circuit : (d : ℕ) → List (Gate d)
  | 0 => []
  | n+1 => draw n ++ (circuit n).map Gate.shift

private theorem prepend_eq_iff {n : ℕ} (b : Bool) (T : Word n) (J : Word (n+1)) :
    prepend b T = J ↔ b = J 0 ∧ T = rest J := by
  conv_lhs => rhs; rw [← Fin.cons_self_tail J]
  exact Fin.cons_inj

private theorem true_count {d : ℕ} (I : Word d) :
    (∑ i, (if I i = true then (1 : ℂ) else 0)) = (weight I : ℂ) := by
  simp only [weight, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases I i <;> simp

private theorem false_count {d : ℕ} (I : Word d) :
    (∑ i, (if I i = false then (1 : ℂ) else 0)) = (d : ℂ) - (weight I : ℂ) := by
  rw [← true_count]
  calc
    _ = ∑ i : Fin d, (1 - (if I i = true then (1 : ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      cases I i <;> norm_num
    _ = _ := by simp [Finset.sum_sub_distrib]

private theorem choose_ratio_true {n k : ℕ} (hk : k ≤ n) :
    ((k : ℂ)+1) / (n.choose k : ℂ) / ((n : ℂ)+1) =
      1 / ((n+1).choose (k+1) : ℂ) := by
  have h : ((n : ℂ)+1)*(n.choose k : ℂ) =
      ((n+1).choose (k+1) : ℂ)*((k : ℂ)+1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  have h1 : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h2 : ((n+1).choose (k+1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_succ hk)).ne'
  have h3 : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  linear_combination -h

private theorem choose_ratio_false {n k : ℕ} (hk : k ≤ n) :
    ((n : ℂ)+1-k) / (n.choose k : ℂ) / ((n : ℂ)+1) =
      1 / ((n+1).choose k : ℂ) := by
  have hs : k ≤ n+1 := by omega
  have h : (n.choose k : ℂ)*((n : ℂ)+1) =
      ((n+1).choose k : ℂ)*((n : ℂ)+1-k) := by
    have h' := congrArg (fun m : ℕ => (m:ℂ)) (Nat.choose_mul_succ_eq n k)
    simpa only [Nat.cast_mul, Nat.cast_sub hs, Nat.cast_add, Nat.cast_one] using h'
  have h1 : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h2 : ((n+1).choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  have h3 : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  linear_combination -h

/-- The output of the explicit circuit, for every pair of input/output words. -/
theorem circuit_entry (d : ℕ) (I J : Word d) :
    run (circuit d) (fun T => if T = J then 1 else 0) I =
      if weight I = weight J then 1 / (d.choose (weight J) : ℂ) else 0 := by
  classical
  induction d with
  | zero =>
    have h : I = J := Subsingleton.elim ..
    simp [circuit, run, weight, h]
  | succ n ih =>
    let k := weight (rest J)
    have ht (A : Word (n+1)) :
        run ((circuit n).map Gate.shift) (fun T => if T = J then 1 else 0) A =
          if weight A = weight J then
            (if A 0 = J 0 then (1 : ℂ) else 0) / (n.choose k : ℂ) else 0 := by
      rw [run_shift]
      by_cases hb : A 0 = J 0
      · have hw : weight A = weight J ↔ weight (rest A) = weight (rest J) := by
          rw [weight_succ A, weight_succ J, hb, Nat.add_left_cancel_iff]
        simpa only [prepend_eq_iff, hb, true_and, ite_true, hw, k] using
          ih (rest A) (rest J)
      · simp only [prepend_eq_iff, hb, false_and, ite_false, run_const, zero_div, ite_self]
    rw [circuit, run_append, funext ht, run_weight]
    by_cases hw : weight I = weight J
    · simp only [hw, ite_true]
      rw [draw_head n (fun b => (if b = J 0 then (1:ℂ) else 0) / (n.choose k : ℂ))]
      rw [← Finset.sum_div]
      have hk := weight_le (rest J)
      cases hb : J 0 with
      | false =>
        have hj : weight J = k := by simp [weight_succ J, hb, k]
        rw [false_count, hw, hj, Nat.cast_add, Nat.cast_one]
        exact choose_ratio_false hk
      | true =>
        have hj : weight J = k+1 := by simp [weight_succ J, hb, k, Nat.add_comm]
        rw [true_count, hw, hj, Nat.cast_add, Nat.cast_one]
        exact choose_ratio_true hk
    · simp [hw]

private theorem gate_matrix_action {d : ℕ} (g : Gate d) (I : Word d) (F : Word d → ℂ) :
    ∑ J, gateMatrix g I J * F J = gateAction g F I := by
  classical
  simp [gateMatrix, gateAction, add_mul, ite_mul, Finset.sum_add_distrib]
  ring

theorem product_entry {d : ℕ} (l : List (Gate d)) (I J : Word d) :
    (l.map gateMatrix).prod I J = run l (fun T => if T = J then 1 else 0) I := by
  classical
  induction l generalizing I with
  | nil => simp [run, Matrix.one_apply]
  | cons g gs ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, ih, run]
    apply gate_matrix_action

/-- The matrix product itself, including the one-entry empty circuit. -/
theorem symmetrizer_eq_adjacent_product (d : ℕ) (I J : Word d) :
    ((circuit d).map gateMatrix).prod I J =
      if weight I = weight J then 1 / (d.choose (weight I) : ℂ) else 0 := by
  rw [product_entry, circuit_entry]
  split <;> simp_all

/-- A front gate is precisely the physical two-site matrix tensored with
the identity on untouched labelled legs, with its positive normalization. -/
theorem front_matrix_eq_spinor {n : ℕ} (c : ℕ) (a b x y : Bool) (I J : Word n) :
    gateMatrix (Gate.front c) (prepend a (prepend b I)) (prepend x (prepend y J)) =
      if I = J then SpinorGates.exchangeEntry c (a,b) (x,y) / ((c:ℂ)+1) else 0 := by
  classical
  by_cases h : I = J <;> cases a <;> cases b <;> cases x <;> cases y <;>
    simp [gateMatrix, Gate.odds, Gate.swap, prepend, rest, Fin.cons_inj, h,
      SpinorGates.exchangeEntry, add_div]

/-- A shifted gate leaves the labelled head untouched. -/
theorem shift_matrix {n : ℕ} (g : Gate n) (a b : Bool) (I J : Word n) :
    gateMatrix g.shift (prepend a I) (prepend b J) =
      if a = b then gateMatrix g I J else 0 := by
  classical
  by_cases h : a = b <;> simp [gateMatrix, Gate.odds, Gate.swap, prepend,
    rest, Fin.cons_inj, h]

/-- Entrywise identity connecting the physical sphere integral directly to
the finite circuit of normalized nearest-neighbour exchanges. -/
theorem tensorMoment_eq_adjacent_product {d : ℕ} (I J : Word d) :
    BlochSphere.tensorMoment I J =
      ((circuit d).map gateMatrix).prod I J / ((d : ℂ)+1) := by
  rw [BlochSphere.tensorMoment_eq, symmetrizer_eq_adjacent_product]
  change (if weight I = weight J then 1 / (((d:ℂ)+1)*(d.choose (weight I) : ℂ)) else 0) = _
  split <;> simp [*, div_eq_mul_inv, mul_comm]

#print axioms draw_head
#print axioms symmetrizer_eq_adjacent_product
#print axioms tensorMoment_eq_adjacent_product

end IsingScaling.Rotor.HeisenbergField.SymmetrizerExchange
