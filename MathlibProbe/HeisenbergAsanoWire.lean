import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Contracting a binary wire in an open-polydisk Lee–Yang symbol

Fix the spectator variables of a finite network. For two half-edge variables
write its symbol as

  p(z,w) = (A + B z) + (C + D z) w .

The binary trace with damping s keeps the two terms for which the bits agree,
giving A + s D. Suppose p is nonzero for all z,w in the open unit disk.
The value at (0,0) shows A is nonzero. For an affine polynomial a+bw without
a zero there, |b| ≤ |a| follows by testing the possible zero -a/b. Applying
this with z fixed gives |C+Dz| ≤ |A+Bz|, up to the closed disk by continuity.
Square this inequality at z = 1 and z = -1 and add. The parallelogram law
gives |C|²+|D|² ≤ |A|²+|B|². Interchanging z and w gives the other inequality,
so |D| ≤ |A|. Hence |A+sD| ≥ (1-|s|)|A|, strictly positive for |s| < 1.

For the physical boundary value s = 1 let the spectator parameter range over
a connected open set, with A and D holomorphic there. The quotient D/A has
modulus at most one. A zero of A+D forces the quotient to equal -1 and to
attain its maximum modulus at an interior point. The maximum modulus principle
makes the quotient constant throughout the set. Thus a single nonzero value
of A+D anywhere on the set implies nonvanishing everywhere on it. The stable
symbol 1-zw illustrates the possible identically zero boundary contraction.

For any finite number of wires the coefficients form a four-branch tensor
tree, one branch for each pair of bits at a wire. The finite recursion below
replaces the 00 and 11 branches by their damped sum, dropping 10 and 01. At
each step the two-variable theorem applies with all uncontracted half-edge
activities fixed arbitrarily in the open disk. No stability assumption on any
individual tensor coefficient at an intermediate step is required.

A partial exchange of two row activities averages B and C with weights
1−θ, θ, and keeps A and D. At any fixed z the new squared slice gap
|A+B'z|²−|C'+Dz|² equals the weighted mean of the original gap and its
transposed counterpart plus θ(1−θ)(1−|z|²)|B−C|². The two old gaps are
nonnegative in the disk. Also |B'| ≤ |A|, since the two original one-variable
restrictions give |B|,|C| ≤ |A|. Thus A+B'z stays nonzero and its modulus
dominates |C'+Dz|, so the new symbol stays nonzero throughout the bidisk.
-/

namespace MathlibProbe.HeisenbergAsanoWire

open Set

/-- Symbol of two binary legs at fixed spectator activities. -/
def biAffine (A B C D z w : ℂ) : ℂ := (A + B * z) + (C + D * z) * w

/-- All spectator variables have already been fixed in their admissible domains. -/
def StablePair (A B C D : ℂ) : Prop :=
  ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → biAffine A B C D z w ≠ 0

private theorem affine_bound {a b : ℂ}
    (h : ∀ w : ℂ, ‖w‖ < 1 → a + b * w ≠ 0) : ‖b‖ ≤ ‖a‖ := by
  by_contra! hlt
  have hb : b ≠ 0 := norm_pos_iff.mp ((norm_nonneg a).trans_lt hlt)
  have hw : ‖-a / b‖ < 1 := by
    rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr hb)]
    exact hlt
  apply h (-a / b) hw
  field_simp
  ring

theorem stablePair_swap {A B C D : ℂ} (h : StablePair A B C D) :
    StablePair A C B D := by
  intro z w hz hw
  have he : biAffine A C B D z w = biAffine A B C D w z := by
    unfold biAffine
    ring
  rw [he]
  exact h w z hw hz

theorem constant_ne_zero {A B C D : ℂ} (h : StablePair A B C D) : A ≠ 0 := by
  simpa [biAffine] using h 0 0 (by simp) (by simp)

private theorem slice_bound {A B C D : ℂ} (h : StablePair A B C D)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖C + D * z‖ ≤ ‖A + B * z‖ := by
  have hinter (x : ℂ) (hx : x ∈ Metric.ball (0 : ℂ) 1) :
      ‖C + D * x‖ ≤ ‖A + B * x‖ :=
    affine_bound fun w hw => h x w (mem_ball_zero_iff.mp hx) hw
  have hz' : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact mem_closedBall_zero_iff.mpr hz
  exact le_on_closure hinter (by fun_prop) (by fun_prop) hz'

private theorem mean_square_bound {A B C D : ℂ} (h : StablePair A B C D) :
    ‖C‖ ^ 2 + ‖D‖ ^ 2 ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  have hp : ‖C + D‖ ≤ ‖A + B‖ := by
    simpa using slice_bound h (z := (1 : ℂ)) (by simp)
  have hm : ‖C - D‖ ≤ ‖A - B‖ := by
    simpa [sub_eq_add_neg] using slice_bound h (z := (-1 : ℂ)) (by simp)
  have hsq := add_le_add (pow_le_pow_left₀ (norm_nonneg _) hp 2)
    (pow_le_pow_left₀ (norm_nonneg _) hm 2)
  rw [parallelogram_law_with_norm ℝ C D, parallelogram_law_with_norm ℝ A B] at hsq
  linarith

/-- Sharp coefficient estimate for an open-bidisk stable multiaffine symbol. -/
theorem diagonal_norm_le {A B C D : ℂ} (h : StablePair A B C D) : ‖D‖ ≤ ‖A‖ := by
  have h₁ := mean_square_bound h
  have h₂ := mean_square_bound (stablePair_swap h)
  exact (sq_le_sq₀ (norm_nonneg D) (norm_nonneg A)).mp (by linarith)

/-- Pointwise lower bound for the damped trace. -/
theorem contract_norm_lower {A B C D : ℂ} (h : StablePair A B C D) (s : ℂ) :
    (1 - ‖s‖) * ‖A‖ ≤ ‖A + s * D‖ := by
  have h₁ : ‖A‖ ≤ ‖A + s * D‖ + ‖s * D‖ := by
    simpa using norm_sub_le (A + s * D) (s * D)
  have h₂ := mul_le_mul_of_nonneg_left (diagonal_norm_le h) (norm_nonneg s)
  rw [norm_mul] at h₁
  nlinarith

/-- Asano contraction for the full open disk of wire activities. -/
theorem contract_nonzero {A B C D s : ℂ} (h : StablePair A B C D) (hs : ‖s‖ < 1) :
    A + s * D ≠ 0 :=
  norm_pos_iff.mp <| (mul_pos (sub_pos.mpr hs) (norm_pos_iff.mpr (constant_ne_zero h))).trans_le
    (contract_norm_lower h s)

/-- Weights used by a partial exchange of two sites. -/
def partialMix (θ : ℝ) (x y : ℂ) : ℂ := ((1 - θ : ℝ) : ℂ) * x + (θ : ℂ) * y

/-- Algebraic squared gap identity for the two transposed rows. -/
theorem partialMix_gap (θ : ℝ) (A B C D z : ℂ) :
    ‖A + partialMix θ B C * z‖ ^ 2 - ‖partialMix θ C B + D * z‖ ^ 2 =
      (1 - θ) * (‖A + B * z‖ ^ 2 - ‖C + D * z‖ ^ 2) +
      θ * (‖A + C * z‖ ^ 2 - ‖B + D * z‖ ^ 2) +
      θ * (1 - θ) * (1 - ‖z‖ ^ 2) * ‖B - C‖ ^ 2 := by
  simp only [partialMix, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

private theorem affine_nonzero {a b w : ℂ} (ha : a ≠ 0) (hab : ‖b‖ ≤ ‖a‖)
    (hw : ‖w‖ < 1) : a + b * w ≠ 0 := by
  intro he
  have he' : b * w = -a := by linear_combination he
  have hlt : ‖b * w‖ < ‖a‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hab (norm_nonneg w)).trans_lt (by
      simpa using mul_lt_mul_of_pos_left hw (norm_pos_iff.mpr ha))
  simp [he'] at hlt

/-- Partial symmetrization of either order of the two independently variable legs. -/
theorem stablePair_partialSym {A B C D : ℂ} (h : StablePair A B C D)
    {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    StablePair A (partialMix θ B C) (partialMix θ C B) D := by
  have hA := constant_ne_zero h
  have hb : ‖B‖ ≤ ‖A‖ := by simpa using slice_bound (stablePair_swap h) (z := 0) (by simp)
  have hc : ‖C‖ ≤ ‖A‖ := by simpa using slice_bound h (z := 0) (by simp)
  have hθ : 0 ≤ 1 - θ := sub_nonneg.mpr h₁
  have hb' : ‖partialMix θ B C‖ ≤ ‖A‖ := by
    unfold partialMix
    calc
      _ ≤ ‖((1-θ : ℝ) : ℂ) * B‖ + ‖(θ : ℂ) * C‖ := norm_add_le _ _
      _ = (1-θ) * ‖B‖ + θ * ‖C‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ, abs_of_nonneg h₀]
      _ ≤ (1-θ) * ‖A‖ + θ * ‖A‖ := add_le_add (mul_le_mul_of_nonneg_left hb hθ)
        (mul_le_mul_of_nonneg_left hc h₀)
      _ = ‖A‖ := by ring
  intro z w hz hw
  have hg₁ := sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (slice_bound h hz.le) 2)
  have hg₂ := sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _)
    (slice_bound (stablePair_swap h) hz.le) 2)
  have hz₂ : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖, norm_nonneg z]
  have hgap := partialMix_gap θ A B C D z
  have hg : ‖partialMix θ C B + D * z‖ ^ 2 ≤ ‖A + partialMix θ B C * z‖ ^ 2 := by
    linarith [mul_nonneg hθ hg₁, mul_nonneg h₀ hg₂,
      mul_nonneg (mul_nonneg (mul_nonneg h₀ hθ) hz₂) (sq_nonneg ‖B-C‖)]
  exact affine_nonzero (affine_nonzero hA hb' hz)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hg) hw

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- At the undamped physical wire the boundary symbol is either nonzero everywhere
on the connected open domain of spectator fields, or identically zero there. -/
theorem boundary_eq_zero_of_zero {U : Set E} (hconn : IsPreconnected U) (hopen : IsOpen U)
    {A B C D : E → ℂ} (hA : DifferentiableOn ℂ A U) (hD : DifferentiableOn ℂ D U)
    (hst : ∀ x ∈ U, StablePair (A x) (B x) (C x) (D x))
    {x₀ : E} (hx₀ : x₀ ∈ U) (hz : A x₀ + D x₀ = 0) :
    ∀ x ∈ U, A x + D x = 0 := by
  let q : E → ℂ := fun x => D x / A x
  have hA₀ : ∀ x ∈ U, A x ≠ 0 := fun x hx => constant_ne_zero (hst x hx)
  have hhol : DifferentiableOn ℂ q U := by
    simp only [q, div_eq_mul_inv]
    exact hD.mul (hA.inv hA₀)
  have hq : ∀ x ∈ U, ‖q x‖ ≤ 1 := by
    intro x hx
    change ‖D x / A x‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hA₀ x hx))]
    exact diagonal_norm_le (hst x hx)
  have hval : q x₀ = -1 := by
    change D x₀ / A x₀ = -1
    apply (div_eq_iff (hA₀ x₀ hx₀)).2
    linear_combination hz
  have hm : IsMaxOn (norm ∘ q) U x₀ := by
    intro x hx
    change ‖q x‖ ≤ ‖q x₀‖
    simpa [hval] using hq x hx
  have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn hopen hhol hx₀ hm
  intro x hx
  have he : q x = -1 := (hc hx).trans hval
  have hDx := (div_eq_iff (hA₀ x hx)).1 he
  linear_combination hDx

/-- A single nonzero reference field rules out the identically zero case. -/
theorem boundary_nonzero_of_anchor {U : Set E} (hconn : IsPreconnected U) (hopen : IsOpen U)
    {A B C D : E → ℂ} (hA : DifferentiableOn ℂ A U) (hD : DifferentiableOn ℂ D U)
    (hst : ∀ x ∈ U, StablePair (A x) (B x) (C x) (D x))
    {anchor : E} (ha : anchor ∈ U) (href : A anchor + D anchor ≠ 0) :
    ∀ x ∈ U, A x + D x ≠ 0 := by
  intro x hx hz
  exact href (boundary_eq_zero_of_zero hconn hopen hA hD hst hx hz anchor ha)

end Boundary

/-- Calibration of the boundary exception on the stable symbol 1-zw. -/
theorem stable_vanishing_boundary_example : StablePair 1 0 0 (-1) ∧ (1 : ℂ) + (-1) = 0 := by
  refine ⟨?_, by norm_num⟩
  intro z w hz hw he
  have hzw : z * w = 1 := by
    unfold biAffine at he
    linear_combination -he
  have hlt : ‖z * w‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hz.le (norm_nonneg w)).trans_lt (by simpa using hw)
  simp [hzw] at hlt

section FiniteNetwork

/-- Ordered slots, with the first wire outermost. -/
def Slots (α : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => α × Slots α n

/-- A binary network coefficient for every assignment of the two bits on each wire. -/
abbrev Coefficients (n : ℕ) := Slots (Bool × Bool) n → ℂ

noncomputable section

/-- Independently variable half-edge activities prior to identifying the two bits. -/
def networkSymbol : (n : ℕ) → Coefficients n → Slots (ℂ × ℂ) n → ℂ
  | 0, c, _ => c ()
  | n + 1, c, z =>
      biAffine
        (networkSymbol n (fun b => c ((false, false), b)) z.2)
        (networkSymbol n (fun b => c ((true, false), b)) z.2)
        (networkSymbol n (fun b => c ((false, true), b)) z.2)
        (networkSymbol n (fun b => c ((true, true), b)) z.2) z.1.1 z.1.2

/-- The independent open-polydisk conditions on the remaining slots. -/
def OpenSlots : (n : ℕ) → Slots (ℂ × ℂ) n → Prop
  | 0, _ => True
  | n + 1, z => ‖z.1.1‖ < 1 ∧ ‖z.1.2‖ < 1 ∧ OpenSlots n z.2

/-- Stability of the physical symbol on the full open polydisk. -/
def NetworkStable (n : ℕ) (c : Coefficients n) : Prop :=
  ∀ v, OpenSlots n v → networkSymbol n c v ≠ 0

theorem networkSymbol_linear (n : ℕ) (c d : Coefficients n) (s : ℂ) (v : Slots (ℂ × ℂ) n) :
    networkSymbol n (fun b => c b + s * d b) v =
      networkSymbol n c v + s * networkSymbol n d v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [networkSymbol, ih, biAffine]
    ring

/-- The honest binary trace over the leading slot, coefficient by coefficient. -/
def contractHead (n : ℕ) (s : ℂ) (c : Coefficients (n + 1)) : Coefficients n :=
  fun b => c ((false, false), b) + s * c ((true, true), b)

/-- The remaining complete coefficient array has a stable symbol after contraction. -/
theorem contractHead_stable {n : ℕ} {c : Coefficients (n + 1)} (hc : NetworkStable (n + 1) c)
    {s : ℂ} (hs : ‖s‖ < 1) : NetworkStable n (contractHead n s c) := by
  intro v hv
  have hpair : StablePair
      (networkSymbol n (fun b => c ((false, false), b)) v)
      (networkSymbol n (fun b => c ((true, false), b)) v)
      (networkSymbol n (fun b => c ((false, true), b)) v)
      (networkSymbol n (fun b => c ((true, true), b)) v) := by
    intro z w hz hw
    exact hc ((z, w), v) ⟨hz, hw, hv⟩
  unfold contractHead
  rw [networkSymbol_linear]
  exact contract_nonzero hpair hs

/-- The open disk for every independent binary-wire fugacity. -/
def OpenDampings : (n : ℕ) → Slots ℂ n → Prop
  | 0, _ => True
  | n + 1, t => ‖t.1‖ < 1 ∧ OpenDampings n t.2

/-- Close all wires by successively summing only equal end bits. -/
def closeDamped : (n : ℕ) → Slots ℂ n → Coefficients n → ℂ
  | 0, _, c => c ()
  | n + 1, t, c => closeDamped n t.2 (contractHead n t.1 c)

/-- Finite Asano contraction for an arbitrary number of wires and complex dampings. -/
theorem closeDamped_nonzero (n : ℕ) (t : Slots ℂ n) (c : Coefficients n)
    (ht : OpenDampings n t) (hc : NetworkStable n c) : closeDamped n t c ≠ 0 := by
  induction n with
  | zero => exact hc () trivial
  | succ n ih => exact ih t.2 _ ht.2 (contractHead_stable hc ht.1)

/-- Expansion of the damped partition sum directly in the diagonal binary assignments. -/
def diagonalTrace : (n : ℕ) → Slots ℂ n → Coefficients n → ℂ
  | 0, _, c => c ()
  | n + 1, t, c =>
    diagonalTrace n t.2 (fun b => c ((false, false), b)) +
      t.1 * diagonalTrace n t.2 (fun b => c ((true, true), b))

theorem diagonalTrace_linear (n : ℕ) (t : Slots ℂ n) (c d : Coefficients n) (s : ℂ) :
    diagonalTrace n t (fun b => c b + s * d b) =
      diagonalTrace n t c + s * diagonalTrace n t d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [diagonalTrace, ih]
    ring

theorem closeDamped_eq_diagonalTrace (n : ℕ) (t : Slots ℂ n) (c : Coefficients n) :
    closeDamped n t c = diagonalTrace n t c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [closeDamped, ih, diagonalTrace]
    exact diagonalTrace_linear n t.2 (fun b => c ((false, false), b))
      (fun b => c ((true, true), b)) t.1

/-- Finite products of stable gate symbols give a nonvanishing binary partition sum
once their product has been identified with the open-leg network symbol. -/
theorem diagonalTrace_nonzero_of_gate_product {ι : Type*} [Fintype ι] (n : ℕ) (t : Slots ℂ n)
    (c : Coefficients n) (gate : ι → Slots (ℂ × ℂ) n → ℂ)
    (product_symbol : ∀ v, networkSymbol n c v = ∏ j, gate j v)
    (gate_nonzero : ∀ j v, OpenSlots n v → gate j v ≠ 0) (ht : OpenDampings n t) :
    diagonalTrace n t c ≠ 0 := by
  rw [← closeDamped_eq_diagonalTrace]
  apply closeDamped_nonzero n t c ht
  intro v hv
  rw [product_symbol]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => gate_nonzero j v hv

/-- Equivalence with wire-indexed arrays. Its initial coordinate is the outermost wire. -/
def slotsEquiv (α : Type) : (n : ℕ) → Slots α n ≃ (Fin n → α)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun _ => funext (fun i => Fin.elim0 i) }
  | n + 1 =>
    ((Equiv.refl α).prodCongr (slotsEquiv α n)).trans (Fin.consEquiv fun _ => α)

@[simp] theorem slotsEquiv_cons {α : Type} {n : ℕ} (a : α) (v : Slots α n) :
    slotsEquiv α (n + 1) (a, v) = Fin.cons a (slotsEquiv α n v) := rfl

/-- A half-edge activity contributes its value exactly at bit one. -/
def bitFactor (z : ℂ) (b : Bool) : ℂ := if b then z else 1

/-- Dense contraction of an array against independent single-slot weights. -/
def denseSum {β : Type} [Fintype β] (n : ℕ) (c : (Fin n → β) → ℂ)
    (weight : Fin n → β → ℂ) : ℂ :=
  ∑ ξ : Fin n → β, c ξ * ∏ j, weight j (ξ j)

private theorem denseSum_succ {β : Type} [Fintype β] (n : ℕ)
    (c : (Fin (n + 1) → β) → ℂ) (weight : Fin (n + 1) → β → ℂ) :
    denseSum (n + 1) c weight =
      ∑ head : β, weight 0 head *
        denseSum n (fun tail => c (Fin.cons head tail)) (fun j => weight j.succ) := by
  classical
  unfold denseSum
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => β)
      (fun ξ => c ξ * ∏ j, weight j (ξ j)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro head _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  rw [Fin.prod_univ_succ]
  change c (Fin.cons (α := fun _ => β) head tail) *
    (weight 0 (Fin.cons (α := fun _ => β) head tail 0) *
      ∏ j : Fin n, weight j.succ (Fin.cons (α := fun _ => β) head tail j.succ)) = _
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- Open-leg partition sum over all assignments of the two endpoint bits of each wire. -/
def denseSymbol (n : ℕ) (c : (Fin n → Bool × Bool) → ℂ) (v : Fin n → ℂ × ℂ) : ℂ :=
  denseSum n c fun j bit => bitFactor (v j).1 bit.1 * bitFactor (v j).2 bit.2

private theorem denseSymbol_succ (n : ℕ) (c : (Fin (n + 1) → Bool × Bool) → ℂ)
    (v : Fin (n + 1) → ℂ × ℂ) :
    denseSymbol (n + 1) c v =
      biAffine
        (denseSymbol n (fun tail => c (Fin.cons (false, false) tail)) (Fin.tail v))
        (denseSymbol n (fun tail => c (Fin.cons (true, false) tail)) (Fin.tail v))
        (denseSymbol n (fun tail => c (Fin.cons (false, true) tail)) (Fin.tail v))
        (denseSymbol n (fun tail => c (Fin.cons (true, true) tail)) (Fin.tail v))
        (v 0).1 (v 0).2 := by
  unfold denseSymbol
  rw [denseSum_succ, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, bitFactor, Bool.false_eq_true, ↓reduceIte, Fin.tail_def, biAffine]
  ring

theorem networkSymbol_eq_denseSymbol (n : ℕ) (c : (Fin n → Bool × Bool) → ℂ)
    (v : Slots (ℂ × ℂ) n) :
    networkSymbol n (fun b => c (slotsEquiv _ n b)) v = denseSymbol n c (slotsEquiv _ n v) := by
  induction n with
  | zero =>
    simp [networkSymbol, denseSymbol, denseSum]
    exact congrArg c (Subsingleton.elim _ _)
  | succ n ih =>
    rcases v with ⟨zw, v⟩
    rw [denseSymbol_succ]
    simp only [networkSymbol, slotsEquiv_cons, Fin.cons_zero, Fin.tail_cons]
    exact congrArg₂ (fun a b => biAffine a b
      (networkSymbol n (fun tail => c (Fin.cons (false, true) (slotsEquiv _ n tail))) v)
      (networkSymbol n (fun tail => c (Fin.cons (true, true) (slotsEquiv _ n tail))) v)
      zw.1 zw.2) (ih (fun t => c (Fin.cons (false, false) t)) v)
      (ih (fun t => c (Fin.cons (true, false) t)) v) |>.trans (by
        rw [ih (fun t => c (Fin.cons (false, true) t)) v,
          ih (fun t => c (Fin.cons (true, true) t)) v])

/-- Closed equal-bit partition sum. At every wire one Boolean is shared between its ends. -/
def denseTrace (n : ℕ) (c : (Fin n → Bool × Bool) → ℂ) (t : Fin n → ℂ) : ℂ :=
  denseSum n (fun b => c (fun j => (b j, b j))) (fun j b => bitFactor (t j) b)

/-- The undamped finite network sums the diagonal coefficients with weight one. -/
theorem denseTrace_one (n : ℕ) (c : (Fin n → Bool × Bool) → ℂ) :
    denseTrace n c (fun _ => 1) = ∑ b : Fin n → Bool, c (fun j => (b j, b j)) := by
  simp [denseTrace, denseSum, bitFactor]

private theorem double_cons {n : ℕ} (a : Bool) (b : Fin n → Bool) :
    (fun i : Fin (n + 1) => (Fin.cons (α := fun _ => Bool) a b i,
      Fin.cons (α := fun _ => Bool) a b i)) =
      Fin.cons (α := fun _ => Bool × Bool) (a, a) (fun i => (b i, b i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem denseTrace_succ (n : ℕ) (c : (Fin (n + 1) → Bool × Bool) → ℂ)
    (t : Fin (n + 1) → ℂ) :
    denseTrace (n + 1) c t =
      denseTrace n (fun tail => c (Fin.cons (false, false) tail)) (Fin.tail t) +
        t 0 * denseTrace n (fun tail => c (Fin.cons (true, true) tail)) (Fin.tail t) := by
  unfold denseTrace
  rw [denseSum_succ]
  simp only [Fintype.sum_bool, bitFactor, Bool.false_eq_true, ↓reduceIte, Fin.tail_def, double_cons]
  ring

theorem diagonalTrace_eq_denseTrace (n : ℕ) (t : Slots ℂ n) (c : (Fin n → Bool × Bool) → ℂ) :
    diagonalTrace n t (fun b => c (slotsEquiv _ n b)) = denseTrace n c (slotsEquiv _ n t) := by
  induction n with
  | zero =>
    simp [diagonalTrace, denseTrace, denseSum]
    exact congrArg c (Subsingleton.elim _ _)
  | succ n ih =>
    rcases t with ⟨z, t⟩
    rw [denseTrace_succ]
    simp only [diagonalTrace, slotsEquiv_cons, Fin.cons_zero, Fin.tail_cons]
    rw [ih t (fun tail => c (Fin.cons (false, false) tail)),
      ih t (fun tail => c (Fin.cons (true, true) tail))]

private theorem openSlots_iff (n : ℕ) (v : Slots (ℂ × ℂ) n) :
    OpenSlots n v ↔ ∀ i : Fin n,
      ‖(slotsEquiv _ n v i).1‖ < 1 ∧ ‖(slotsEquiv _ n v i).2‖ < 1 := by
  induction n with
  | zero => simp [OpenSlots]
  | succ n ih =>
    rcases v with ⟨zw, v⟩
    simp only [OpenSlots, slotsEquiv_cons, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      ← ih, and_assoc]

private theorem openDampings_iff (n : ℕ) (t : Slots ℂ n) :
    OpenDampings n t ↔ ∀ i : Fin n, ‖slotsEquiv _ n t i‖ < 1 := by
  induction n with
  | zero => simp [OpenDampings]
  | succ n ih =>
    rcases t with ⟨z, t⟩
    simp only [OpenDampings, slotsEquiv_cons, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      ← ih]

/-- Fin-indexed Asano theorem. Both its input and output are the literal dense
finite partition sums of the same coefficient array, with independent and with
identified wire-end bits, respectively. -/
theorem denseTrace_nonzero (n : ℕ) (c : (Fin n → Bool × Bool) → ℂ) (t : Fin n → ℂ)
    (hst : ∀ v : Fin n → ℂ × ℂ, (∀ i, ‖(v i).1‖ < 1 ∧ ‖(v i).2‖ < 1) →
      denseSymbol n c v ≠ 0) (ht : ∀ i, ‖t i‖ < 1) : denseTrace n c t ≠ 0 := by
  let t' := (slotsEquiv ℂ n).symm t
  have hde : slotsEquiv ℂ n t' = t := (slotsEquiv ℂ n).apply_symm_apply _
  have hs : NetworkStable n (fun b => c (slotsEquiv _ n b)) := by
    intro v hv
    rw [networkSymbol_eq_denseSymbol]
    exact hst _ ((openSlots_iff n v).1 hv)
  have had : OpenDampings n t' := (openDampings_iff n t').2 (by rwa [hde])
  have h := closeDamped_nonzero n t' _ had hs
  rwa [closeDamped_eq_diagonalTrace, diagonalTrace_eq_denseTrace, hde] at h

/-- Transpose the row ends of two wires. Every column end stays at its original index. -/
def swapRows {n : ℕ} {α β : Type} (i j : Fin n) (v : Fin n → α × β) : Fin n → α × β :=
  fun k => ((v (Equiv.swap i j k)).1, (v k).2)

theorem swapRows_involutive {n : ℕ} {α β : Type} (i j : Fin n) :
    Function.Involutive (swapRows (α := α) (β := β) i j) := by
  intro v
  funext k
  simp [swapRows, Equiv.swap_apply_self]

/-- Convex partial exchange acting on the actual dense coefficient (matrix entry). -/
def partialRowExchange {n : ℕ} (i j : Fin n) (θ : ℝ)
    (c : (Fin n → Bool × Bool) → ℂ) (bits : Fin n → Bool × Bool) : ℂ :=
  partialMix θ (c bits) (c (swapRows i j bits))

private def legWeight {n : ℕ} (v : Fin n → ℂ × ℂ) (b : Fin n → Bool × Bool) : ℂ :=
  ∏ k, bitFactor (v k).1 (b k).1 * bitFactor (v k).2 (b k).2

private theorem legWeight_swapRows {n : ℕ} (i j : Fin n) (v : Fin n → ℂ × ℂ)
    (ξ : Fin n → Bool × Bool) : legWeight v (swapRows i j ξ) = legWeight (swapRows i j v) ξ := by
  unfold legWeight swapRows
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  exact Fintype.prod_equiv (Equiv.swap i j) _ _ (by
    intro k
    simp [Equiv.swap_apply_self])

theorem denseSymbol_swapRows {n : ℕ} (i j : Fin n) (c : (Fin n → Bool × Bool) → ℂ)
    (v : Fin n → ℂ × ℂ) :
    denseSymbol n (fun b => c (swapRows i j b)) v = denseSymbol n c (swapRows i j v) := by
  change (∑ b, c (swapRows i j b) * legWeight v b) =
    ∑ b, c b * legWeight (swapRows i j v) b
  let e := (swapRows_involutive (α := Bool) (β := Bool) i j).toPerm _
  apply Fintype.sum_equiv e
  intro b
  change c (swapRows i j b) * legWeight v b =
    c (swapRows i j b) * legWeight (swapRows i j v) (swapRows i j b)
  rw [← legWeight_swapRows, swapRows_involutive i j]

/-- Thus an exchange of dense row bits evaluates to the same exchange of row variables. -/
theorem denseSymbol_partialRowExchange {n : ℕ} (i j : Fin n) (θ : ℝ)
    (c : (Fin n → Bool × Bool) → ℂ) (v : Fin n → ℂ × ℂ) :
    denseSymbol n (partialRowExchange i j θ c) v =
      partialMix θ (denseSymbol n c v) (denseSymbol n c (swapRows i j v)) := by
  rw [← denseSymbol_swapRows]
  change (∑ b, partialMix θ (c b) (c (swapRows i j b)) * legWeight v b) =
    partialMix θ (∑ b, c b * legWeight v b) (∑ b, c (swapRows i j b) * legWeight v b)
  simp only [partialMix, add_mul, mul_assoc, Finset.mul_sum, Finset.sum_add_distrib]

private def twoRows {n : ℕ} (i j : Fin n) (v : Fin n → ℂ × ℂ) (z w : ℂ)
    (k : Fin n) : ℂ × ℂ :=
  (if k = i then z else if k = j then w else (v k).1, (v k).2)

@[simp] private theorem bitFactor_one (b : Bool) : bitFactor 1 b = 1 := by cases b <;> rfl

private theorem legWeight_twoRows {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (v : Fin n → ℂ × ℂ) (z w : ℂ) (b : Fin n → Bool × Bool) :
    legWeight (twoRows i j v z w) b =
      bitFactor z (b i).1 * bitFactor w (b j).1 * legWeight (twoRows i j v 1 1) b := by
  classical
  unfold legWeight
  have hterm (k : Fin n) :
      bitFactor (twoRows i j v z w k).1 (b k).1 * bitFactor (twoRows i j v z w k).2 (b k).2 =
      ((if k = i then bitFactor z (b i).1 else 1) *
       (if k = j then bitFactor w (b j).1 else 1)) *
       (bitFactor (twoRows i j v 1 1 k).1 (b k).1 * bitFactor (twoRows i j v 1 1 k).2 (b k).2) := by
    by_cases hi : k = i
    · subst k
      simp [twoRows, hij]
    by_cases hj : k = j
    · subst k
      simp [twoRows, hij.symm]
    simp [twoRows, hi, hj]
  simp_rw [hterm]
  simp only [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

private theorem sum_biAffine {ι : Type} [Fintype ι] (a b c d : ι → ℂ) (z w : ℂ) :
    (∑ l, biAffine (a l) (b l) (c l) (d l) z w) =
      biAffine (∑ l, a l) (∑ l, b l) (∑ l, c l) (∑ l, d l) z w := by
  simp only [biAffine, add_mul, Finset.sum_mul, Finset.sum_add_distrib]

/-- The dense binary symbol is genuinely multiaffine in every two separate row ends. -/
private theorem denseSymbol_twoRows {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (c : (Fin n → Bool × Bool) → ℂ) (v : Fin n → ℂ × ℂ) :
    ∃ A B C D : ℂ, ∀ z w, denseSymbol n c (twoRows i j v z w) = biAffine A B C D z w := by
  let k (p q : Bool) (b : Fin n → Bool × Bool) : ℂ :=
    if (b i).1 = p ∧ (b j).1 = q then c b * legWeight (twoRows i j v 1 1) b else 0
  refine ⟨∑ b, k false false b, ∑ b, k true false b, ∑ b, k false true b,
    ∑ b, k true true b, ?_⟩
  intro z w
  rw [← sum_biAffine]
  change (∑ b, c b * legWeight (twoRows i j v z w) b) = _
  apply Finset.sum_congr rfl
  intro b _
  rw [legWeight_twoRows i j hij]
  cases hi : (b i).1 <;> cases hj : (b j).1 <;> simp [k, hi, hj, bitFactor, biAffine] <;> ring

/-- Stability under exchange of any two row ends, with all column ends and
the other row ends independently variable in the disk. -/
theorem denseSymbol_partialRowExchange_nonzero {n : ℕ} (i j : Fin n) {θ : ℝ}
    (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) (c : (Fin n → Bool × Bool) → ℂ)
    (hst : ∀ v : Fin n → ℂ × ℂ, (∀ k, ‖(v k).1‖ < 1 ∧ ‖(v k).2‖ < 1) →
      denseSymbol n c v ≠ 0) (v : Fin n → ℂ × ℂ)
    (hv : ∀ k, ‖(v k).1‖ < 1 ∧ ‖(v k).2‖ < 1) :
    denseSymbol n (partialRowExchange i j θ c) v ≠ 0 := by
  rw [denseSymbol_partialRowExchange]
  by_cases hij : i = j
  · subst j
    have hr : swapRows i i v = v := by ext k <;> simp [swapRows]
    rw [hr]
    convert! hst v hv using 1
    unfold partialMix
    push_cast
    ring
  obtain ⟨A, B, C, D, hchart⟩ := denseSymbol_twoRows i j hij c v
  have hp : StablePair A B C D := by
    intro z w hz hw
    rw [← hchart]
    apply hst
    intro k
    refine ⟨?_, (hv k).2⟩
    change ‖if k = i then z else if k = j then w else (v k).1‖ < 1
    split_ifs <;> first | assumption | exact (hv k).1
  have hv₁ : twoRows i j v (v i).1 (v j).1 = v := by
    funext k
    by_cases hi : k = i
    · subst k
      simp [twoRows]
    by_cases hj : k = j
    · subst k
      simp [twoRows, hi]
    simp [twoRows, hi, hj]
  have hv₂ : twoRows i j v (v j).1 (v i).1 = swapRows i j v := by
    funext k
    by_cases hi : k = i
    · subst k
      simp [twoRows, swapRows]
    by_cases hj : k = j
    · subst k
      simp [twoRows, swapRows, hi]
    simp [twoRows, swapRows, hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]
  have he₁ := hchart (v i).1 (v j).1
  have he₂ := hchart (v j).1 (v i).1
  rw [hv₁] at he₁
  rw [hv₂] at he₂
  rw [he₁, he₂]
  have hm : partialMix θ (biAffine A B C D (v i).1 (v j).1)
      (biAffine A B C D (v j).1 (v i).1) =
      biAffine A (partialMix θ B C) (partialMix θ C B) D (v i).1 (v j).1 := by
    unfold partialMix biAffine
    push_cast
    ring
  rw [hm]
  exact stablePair_partialSym hp h₀ h₁ _ _ (hv i).1 (hv j).1

end
end FiniteNetwork

end MathlibProbe.HeisenbergAsanoWire
