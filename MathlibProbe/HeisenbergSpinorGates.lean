import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # Disk stability of the classical Heisenberg exchange factor

For spinor projections P and Q the matrix I + c Swap has expectation
1 + c tr(PQ). Its boundary polynomial can be divided by two nonzero
factors. The resulting expression is a positive combination of two
points of a disk avoiding zero. This proof applies to every c ≥ 0.
-/

noncomputable section
open scoped ComplexConjugate

namespace IsingScaling.Rotor.HeisenbergField.SpinorGates

/-- A binary index contributes its half-edge variable at bit one. -/
def leg (x : ℂ) (i : Bool) : ℂ := if i then x else 1

/-- Matrix element of I+c Swap. Bit false denotes the positive field spinor. -/
def exchangeEntry (c : ℝ) (i j : Bool × Bool) : ℂ :=
  (if i=j then 1 else 0) + (c : ℂ) * (if i=(j.2,j.1) then 1 else 0)

/-- Two outgoing and two incoming boundary spinors. -/
def twoLegSymbol (M : (Bool × Bool) → (Bool × Bool) → ℂ) (x u w v : ℂ) : ℂ :=
  ∑ a : Bool, ∑ b : Bool, ∑ k : Bool, ∑ l : Bool,
    M (a,b) (k,l) * leg x a * leg u b * leg w k * leg v l

theorem exchange_symbol (c : ℝ) (x u w v : ℂ) :
    twoLegSymbol (exchangeEntry c) x u w v =
      (1+x*w)*(1+u*v)+(c : ℂ)*(1+x*v)*(1+u*w) := by
  simp [twoLegSymbol, exchangeEntry, leg]
  ring

private theorem disk_gap (x y : ℂ) :
    ‖1-x*y‖^2 - ‖conj x-y‖^2 = (1-‖x‖^2)*(1-‖y‖^2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem disk_lt {x y : ℂ} (hx : ‖x‖<1) (hy : ‖y‖<1) :
    ‖conj x-y‖ < ‖1-x*y‖ := by
  have px : 0 < 1-‖x‖^2 := by nlinarith [norm_nonneg x, sq_lt_sq' (by linarith [norm_nonneg x]) hx]
  have py : 0 < 1-‖y‖^2 := by nlinarith [norm_nonneg y, sq_lt_sq' (by linarith [norm_nonneg y]) hy]
  nlinarith [disk_gap x y, mul_pos px py, norm_nonneg (1-x*y), norm_nonneg (conj x-y)]

private theorem disk_den {x t : ℂ} (hx : ‖x‖<1) (ht : ‖t‖<1) :
    ‖t+conj x‖ < ‖1+x*t‖ := by
  simpa [add_comm] using disk_lt hx (by simpa using ht : ‖-t‖<1)

private theorem den_ne {x t : ℂ} (hx : ‖x‖<1) (ht : ‖t‖<1) : 1+x*t ≠ 0 :=
  norm_pos_iff.mp ((norm_nonneg _).trans_lt (disk_den hx ht))

private def ratio (x u t : ℂ) := (1+u*t)/(1+x*t)

private theorem image_in_disk {x t : ℂ} (hx : ‖x‖<1) (ht : ‖t‖<1) (u : ℂ) :
    ‖(1-x*conj x)*ratio x u t - (1-u*conj x)‖ ≤ ‖u-x‖ := by
  have he : (1-x*conj x)*ratio x u t - (1-u*conj x) =
      (u-x) * ((t+conj x)/(1+x*t)) := by
    unfold ratio
    field_simp [den_ne hx ht]
    ring
  have ha : ‖(t+conj x)/(1+x*t)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (den_ne hx ht))]
    exact disk_den hx ht
  rw [he, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ha.le

/-- The actual ferromagnetic exchange matrix has nonvanishing symbol
on the full four-variable open unit polydisk. -/
theorem exchange_disk_nonzero {c : ℝ} (hc : 0 ≤ c) {x u w v : ℂ}
    (hx : ‖x‖<1) (hu : ‖u‖<1) (hw : ‖w‖<1) (hv : ‖v‖<1) :
    twoLegSymbol (exchangeEntry c) x u w v ≠ 0 := by
  let b : ℂ := 1-u*conj x
  let k : ℂ := 1-x*conj x
  have hsep : ‖u-x‖ < ‖b‖ := by
    simpa [b, norm_sub_rev u x, mul_comm] using
      (disk_lt (x := conj x) (by simpa using hx) hu)
  have fac : twoLegSymbol (exchangeEntry c) x u w v =
      ((1+x*w)*(1+x*v))*(ratio x u v+(c:ℂ)*ratio x u w) := by
    rw [exchange_symbol]
    unfold ratio
    field_simp [den_ne hx hw, den_ne hx hv]
  rw [fac]
  apply mul_ne_zero (mul_ne_zero (den_ne hx hw) (den_ne hx hv))
  intro he
  have eq : (k*ratio x u v-b)+(c:ℂ)*(k*ratio x u w-b) = -(((1+c:ℝ):ℂ)*b) := by
    push_cast
    linear_combination k*he
  have H := norm_add_le (k*ratio x u v-b) ((c:ℂ)*(k*ratio x u w-b))
  rw [eq, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_pos (by linarith : 0 < 1+c)] at H
  have H' := H.trans (add_le_add (image_in_disk hx hv u)
    (mul_le_mul_of_nonneg_left (image_in_disk hx hw u) hc))
  nlinarith [mul_pos (by linarith : 0<1+c) (sub_pos.mpr hsep)]

/-- Entries of the Euler field matrix I+t*(H₀ σz+H₁ σx+H₂ σy). -/
def fieldEntry (t : ℝ) (H : Fin 3 → ℂ) : Bool → Bool → ℂ
  | false, false => 1+(t:ℂ)*H 0
  | false, true => (t:ℂ)*(H 1-Complex.I*H 2)
  | true, false => (t:ℂ)*(H 1+Complex.I*H 2)
  | true, true => 1-(t:ℂ)*H 0

/-- Symbol of a one-in, one-out matrix on the same binary spinors. -/
def oneLegSymbol (M : Bool → Bool → ℂ) (x y : ℂ) : ℂ :=
  ∑ i : Bool, ∑ j : Bool, M i j * leg x i * leg y j

theorem field_symbol (t : ℝ) (H : Fin 3 → ℂ) (x y : ℂ) :
    oneLegSymbol (fieldEntry t H) x y =
      ((1+(t:ℂ)*H 0) + ((t:ℂ)*(H 1-Complex.I*H 2))*y) +
      x*(((t:ℂ)*(H 1+Complex.I*H 2)) + (1-(t:ℂ)*H 0)*y) := by
  simp [oneLegSymbol, fieldEntry, leg]
  ring

/-- A directly checkable strict cone for the actual Euler field gate.
For t tending to zero this eventually holds uniformly on each compact
set with a strictly positive original Lee–Yang margin. -/
theorem field_disk_nonzero {t : ℝ} (ht : 0<t) {H : Fin 3 → ℂ}
    (hcone : (1+t*‖H 0‖)*(‖H 1‖+‖H 2‖) < (H 0).re) {x y : ℂ}
    (hx : ‖x‖<1) (hy : ‖y‖<1) : oneLegSymbol (fieldEntry t H) x y ≠ 0 := by
  let s := ‖H 1‖+‖H 2‖
  let p := 1+(t:ℂ)*H 0
  let m := 1-(t:ℂ)*H 0
  let a := (t:ℂ)*(H 1-Complex.I*H 2)
  let b := (t:ℂ)*(H 1+Complex.I*H 2)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have ht0 : ‖(t:ℂ)‖ = t := by simp [abs_of_pos ht]
  have sqDiff : ‖p‖^2-‖m‖^2=4*t*(H 0).re := by
    simp only [p,m,Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  have sumBound : ‖p‖+‖m‖ ≤ 2*(1+t*‖H 0‖) := by
    have l := norm_add_le (1 : ℂ) ((t:ℂ)*H 0)
    have r := norm_sub_le (1 : ℂ) ((t:ℂ)*H 0)
    simp only [norm_one,norm_mul,ht0] at l r
    dsimp only [p,m]
    linarith
  have gap : 2*t*s < ‖p‖-‖m‖ := by
    by_contra! hn
    have hb := mul_le_mul hn sumBound (by positivity : 0≤‖p‖+‖m‖) (by positivity : 0≤2*t*s)
    have hc := mul_lt_mul_of_pos_left hcone (by positivity : 0<4*t)
    change 4*t*((1+t*‖H 0‖)*s) < _ at hc
    nlinarith [hb, hc, sqDiff]
  have ha : ‖a‖ ≤ t*s := by
    have h := norm_sub_le (H 1) (Complex.I*H 2)
    simp only [norm_mul,Complex.norm_I,one_mul] at h
    simpa only [a,s,norm_mul,ht0] using mul_le_mul_of_nonneg_left h ht.le
  have hb : ‖b‖ ≤ t*s := by
    have h := norm_add_le (H 1) (Complex.I*H 2)
    simp only [norm_mul,Complex.norm_I,one_mul] at h
    simpa only [b,s,norm_mul,ht0] using mul_le_mul_of_nonneg_left h ht.le
  have mul_y (z : ℂ) : ‖z*y‖ ≤ ‖z‖ :=
    (norm_mul z y).le.trans (mul_le_of_le_one_right (norm_nonneg _) hy.le)
  have positive : ‖b+m*y‖ < ‖p+a*y‖ := by
    have h1 := (norm_add_le b (m*y)).trans (add_le_add hb (mul_y m))
    have h2 := norm_sub_le (p+a*y) (a*y)
    rw [add_sub_cancel_right] at h2
    linarith [(mul_y a).trans ha]
  rw [field_symbol]
  change p+a*y+x*(b+m*y) ≠ 0
  intro he
  have e := congrArg norm (eq_neg_of_add_eq_zero_left he)
  rw [norm_neg,norm_mul] at e
  linarith [mul_le_of_le_one_left (norm_nonneg (b+m*y)) hx.le]

/-- The physical contraction traces the gate with the spin projection, so
the row and column of the projection are reversed. -/
def oneLegTrace (P M : Bool → Bool → ℂ) : ℂ :=
  ∑ i : Bool, ∑ j : Bool, M i j * P j i

/-- Both endpoints of a bond use a separate copy of their spin projection. -/
def twoLegTrace (P Q : Bool → Bool → ℂ) (M : (Bool × Bool) → (Bool × Bool) → ℂ) : ℂ :=
  ∑ a : Bool, ∑ b : Bool, ∑ k : Bool, ∑ l : Bool, M (a,b) (k,l) * P k a * Q l b

theorem exchange_trace (c : ℝ) (P Q : Bool → Bool → ℂ) :
    twoLegTrace P Q (exchangeEntry c) =
      (P false false+P true true)*(Q false false+Q true true) + (c:ℂ)*oneLegTrace P Q := by
  simp [twoLegTrace,oneLegTrace,exchangeEntry]
  ring

theorem field_trace (t : ℝ) (H : Fin 3 → ℂ) (P : Bool → Bool → ℂ) :
    oneLegTrace P (fieldEntry t H) = P false false+P true true+(t:ℂ)*
      (H 0*(P false false-P true true) + H 1*(P true false+P false true) +
        H 2*Complex.I*(P false true-P true false)) := by
  simp [oneLegTrace,fieldEntry]
  ring

#print axioms exchange_symbol
#print axioms exchange_disk_nonzero
#print axioms field_symbol
#print axioms field_disk_nonzero
#print axioms exchange_trace
#print axioms field_trace

end IsingScaling.Rotor.HeisenbergField.SpinorGates
