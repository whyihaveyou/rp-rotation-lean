import MathlibProbe.AngularStrip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-! Uniform angular estimate for the normalized Stieltjes kernel in AS-6. -/

open Complex
open scoped Real

namespace IsingRotation

private lemma polar_lower {v X c : ℝ} (hv : |v| ≤ 1) (hX : |X| ≤ 3/4)
    (hc : 1 ≤ c) : (1/8 : ℝ)^2 ≤ (v*c + X)^2 + (1-X^2)*(1-v^2) := by
  have hv2 : v^2 ≤ 1 := by nlinarith [sq_abs v, mul_self_le_mul_self (abs_nonneg v) hv]
  have hX2 : X^2 ≤ (3/4 : ℝ)^2 := by nlinarith [sq_abs X, mul_self_le_mul_self (abs_nonneg X) hX]
  by_cases small : |v| ≤ 7/8
  · have hs : v^2 ≤ (7/8 : ℝ)^2 := by nlinarith [sq_abs v, mul_self_le_mul_self (abs_nonneg v) small]
    nlinarith [mul_le_mul (show (7:ℝ)/16 ≤ 1-X^2 by linarith) (show (15:ℝ)/64 ≤ 1-v^2 by linarith) (by norm_num) (by linarith : 0 ≤ 1-X^2), sq_nonneg (v*c+X)]
  · have hbig : (1/8 : ℝ) ≤ |v*c + X| := by
      have hc' : |v| ≤ |v*c| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ c)]; nlinarith [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hc)]
      have htri := abs_add_le (v*c+X) (-X)
      rw [add_neg_cancel_right, abs_neg] at htri
      linarith
    nlinarith [sq_abs (v*c+X), mul_self_le_mul_self (by norm_num : 0 ≤ (1:ℝ)/8) hbig,
      mul_nonneg (by linarith : 0 ≤ 1-X^2) (by linarith : 0 ≤ 1-v^2)]

private lemma cos_parts (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re * Real.cosh z.im ∧
    (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, ← Complex.ofReal_sinh]

/-- A good normal controls the denominator of the compactified kernel
even at large imaginary angular times. -/
theorem angularDenominator_lower (z : ℂ) (v : ℝ) (hv : |v| ≤ 1)
    (hx : |Real.cos z.re| ≤ 3/4) : (1/8 : ℝ) ≤ ‖1 + (v:ℂ)*Complex.cos z‖ := by
  let X := Real.cos z.re
  let S := Real.sin z.re
  let c := Real.cosh z.im
  let s := Real.sinh z.im
  have hs : S^2 = 1-X^2 := Real.sin_sq _
  have hc : s^2 = c^2-1 := by linarith [Real.cosh_sq_sub_sinh_sq z.im]
  have hid : ‖1+(v:ℂ)*Complex.cos z‖^2 = (v*c+X)^2+(1-X^2)*(1-v^2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, (cos_parts z).1, (cos_parts z).2]
    change (1+v*(X*c))*(1+v*(X*c))+_ = _
    ring_nf
    dsimp [X,S,c,s] at hs hc ⊢
    rw [hs,hc]
    ring
  have hb := polar_lower hv hx (Real.one_le_cosh z.im)
  nlinarith [norm_nonneg (1+(v:ℂ)*Complex.cos z)]

private theorem cos_norm_upper (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.cos z‖^2 = (Real.cosh z.im)^2 - (Real.sin z.re)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply,(cos_parts z).1,(cos_parts z).2]
    have hs := Real.sin_sq_add_cos_sq z.re
    have hc := Real.cosh_sq_sub_sinh_sq z.im
    linear_combination (Real.cosh z.im)^2*hs - (Real.sin z.re)^2*hc
  have h2 : ‖Complex.cos z‖ ≤ Real.cosh z.im := by nlinarith [Real.cosh_pos z.im, sq_nonneg (Real.sin z.re)]
  refine h2.trans ?_
  rw [Real.cosh_eq]
  linarith [Real.exp_le_exp.mpr (le_abs_self z.im), Real.exp_le_exp.mpr (neg_le_abs z.im)]

/-- Integral kernels at cotangent squared admit this nonsingular chart formula
in any direction with sine nonzero. -/
theorem angularKernel_identity (z : ℂ) (u : ℝ) (hs : Complex.sin z ≠ 0)
    (hd : 1 + (2*(u:ℂ)-1)*Complex.cos (2*z) ≠ 0) :
    (1-(u:ℂ)+(u:ℂ)*(Complex.cos z / Complex.sin z)^2)⁻¹ =
    (1-Complex.cos (2*z))/(1 + (2*(u:ℂ)-1)*Complex.cos (2*z)) := by
  have h1 := Complex.cos_two_mul_eq_one_sub z
  have h2 := Complex.cos_two_mul z
  have hb : 2 * (Complex.sin z)^2 * (1-(u:ℂ)+(u:ℂ)*(Complex.cos z / Complex.sin z)^2) =
      1 + (2*(u:ℂ)-1)*Complex.cos (2*z) := by
    calc
      _ = (1-(u:ℂ))*(2*Complex.sin z^2) + (u:ℂ)*(2*Complex.cos z^2) := by field_simp [hs]
      _ = _ := by linear_combination (1-(u:ℂ))*h1 - (u:ℂ)*h2
  have harg : 1-(u:ℂ)+(u:ℂ)*(Complex.cos z / Complex.sin z)^2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hb
    exact hd hb.symm
  rw [inv_eq_one_div, div_eq_div_iff harg hd, one_mul, ← hb, h1]
  ring

/-- Uniform exponential bound for the normalized Stieltjes
kernel in the nonsingular angular chart. -/
theorem angularKernel_bound (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hx : |Real.cos (2*z.re)| ≤ 3/4) :
    ‖(1-Complex.cos (2*z))/(1 + (2*(u:ℂ)-1)*Complex.cos (2*z))‖ ≤
    16 * Real.exp (2*|z.im|) := by
  have hv : |2*u-1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hd := angularDenominator_lower (2*z) (2*u-1) hv (by simpa using hx)
  push_cast at hd
  rw [norm_div, div_le_iff₀ (by linarith : 0 < ‖1+(2*(u:ℂ)-1)*Complex.cos (2*z)‖)]
  have hh : ‖Complex.cos (2*z)‖ ≤ Real.exp (2*|z.im|) := by simpa [abs_mul] using cos_norm_upper (2*z)
  have hpos := Real.exp_pos (2*|z.im|)
  have hone : 1 ≤ Real.exp (2*|z.im|) := Real.one_le_exp (by positivity)
  have hnum := norm_sub_le (1:ℂ) (Complex.cos (2*z))
  rw [norm_one] at hnum
  nlinarith [mul_le_mul_of_nonneg_left hd hpos.le]

/-- The nearest strip centre supplies a good normal, also when the real
part lies on one of the other strip boundaries. -/
theorem angularStrip_good_normal (z : ℂ) : ∃ i : ℤ, z ∈ angularStrip i ∧
    |Real.cos (2*(z.re - (i:ℝ)*(π/4)))| ≤ 3/4 := by
  let w := Real.pi / 4
  have hw : 0 < w := by dsimp [w]; positivity
  let a := z.re / w
  let n : ℤ := ⌊a + 1/2⌋ - 1
  have lo : (n:ℝ) + 1/2 ≤ a := by
    dsimp [n]; push_cast; linarith [Int.floor_le (a+1/2)]
  have hi : a ≤ (n:ℝ) + 3/2 := by
    dsimp [n]; push_cast; linarith [Int.lt_floor_add_one (a+1/2)]
  have hlo := (le_div_iff₀ hw).mp lo
  have hhi := (div_le_iff₀ hw).mp hi
  refine ⟨n, ?_, ?_⟩
  · change (n:ℝ)*w < z.re ∧ z.re < ((n:ℝ)+2)*w
    constructor <;> linarith
  · let θ := 2*(z.re - (n:ℝ)*w)
    have tl : π/4 ≤ θ := by dsimp [θ]; dsimp [w] at *; linarith
    have tu : θ ≤ π - π/4 := by dsimp [θ]; dsimp [w] at *; linarith
    have cp : Real.cos (π/4) ≤ 3/4 := by
      rw [Real.cos_pi_div_four]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    have c1 := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos] : 0 ≤ π/4)
        (by linarith [Real.pi_pos] : θ ≤ π) tl
    have c2 := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos] : 0 ≤ θ)
        (by linarith [Real.pi_pos] : π-π/4 ≤ π) tu
    rw [Real.cos_pi_sub] at c2
    change |Real.cos θ| ≤ 3/4
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end IsingRotation
