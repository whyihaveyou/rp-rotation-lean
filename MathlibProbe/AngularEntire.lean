import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-! The angular mode exclusion in §12.3 (AS-6), in complex-exponential coordinates. -/
open Complex Filter Function
open scoped Topology Real

namespace IsingRotation

/-- The exponential growth allowance on the upper half-plane is smaller than the
first frequency of a function of period π/2. Multiplication by the cusp parameter
gives decay at infinity. Holomorphicity upgrades it to decay by a full power of
the parameter, leaving the original function bounded. -/
private theorem angular_upper_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hp : Periodic f ((Real.pi / 2 : ℝ) : ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (2 * |z.im|)) :
    ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ B := by
  let h : ℝ := Real.pi / 2
  have hh : 0 < h := by dsimp [h]; positivity
  let q := Periodic.qParam h
  have hq : Periodic q (h : ℂ) := by
    intro z
    dsimp [q, Periodic.qParam]
    rw [mul_add, add_div, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hh.ne')]
    exact Complex.exp_periodic _
  have hnorm (z : ℂ) : ‖q z‖ = Real.exp (-4 * z.im) := by
    rw [show ‖q z‖ = _ from Periodic.norm_qParam h z]
    congr 1
    dsimp [h]
    field_simp [Real.pi_ne_zero]
    ring
  let L := comap Complex.im atTop
  have him : Tendsto Complex.im L atTop := tendsto_comap
  have hzero : ZeroAtFilter L (q * f) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (.of_forall fun z => norm_nonneg _) (g := fun z : ℂ => C * Real.exp (-2 * z.im))
    · filter_upwards [him.eventually (eventually_ge_atTop 0)] with z hz
      change ‖q z * f z‖ ≤ _
      rw [norm_mul, hnorm]
      calc
        _ ≤ Real.exp (-4 * z.im) * (C * Real.exp (2 * |z.im|)) :=
          mul_le_mul_of_nonneg_left (hg z) (Real.exp_pos _).le
        _ = _ := by rw [abs_of_nonneg hz, mul_left_comm, ← Real.exp_add]; ring_nf
    · have hs := (Real.tendsto_exp_atBot.comp (him.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))).const_mul C
      simpa [Function.comp_def] using hs
  have hdecay := Periodic.exp_decay_of_zero_at_inf hh (hq.mul hp)
      (.of_forall fun z => ((Periodic.differentiable_qParam (h := h)).mul hf) z) hzero
  obtain ⟨b,hb⟩ := hdecay.bound
  obtain ⟨t, ht⟩ := eventually_atTop.mp (eventually_comap.mp hb)
  refine ⟨max b (C * Real.exp (2 * t)), fun z hz => ?_⟩
  by_cases ht' : t ≤ z.im
  · have hz' := ht _ ht' z rfl
    change ‖q z * f z‖ ≤ b * ‖Real.exp (-2 * Real.pi * z.im / h)‖ at hz'
    rw [← Periodic.norm_qParam, Real.norm_of_nonneg (norm_nonneg _)] at hz'
    change ‖q z * f z‖ ≤ b * ‖q z‖ at hz'
    rw [norm_mul, mul_comm b] at hz'
    exact (le_of_mul_le_mul_left hz' (norm_pos_iff.mpr (Periodic.qParam_ne_zero (h := h) z))).trans (le_max_left _ _)
  · refine (hg z).trans ((mul_le_mul_of_nonneg_left ?_ hC).trans (le_max_right _ _))
    rw [abs_of_nonneg hz, Real.exp_le_exp]
    linarith

/-- A quarter-turn-periodic entire angular function growing at most as
`C exp(2 |Im z|)` is constant. Both sides of the real axis are included. -/
theorem angularEntire_constant (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hp : Periodic f ((Real.pi / 2 : ℝ) : ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (2 * |z.im|)) (z w : ℂ) : f z = f w := by
  obtain ⟨b,hb⟩ := angular_upper_bound f hf hp C hC hg
  have hpneg : Periodic (fun x : ℂ => f (-x)) ((Real.pi / 2 : ℝ) : ℂ) := by
    intro x
    simpa [neg_add, sub_eq_add_neg, add_comm] using hp.sub_eq (-x)
  obtain ⟨d,hd⟩ := angular_upper_bound (fun x => f (-x))
    (hf.comp differentiable_id.neg) hpneg C hC (fun x => by simpa using hg (-x))
  apply hf.apply_eq_apply_of_bounded _ z w
  refine isBounded_iff_forall_norm_le.mpr ⟨max b d, ?_⟩
  rintro _ ⟨x,rfl⟩
  rcases le_total 0 x.im with hx | hx
  · exact (hb x hx).trans (le_max_left _ _)
  · have hx' : 0 ≤ (-x).im := by simpa
    simpa using (hd (-x) hx').trans (le_max_right b d)

end IsingRotation
