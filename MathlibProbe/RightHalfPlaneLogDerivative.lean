import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The logarithmic derivative at a zero-free half-plane boundary

Let an entire function f satisfy |f(z)| ≤ C exp(T |z|) and have
no zero in the closed right half-plane. On the disk of radius R > 0,
factor its finitely many zeros a with multiplicities. In the
factorization replace each z−a by (R²−conj(a)z)/R. The resulting
function has no zero in the open disk, has the original boundary modulus,
and has a modulus at zero at least as large as that of the original
function. The replacement decreases the real logarithmic derivative at
zero because the difference of the old and new contributions is
−Re(a)(|a|⁻²−R⁻²) ≥ 0. Zeros on the circle give equality.

For a nonvanishing function F on the disk take the primitive L of
F'/F vanishing at the origin, using
`DifferentiableOn.isExactOn_ball`. Then F = F(0) exp L on the disk.
If Re L ≤ M and M > 0, its Schwarz transform L/(2M−L) maps the
disk into the unit disk. The derivative form of Schwarz's lemma gives
|L'(0)| ≤ 2M/R. The maximum-modulus principle supplies
M = 1 + log C + TR − log |f(0)|, and arbitrary R then gives
Re(f'(0)/f(0)) ≥ −2T.
-/

noncomputable section
open Complex Filter Function Metric Set
open scoped Topology ComplexConjugate

namespace MathlibProbe.RightHalfPlaneLogDerivative

/-- Sharp derivative estimate at the centre for a holomorphic half-plane map. -/
theorem norm_deriv_le_of_re_le {L : ℂ → ℂ} {M R : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hzero : L 0 = 0) (hre : ∀ z ∈ ball (0 : ℂ) R, (L z).re ≤ M) :
    ‖deriv L 0‖ ≤ 2 * M / R := by
  let W : ℂ → ℂ := fun z ↦ L z / (2 * (M : ℂ) - L z)
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hden (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : 2 * (M : ℂ) - L z ≠ 0 := by
    intro e
    have e' := congrArg Complex.re (sub_eq_zero.mp e)
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, zero_mul, sub_zero] at e'
    linarith [hre z hz]
  have dW : DifferentiableOn ℂ W (ball 0 R) :=
    hL.div (hL.const_sub _) hden
  have w0 : W 0 = 0 := by simp [W, hzero]
  have hmap : MapsTo W (ball 0 R) (closedBall (W 0) 1) := by
    rw [w0]
    intro z hz
    rw [mem_closedBall_zero_iff]
    change ‖L z / (2 * (M : ℂ) - L z)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden z hz))]
    rw [← sq_le_sq₀ (by positivity) (by positivity)]
    suffices (L z).re * (L z).re ≤ (2 * M - (L z).re) * (2 * M - (L z).re) by
      simpa [Complex.sq_norm, Complex.normSq_apply] using this
    nlinarith [hre z hz]
  have bound := Complex.norm_deriv_le_div_of_mapsTo_ball dW hmap hR
  have dL := (hL.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
  have hd : deriv W 0 = deriv L 0 / (2 * (M : ℂ)) := by
    rw [show deriv W 0 = _ from (dL.div (dL.const_sub _) (hden _ h0)).deriv]
    simp [hzero, field]
  rw [hd, norm_div, norm_mul, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hM] at bound
  have h := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp bound
  linarith [show 1 / R * (2 * M) = 2 * M / R by ring]

/-- Zero-free disk estimate. The logarithm branch is built by an analytic
primitive, so no branch-cut hypothesis is imposed on the range. -/
theorem zeroFree_disk {F : ℂ → ℂ} {B R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F (ball 0 R))
    (hn : ∀ z ∈ ball (0 : ℂ) R, F z ≠ 0)
    (hB : ∀ z ∈ ball (0 : ℂ) R, ‖F z‖ ≤ B) :
    ‖deriv F 0 / F 0‖ ≤ 2 * (1 + Real.log B - Real.log ‖F 0‖) / R := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hn0 := norm_pos_iff.mpr (hn _ h0)
  have bpos := lt_of_lt_of_le hn0 (hB _ h0)
  have hld : DifferentiableOn ℂ (logDeriv F) (ball 0 R) :=
    (hF.deriv isOpen_ball).div hF hn
  obtain ⟨L, hL0, dL⟩ := hld.isExactOn_ball.with_val_at 0 0
  have hdL : DifferentiableOn ℂ L (ball 0 R) := fun z hz ↦ (dL z hz).differentiableAt.differentiableWithinAt
  have dE : DifferentiableOn ℂ (Complex.exp ∘ L) (ball 0 R) :=
    Complex.differentiable_exp.comp_differentiableOn hdL
  have logEq : EqOn (logDeriv F) (logDeriv (Complex.exp ∘ L)) (ball 0 R) := by
    intro z hz
    rw [logDeriv_comp Complex.differentiableAt_exp (dL z hz).differentiableAt,
      show logDeriv Complex.exp (L z) = 1 by
        rw [logDeriv_apply, Complex.deriv_exp, div_self (Complex.exp_ne_zero _)],
      one_mul, (dL z hz).deriv]
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hF dE isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (fun _ _ ↦ Complex.exp_ne_zero _) hn).mp logEq
  have hc0 : F 0 = c := by simpa [Pi.smul_apply, hL0] using hc h0
  have hre (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : (L z).re ≤ 1 + Real.log B - Real.log ‖F 0‖ := by
    have eq : ‖F z‖ = ‖F 0‖ * Real.exp (L z).re := by
      simpa [Pi.smul_apply, smul_eq_mul, Complex.norm_exp, ← hc0] using congrArg norm (hc hz)
    have hle := Real.log_le_log (norm_pos_iff.mpr (hn _ hz)) (hB _ hz)
    rw [eq, Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at hle
    linarith
  have hm := Real.log_le_log hn0 (hB _ h0)
  have d := norm_deriv_le_of_re_le hR (by linarith : 0 < 1 + Real.log B - Real.log ‖F 0‖)
    hdL hL0 hre
  simpa only [(dL 0 h0).deriv, logDeriv_apply] using d

private def reflected (R : ℝ) (a z : ℂ) : ℂ :=
  ((R : ℂ) ^ 2 - conj a * z) / R

private theorem reflected_at_zero {R : ℝ} (hR : 0 < R) (a : ℂ) :
    reflected R a 0 = (R : ℂ) := by
  simp [reflected, sq, hR.ne']

private theorem reflected_ne {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ ≤ R) (hz : z ∈ ball (0 : ℂ) R) : reflected R a z ≠ 0 := by
  have hr : ‖conj a * z‖ < ‖(R : ℂ) ^ 2‖ := by
    rw [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR, sq]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) hR)
  exact div_ne_zero (sub_ne_zero.mpr (fun e ↦ hr.ne (congrArg norm e.symm)))
    (Complex.ofReal_ne_zero.mpr hR.ne')

private theorem norm_reflected_on_sphere {R : ℝ} (hR : 0 < R) (a : ℂ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) R) : ‖reflected R a z‖ = ‖z - a‖ := by
  have hzr := mem_sphere_zero_iff_norm.mp hz
  have hzz : (R : ℂ) ^ 2 = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hzr, Complex.ofReal_pow]
  have e : (R : ℂ)^2 - conj a * z = z * conj (z-a) := by rw [hzz, map_sub]; ring
  rw [reflected, e, norm_div, norm_mul, Complex.norm_conj, hzr, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  field_simp

private theorem contribution {R : ℝ} (hR : 0 < R) {a : ℂ}
    (ha : a.re < 0) (hr : ‖a‖ ≤ R) :
    (logDeriv (reflected R a) 0).re ≤
      (logDeriv (fun z : ℂ ↦ z - a) 0).re := by
  have da : a ≠ 0 := fun e ↦ by simp [e] at ha
  have rne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have dl : logDeriv (reflected R a) 0 = -conj a / (R : ℂ)^2 := by
    rw [logDeriv_apply, reflected_at_zero hR]
    have hh : HasDerivAt (reflected R a) (-conj a / R) 0 := by
      unfold reflected
      convert! (((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_sub
        ((R:ℂ)^2)).div_const (R:ℂ) using 1
      simp
    rw [hh.deriv]
    field_simp
  have dr : logDeriv (fun z : ℂ ↦ z - a) 0 = -a⁻¹ := by
    have hh : HasDerivAt (fun z : ℂ ↦ z-a) 1 0 := (hasDerivAt_id (0 : ℂ)).sub_const a
    rw [logDeriv_apply, hh.deriv]
    simp
  rw [dl, dr, ← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.neg_re, Complex.conj_re,
    Complex.neg_re, Complex.inv_re, Complex.normSq_eq_norm_sq, ← neg_div]
  exact div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr da))
    (by nlinarith [norm_nonneg a])

private theorem disk_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hzf : ∀ z : ℂ, 0 ≤ z.re → f z ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ (s : Finset ℂ) (d : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ a ∈ s, a.re < 0 ∧ ‖a‖ ≤ R) ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      EqOn f (fun z ↦ (∏ a ∈ s, (z-a)^d a) * g z) (closedBall 0 R) := by
  classical
  let CB := closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f CB
  have han : AnalyticOnNhd ℂ f CB := fun z _ ↦ hf.analyticAt z
  have hmer : Meromorphic f := fun z ↦ (hf.analyticAt z).meromorphicAt
  have h0 : meromorphicOrderAt f 0 = 0 :=
    (hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hzf 0 (by simp))
  have hall := hmer.exists_meromorphicOrderAt_ne_top_iff_forall.mp
    ⟨0, by rw [h0]; simp⟩
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  let s := hfin.toFinset
  let d : ℂ → ℕ := fun a ↦ (D a).toNat
  have hd (a : ℂ) : (d a : ℤ) = D a :=
    Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han a)
  obtain ⟨g, hg, hgn, hfg⟩ :=
    han.meromorphicOn.extract_zeros_poles (fun z ↦ hall z.val) hfin
  have hpoly : (∏ᶠ a : ℂ, (fun z : ℂ ↦ z-a) ^ D a) =
      (fun z : ℂ ↦ ∏ a ∈ s, (z-a)^(d a)) := by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ ?_ hfin]
    · ext z
      simp only [Finset.prod_apply, Pi.pow_apply]
      apply Finset.prod_congr rfl
      intro a _
      rw [← hd a]
      simp
    · intro a ha
      by_contra ha'
      have : D a = 0 := by simpa [Function.mem_support] using ha'
      exact ha (by change (fun z : ℂ ↦ z-a) ^ D a = 1; rw [this, zpow_zero])
  change f =ᶠ[codiscreteWithin CB] (∏ᶠ a : ℂ, (fun z : ℂ ↦ z-a)^D a) • g at hfg
  rw [hpoly] at hfg
  let P : ℂ → ℂ := fun z ↦ ∏ a ∈ s, (z-a)^d a
  have hP : Differentiable ℂ P := by dsimp [P]; fun_prop
  have hg' : ContinuousOn (fun z ↦ P z * g z) CB :=
    hP.continuous.continuousOn.mul hg.continuousOn
  have hh : EqOn f (fun z ↦ P z * g z) (ball 0 R) := by
    intro z hz
    have hcb := ball_subset_closedBall hz
    have e := eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hfg z hcb
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
      ((hf z).continuousAt.continuousWithinAt)
      ((hP.continuous.continuousAt.mul (hg z hcb).continuousAt).continuousWithinAt)
    filter_upwards [e, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)] with w he hw
    exact he (ball_subset_closedBall hw)
  refine ⟨s, d, g, ?_, hg, fun z hz ↦ hgn ⟨z,hz⟩,
    hh.of_subset_closure hf.continuous.continuousOn hg' ball_subset_closedBall ?_⟩
  · intro a ha
    have hmem : a ∈ D.support := hfin.mem_toFinset.mp ha
    have hcb : a ∈ CB := D.supportWithinDomain hmem
    refine ⟨?_, mem_closedBall_zero_iff.mp hcb⟩
    by_contra! h
    have hord := (hf.analyticAt a).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hzf a h)
    exact hmem (by simp [D, MeromorphicOn.divisor_apply han.meromorphicOn hcb, hord])
  · rw [closure_ball _ hR.ne']

private theorem finite_disk_estimate {f : ℂ → ℂ} {B R : ℝ}
    (hR : 0 < R) (hf : Differentiable ℂ f)
    (hn : ∀ z : ℂ, 0 ≤ z.re → f z ≠ 0)
    (hB : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ B) :
    -(2 * (1 + Real.log B - Real.log ‖f 0‖)) / R ≤ (logDeriv f 0).re := by
  classical
  obtain ⟨s, d, g, hs, hg, hgn, heq⟩ := disk_factorization hf hn hR
  let P := fun z : ℂ ↦ ∏ a ∈ s, (z-a)^d a
  let Q := fun z : ℂ ↦ ∏ a ∈ s, reflected R a z ^ d a
  let F := fun z : ℂ ↦ Q z * g z
  have pd : Differentiable ℂ P := by dsimp [P]; fun_prop
  have qd : Differentiable ℂ Q := by dsimp [Q, reflected]; fun_prop
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have h0c := ball_subset_closedBall h0
  have hqn (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : Q z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a ha ↦ pow_ne_zero _ (reflected_ne hR (hs a ha).2 hz))
  have hpn0 : P 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply pow_ne_zero
    have h := (hs a ha).1
    intro e
    have : a = 0 := (sub_eq_zero.mp e).symm
    simp [this] at h
  have fda : DifferentiableOn ℂ F (closedBall 0 R) := qd.differentiableOn.mul hg.differentiableOn
  have fn (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : F z ≠ 0 :=
    mul_ne_zero (hqn _ hz) (hgn _ (ball_subset_closedBall hz))
  have fbound (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : ‖F z‖ ≤ B := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) (U := ball 0 R)
    · apply DifferentiableOn.diffContOnCl
      simpa [closure_ball _ hR.ne'] using fda
    · intro y hys
      have hy : y ∈ sphere (0 : ℂ) R := by simpa [frontier_ball _ hR.ne'] using hys
      have nQ : ‖Q y‖ = ‖P y‖ := by
        simp only [Q, P, norm_prod, norm_pow, norm_reflected_on_sphere hR _ hy]
      have ef := heq (sphere_subset_closedBall hy)
      change f y = P y * g y at ef
      simpa [F, norm_mul, nQ, ef] using hB y hy
    · exact subset_closure hz
  have larger : ‖f 0‖ ≤ ‖F 0‖ := by
    have ef := heq h0c
    change f 0 = P 0 * g 0 at ef
    rw [ef, show F 0 = Q 0 * g 0 from rfl, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simp only [Q, P, norm_prod, norm_pow, zero_sub, norm_neg, reflected_at_zero hR,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact Finset.prod_le_prod (fun i _ ↦ by positivity)
      (fun a ha ↦ pow_le_pow_left₀ (norm_nonneg _) (hs a ha).2 _)
  have shift : (logDeriv Q 0).re ≤ (logDeriv P 0).re := by
    have pn (a : ℂ) (ha : a ∈ s) : ((0 : ℂ)-a)^d a ≠ 0 := by
      apply pow_ne_zero
      intro e
      have h := (hs a ha).1
      simp [(sub_eq_zero.mp e).symm] at h
    have qn (a : ℂ) (ha : a ∈ s) : reflected R a 0 ^ d a ≠ 0 :=
      pow_ne_zero _ (reflected_ne hR (hs a ha).2 h0)
    change (logDeriv (fun z : ℂ ↦ ∏ a ∈ s, reflected R a z ^ d a) 0).re ≤
      (logDeriv (fun z : ℂ ↦ ∏ a ∈ s, (z-a)^d a) 0).re
    rw [logDeriv_fun_prod qn (by intros; dsimp [reflected]; fun_prop),
        logDeriv_fun_prod pn (by intros; fun_prop)]
    rw [Complex.re_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [logDeriv_fun_pow (f := reflected R a) (x := (0 : ℂ)) (by unfold reflected; fun_prop) (d a),
      logDeriv_fun_pow (f := fun z : ℂ ↦ z-a) (x := (0 : ℂ)) (by fun_prop) (d a)]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (contribution hR (hs a ha).1 (hs a ha).2) (Nat.cast_nonneg _)
  have compare : (logDeriv F 0).re ≤ (logDeriv f 0).re := by
    have ev : f =ᶠ[𝓝 0] (fun z ↦ P z * g z) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0) (heq.mono ball_subset_closedBall)
    have ed : logDeriv f 0 = logDeriv (fun z ↦ P z * g z) 0 := by
      simp only [logDeriv_apply, ev.deriv_eq, ev.eq_of_nhds]
    rw [ed, show logDeriv F 0 = _ from logDeriv_fun_mul _ (hqn 0 h0) (hgn _ h0c)
      (qd 0) (hg 0 h0c).differentiableAt,
      logDeriv_fun_mul _ hpn0 (hgn _ h0c) (pd 0) (hg 0 h0c).differentiableAt,
      Complex.add_re, Complex.add_re]
    linarith
  have disk := zeroFree_disk hR (fda.mono ball_subset_closedBall) fn fbound
  have lg := Real.log_le_log (norm_pos_iff.mpr (hn 0 (by simp))) larger
  have hlow : -(‖logDeriv F 0‖) ≤ (logDeriv F 0).re :=
    le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
  change ‖logDeriv F 0‖ ≤ _ at disk
  apply le_trans _ compare
  apply le_trans _ hlow
  have z := (le_div_iff₀ hR).mp disk
  rw [div_le_iff₀ hR]
  linarith

/-- An entire function of exponential type with no zeros in the closed right
half-plane has real logarithmic derivative at zero at least minus twice its
growth type. All zeros in the left half-plane and their multiplicities are
allowed. -/
theorem re_logDeriv_zero_ge_neg_two_type {f : ℂ → ℂ} {C T : ℝ}
    (hf : Differentiable ℂ f) (hn : ∀ z : ℂ, 0 ≤ z.re → f z ≠ 0)
    (growth : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (T * ‖z‖)) :
    -2 * T ≤ (deriv f 0 / f 0).re := by
  have hn0 : 0 < ‖f 0‖ := norm_pos_iff.mpr (hn 0 (by simp))
  have hc : 0 < C := lt_of_lt_of_le hn0 (by simpa using growth 0)
  change -2 * T ≤ (logDeriv f 0).re
  by_contra! bad
  let gap := -2 * T - (logDeriv f 0).re
  have gp : 0 < gap := sub_pos.mpr bad
  let B := 2 * (1 + Real.log C - Real.log ‖f 0‖)
  let R := (|B| + 1) / gap
  have hr : 0 < R := div_pos (by positivity) gp
  have edge (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
      ‖f z‖ ≤ C * Real.exp (T * R) := by
    simpa [mem_sphere_zero_iff_norm.mp hz] using growth z
  have bound := finite_disk_estimate hr hf hn edge
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp, div_le_iff₀ hr] at bound
  have contrad : R * gap ≤ B := by dsimp [gap, B]; nlinarith
  have eq : R * gap = |B| + 1 := div_mul_cancel₀ _ gp.ne'
  rw [eq] at contrad
  linarith [le_abs_self B]

end MathlibProbe.RightHalfPlaneLogDerivative
