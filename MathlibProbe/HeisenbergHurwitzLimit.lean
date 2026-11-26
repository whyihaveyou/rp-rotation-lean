import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.UniformConvergence
import MathlibProbe.HeisenbergClassicalEulerLimit

/-!
# Passage to an undamped network and then to the physical spin integral

On a circle around a proposed isolated zero the limiting modulus has a
positive minimum. The maximum principle for the reciprocals of the
approximants passes its lower bound to the centre. This form of the
one-variable Hurwitz theorem permits an eventual zero-free hypothesis and
uses a single nonzero limiting value on the connected open set.
-/

noncomputable section
open Filter Metric Set Complex Topology
namespace IsingScaling.Rotor.HeisenbergField.HurwitzLimit

/-- A locally uniform limit of eventually zero-free holomorphic functions on
a connected open domain is nowhere zero if it is nonzero at one point. -/
theorem anchored_nonzero {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    {a : ℂ} (ha : a ∈ U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hhol : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hnz : ∀ᶠ n in atTop, ∀ z ∈ U, F n z ≠ 0)
    (hanchor : f a ≠ 0) : ∀ z ∈ U, f z ≠ 0 := by
  intro z hz hzero
  have df := hconv.differentiableOn hhol ho
  have af := df.analyticOnNhd ho
  rcases (af z hz).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact hanchor (af.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz he ha)
  have isolated : ∀ᶠ w in 𝓝 z, w ≠ z → f w ≠ 0 := eventually_nhdsWithin_iff.1 he
  have loc : ∀ᶠ w in 𝓝 z, w ∈ U ∧ (w ≠ z → f w ≠ 0) := by
    filter_upwards [ho.mem_nhds hz,isolated] with w hw hi using ⟨hw,hi⟩
  obtain ⟨r,hr,hball⟩ := nhds_basis_closedBall.eventually_iff.1 loc
  have inside : closedBall z r ⊆ U := fun w hw => (hball hw).1
  have cs : sphere z r ⊆ U := sphere_subset_closedBall.trans inside
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    ((df.continuousOn.mono cs).norm)
  let m := ‖f w‖ / 2
  have hm : 0 < m := half_pos (norm_pos_iff.mpr
    ((hball (sphere_subset_closedBall hw)).2 (ne_of_mem_sphere hw hr.ne')))
  have unif := (tendstoLocallyUniformlyOn_iff_forall_isCompact ho).1 hconv
    (sphere z r) cs (isCompact_sphere z r)
  have ev : ∀ᶠ n in atTop, m ≤ ‖F n z‖ := by
    filter_upwards [hhol, hnz, Metric.tendstoUniformlyOn_iff.1 unif m hm] with n hn hf hs
    have bnd (v : ℂ) (hv : v ∈ sphere z r) : m ≤ ‖F n v‖ := by
      have first : ‖f w‖ ≤ ‖f v‖ := hmin hv
      have second := hs v hv
      rw [dist_eq_norm] at second
      have third := norm_le_norm_sub_add (f v) (F n v)
      dsimp [m] at second ⊢
      linarith
    have invd : DifferentiableOn ℂ (fun v => (F n v)⁻¹) U := hn.inv hf
    have top : ‖(F n z)⁻¹‖ ≤ m⁻¹ := Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball (x := z) (r := r)) (invd.diffContOnCl_ball inside) (fun v hv => by
        rw [frontier_ball z hr.ne'] at hv
        rw [norm_inv]
        exact (inv_le_inv₀ (hm.trans_le (bnd v hv)) hm).2 (bnd v hv))
      (subset_closure (mem_ball_self hr))
    rw [norm_inv] at top
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hf z hz)) hm).1 top
  have bound := le_of_tendsto_of_tendsto tendsto_const_nhds (hconv.tendsto_at hz).norm ev
  rw [hzero, norm_zero] at bound
  exact (not_le_of_gt hm) bound

/-- First take damping to one for each fixed sufficiently large volume
approximation index. Then take that approximation index to infinity. -/
theorem two_limits {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    {a : ℂ} (ha : a ∈ U) {damped : ℕ → ℕ → ℂ → ℂ} {euler : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (inner : ∀ᶠ n in atTop,
      TendstoLocallyUniformlyOn (damped n) (euler n) atTop U ∧
      (∀ᶠ k in atTop, DifferentiableOn ℂ (damped n k) U ∧
        ∀ z ∈ U, damped n k z ≠ 0) ∧ euler n a ≠ 0)
    (outer : TendstoLocallyUniformlyOn euler f atTop U) (anchor : f a ≠ 0) :
    ∀ z ∈ U, f z ≠ 0 := by
  have good : ∀ᶠ n in atTop, DifferentiableOn ℂ (euler n) U ∧ ∀ z ∈ U, euler n z ≠ 0 := by
    filter_upwards [inner] with n ⟨conv,flags,at_a⟩
    have dh := flags.mono fun _ h => h.1
    exact ⟨conv.differentiableOn dh ho,
      anchored_nonzero ho hc ha conv dh (flags.mono fun _ h => h.2) at_a⟩
  exact anchored_nonzero ho hc ha outer (good.mono fun _ h => h.1) (good.mono fun _ h => h.2) anchor

open ComplexPartition in
/-- Specialization to the original finite product-sphere partition integral
on an affine path starting at the real longitudinal field. Its outer
nonzero anchor follows from positivity of the real Gibbs integrand. -/
theorem physical_partition_of_two_limits {V : Type*} [Fintype V] (J : V → V → ℝ)
    (h₀ : ℝ) (D : ComplexPartition.Field V) {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    (ha : (0 : ℂ) ∈ U) (one : (1 : ℂ) ∈ U)
    {damped : ℕ → ℕ → ℂ → ℂ} {euler : ℕ → ℂ → ℂ}
    (inner : ∀ᶠ n in atTop,
      TendstoLocallyUniformlyOn (damped n) (euler n) atTop U ∧
      (∀ᶠ k in atTop, DifferentiableOn ℂ (damped n k) U ∧
        ∀ z ∈ U, damped n k z ≠ 0) ∧ euler n 0 ≠ 0)
    {c : ℂ} (nonzero_c : c ≠ 0)
    (outer : TendstoLocallyUniformlyOn euler (fun z => c * partition J (affine (uniform h₀) D z))
      atTop U) : partition J (affine (uniform h₀) D 1) ≠ 0 := by
  have z0 : partition J (uniform (h₀ : ℂ)) ≠ 0 := by
    intro h
    have this := partition_uniform_real_pos J h₀
    simp [h] at this
  have a0 : affine (uniform (V := V) (h₀ : ℂ)) D 0 = uniform (h₀ : ℂ) := by
    funext v i; simp [affine]
  have hA : c * partition J (affine (uniform (h₀ : ℂ)) D 0) ≠ 0 := by
    rw [a0]; exact mul_ne_zero nonzero_c z0
  exact (mul_ne_zero_iff.1 (two_limits ho hc ha inner outer hA 1 one)).2

open ComplexPartition ClassicalEuler in
/-- The remaining inner limit is the actual classical Euler spin integral.
Its compact convergence, its positive real anchor and the final nonzero
Gibbs value at the anchor are supplied by the finite-graph integral. -/
theorem physical_partition_of_damped_euler {V : Type*} [Fintype V] (J : V → V → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) {h₀ : ℝ} (hp : 0 ≤ h₀) (D : ComplexPartition.Field V)
    {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U) (ha : (0 : ℂ) ∈ U)
    (one : (1 : ℂ) ∈ U) {damped : ℕ → ℕ → ℂ → ℂ}
    (inner : ∀ᶠ n in atTop,
      TendstoLocallyUniformlyOn (damped n) (fun z => approximant J (affine (uniform h₀) D z) n) atTop U ∧
      ∀ᶠ k in atTop, DifferentiableOn ℂ (damped n k) U ∧ ∀ z ∈ U, damped n k z ≠ 0) :
    partition J (affine (uniform h₀) D 1) ≠ 0 := by
  have eventually_big : ∀ᶠ n : ℕ in atTop, h₀ < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop h₀)
  apply physical_partition_of_two_limits J h₀ D ho hc ha one (damped := damped)
    (c := (Real.exp (offset J) : ℂ)) (euler := fun n z => approximant J (affine (uniform h₀) D z) n)
  · filter_upwards [inner,eventually_big] with n ⟨hconv,stable⟩ hn
    refine ⟨hconv,stable,?_⟩
    have a0 : affine (uniform (V := V) (h₀ : ℂ)) D 0 = uniform (h₀ : ℂ) := by
      funext v i; simp [affine]
    rw [a0]
    intro hz
    have hh := approximant_uniform_real_pos J hJ h₀ hp n hn
    simp [hz] at hh
  · exact_mod_cast Real.exp_ne_zero (offset J)
  · exact (locallyUniform_approximant_affine J (uniform h₀) D).tendstoLocallyUniformlyOn

#print axioms anchored_nonzero
#print axioms two_limits
#print axioms physical_partition_of_two_limits
#print axioms physical_partition_of_damped_euler

end IsingScaling.Rotor.HeisenbergField.HurwitzLimit
