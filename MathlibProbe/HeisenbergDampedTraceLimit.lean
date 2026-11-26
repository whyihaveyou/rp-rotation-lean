import MathlibProbe.HeisenbergAsanoWire
import MathlibProbe.HeisenbergHurwitzLimit

/-! # Strictly damped wire traces and the actual classical partition function

A fixed finite closed-wire trace is jointly continuous in the damping and
the affine field parameter. The wire count and matrix vary with the outer
Euler index. No bound uniform in this count is needed for the inner limit.
-/

noncomputable section
open Filter Set Topology
open MathlibProbe.HeisenbergAsanoWire
namespace IsingScaling.Rotor.HeisenbergField.DampedTraceLimit

def damping (k : ℕ) : ℂ := Complex.ofReal (1 - 1 / ((k : ℝ) + 1))

theorem norm_damping_lt (k : ℕ) : ‖damping k‖ < 1 := by
  have hi : 0 < 1 / ((k : ℝ)+1) := by positivity
  have le : 1 / ((k : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
  rw [damping,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le)]
  exact sub_lt_self _ hi

theorem tendsto_damping : Tendsto damping atTop (𝓝 1) := by
  have ht : Tendsto (fun k : ℕ => (1:ℝ) - 1 / ((k : ℝ)+1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun k : ℕ => Complex.ofReal (1 - 1 / ((k : ℝ) + 1))) atTop (𝓝 1)
  simpa only [Function.comp_def,Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp ht

/-- The coefficient indexing is row and column at each physical wire. -/
def trace (q : ℕ) (M : (Fin q → Bool × Bool) → ℂ → ℂ) (c t z : ℂ) : ℂ :=
  c * denseTrace q (fun u => M u z) (fun _ => t)

theorem differentiableOn_trace (q : ℕ) (M : (Fin q → Bool × Bool) → ℂ → ℂ) (c t : ℂ)
    {U : Set ℂ} (hM : ∀ u, DifferentiableOn ℂ (M u) U) :
    DifferentiableOn ℂ (trace q M c t) U := by
  apply (differentiableOn_const c).mul
  unfold denseTrace denseSum
  apply DifferentiableOn.fun_sum
  intro b _
  exact (hM (fun j => (b j,b j))).mul (differentiableOn_const _)

private theorem tendsto_trace {A : Type*} {p : Filter A} {U : Set ℂ} {x : ℂ} (hx : x ∈ U)
    (q : ℕ) (M : (Fin q → Bool × Bool) → ℂ → ℂ) (c : ℂ) (hM : ∀ u, ContinuousOn (M u) U)
    {T Z : A → ℂ} {t : ℂ} (hc : Tendsto T p (𝓝 t)) (hz : Tendsto Z p (𝓝[U] x)) :
    Tendsto (fun a => trace q M c (T a) (Z a)) p (𝓝 (trace q M c t x)) := by
  apply tendsto_const_nhds.mul
  unfold denseTrace denseSum
  apply tendsto_finsetSum
  intro b _
  apply ((hM _ x hx).tendsto.comp hz).mul
  apply tendsto_finsetProd
  intro j _
  cases b j <;> simp only [bitFactor,Bool.false_eq_true,ite_false,ite_true]
  · exact tendsto_const_nhds
  · exact hc

theorem locallyUniform_damped_trace (q : ℕ) (M : (Fin q → Bool × Bool) → ℂ → ℂ) (c : ℂ)
    {U : Set ℂ} (hM : ∀ u, ContinuousOn (M u) U) :
    TendstoLocallyUniformlyOn (fun k z => trace q M c (damping k) z) (trace q M c 1) atTop U := by
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro x hx
  let p := (atTop : Filter ℕ) ×ˢ (𝓝[U] x)
  have zlim : Tendsto (fun v : ℕ × ℂ => v.2) p (𝓝[U] x) := tendsto_snd
  have tlim : Tendsto (fun v : ℕ × ℂ => damping v.1) p (𝓝 1) := tendsto_damping.comp tendsto_fst
  have fixed := tendsto_trace hx q M c hM (T := fun _ : ℕ × ℂ => (1:ℂ)) tendsto_const_nhds zlim
  have moving := tendsto_trace hx q M c hM tlim zlim
  exact (fixed.prodMk_nhds moving).mono_right (nhds_le_uniformity _)

open ComplexPartition ClassicalEuler in
/-- All analytic limits and real positive anchors are proved here. The
inputs left to a particular physical network are its finite holomorphic
entries, open-symbol stability, and its exact undamped Euler integral. -/
theorem physical_partition_of_dense_network {V : Type*} [Fintype V] (J : V → V → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) {h₀ : ℝ} (hp : 0 ≤ h₀) (D : ComplexPartition.Field V)
    {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U) (ha : (0:ℂ) ∈ U)
    (one : (1:ℂ) ∈ U) (q : ℕ → ℕ) (M : (n:ℕ) → (Fin (q n) → Bool × Bool) → ℂ → ℂ)
    (c : ℕ → ℂ)
    (finite : ∀ᶠ n in atTop, c n ≠ 0 ∧
      (∀ u, DifferentiableOn ℂ (M n u) U) ∧
      (∀ z ∈ U, ∀ v : Fin (q n) → ℂ × ℂ,
        (∀ i, ‖(v i).1‖ < 1 ∧ ‖(v i).2‖ < 1) →
          denseSymbol (q n) (fun u => M n u z) v ≠ 0) ∧
      ∀ z ∈ U, trace (q n) (M n) (c n) 1 z = approximant J (affine (uniform h₀) D z) n) :
    partition J (affine (uniform h₀) D 1) ≠ 0 := by
  apply HurwitzLimit.physical_partition_of_damped_euler J hJ hp D ho hc ha one
    (damped := fun n k z => trace (q n) (M n) (c n) (damping k) z)
  filter_upwards [finite] with n ⟨hn,hM,stable,physical⟩
  refine ⟨(locallyUniform_damped_trace (q n) (M n) (c n) (fun u => (hM u).continuousOn)).congr_right physical,?_⟩
  apply Eventually.of_forall
  intro k
  exact ⟨differentiableOn_trace _ _ _ _ hM,fun z hz => mul_ne_zero hn
    (denseTrace_nonzero (q n) _ _ (stable z hz) (fun _ => norm_damping_lt k))⟩

#print axioms locallyUniform_damped_trace
#print axioms physical_partition_of_dense_network

end IsingScaling.Rotor.HeisenbergField.DampedTraceLimit
