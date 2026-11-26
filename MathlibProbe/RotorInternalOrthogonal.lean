import MathlibProbe.RotorSphereSign
import MathlibProbe.RotorPeriodicSpinState

/-! # Internal orthogonal symmetry of the sphere-spin field

Apply the same orthogonal linear isometry to the spin at each site. It preserves
normalized surface measure at each site and hence the finite product prior. It
also preserves each inner product in the energy, so the Gibbs density has the
same value at a configuration and at its image. The resulting identity of
probability measures holds for any finite real coupling matrix.

Lifting a configuration at a specified root commutes with the spin action.
Averaging over roots therefore gives the identity on the whole lattice field.
Testing the equality against continuous functions passes it to every weak limit
of these laws, simultaneously for all internal orthogonal transformations.
-/

noncomputable section

open MeasureTheory Filter Finset
open scoped InnerProductSpace Topology

namespace IsingScaling.Rotor.PressureSelection.InternalOrthogonal

abbrev Ambient (N : ℕ) := SiteReflection.SphereSign.Ambient N

/-- Apply one orthogonal transformation to the spin at every site. -/
def rotate {N : ℕ} {V : Type*} (U : Ambient N ≃ₗᵢ[ℝ] Ambient N) :
    C(V → Spin N, V → Spin N) where
  toFun σ v := SiteReflection.SphereSign.sphereMap U (σ v)
  continuous_toFun := by
    have h : Continuous (SiteReflection.SphereSign.sphereMap U) :=
      continuous_induced_rng.2 (U.continuous.comp continuous_subtype_val)
    exact continuous_pi fun v => h.comp (continuous_apply v)

@[simp] theorem rotate_val {N : ℕ} {V : Type*} (U : Ambient N ≃ₗᵢ[ℝ] Ambient N)
    (σ : V → Spin N) (v : V) : ((rotate U σ) v).val = U (σ v).val := rfl

theorem energy_rotate {N : ℕ} {V : Type*} [Fintype V] (A : V → V → ℝ)
    (U : Ambient N ≃ₗᵢ[ℝ] Ambient N) (σ : V → Spin N) :
    energy A (rotate U σ) = energy A σ := by
  simp only [energy, rotate_val, U.inner_map_map]

/-- The pushforward of the complete finite Gibbs law under any internal orthogonal map. -/
theorem sphereGibbs_invariant (N : ℕ) [NeZero N] {V : Type*} [Fintype V] (A : V → V → ℝ)
    (U : Ambient N ≃ₗᵢ[ℝ] Ambient N) :
    MeasurePreserving (rotate (V := V) U) (sphereGibbs N A : Measure _)
      (sphereGibbs N A : Measure _) := by
  let θ := Measure.pi (fun _ : V => SiteReflection.surfacePrior N)
  have hp : MeasurePreserving (rotate (V := V) U) θ θ :=
    measurePreserving_pi (fun _ : V => SiteReflection.surfacePrior N)
      (fun _ : V => SiteReflection.surfacePrior N)
      (f := fun _ s => SiteReflection.SphereSign.sphereMap U s)
      (fun _ => SiteReflection.SphereSign.sphereMap_preserving U)
  have hc : Continuous (energy (N := N) A) := by unfold energy; fun_prop
  let move := rotate (V := V) U
  refine ⟨move.continuous.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ x, F x ∂Measure.map move (sphereGibbs N A : Measure _)) = _
  rw [integral_map move.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  change (∫ σ, F (move σ) ∂(θ.tilted (energy A))) = ∫ σ, F σ ∂(θ.tilted (energy A))
  simp only [integral_tilted, smul_eq_mul, div_mul_eq_mul_div, integral_div]
  congr 1
  have h : (∫ σ, Real.exp (energy A (rotate U σ)) * F (rotate U σ) ∂θ) =
      ∫ σ, Real.exp (energy A σ) * F σ ∂θ :=
    hp.hasLaw.integral_comp (hc.rexp.mul F.continuous).aestronglyMeasurable
  simpa only [energy_rotate] using h

/-- Every internal orthogonal transformation preserves this same whole-field law. -/
def AllInternalInvariant {N : ℕ} (P : ProbabilityMeasure (SpinField N)) : Prop :=
  ∀ U : Ambient N ≃ₗᵢ[ℝ] Ambient N,
    MeasurePreserving (rotate (V := Site) U) (P : Measure _) (P : Measure _)

private theorem invariant_of_integrals {N : ℕ} (P : ProbabilityMeasure (SpinField N))
    (U : Ambient N ≃ₗᵢ[ℝ] Ambient N)
    (h : ∀ F : C(SpinField N, ℝ),
      (∫ σ, (F.comp (rotate U)) σ ∂(P : Measure _)) = ∫ σ, F σ ∂(P : Measure _)) :
    MeasurePreserving (rotate (V := Site) U) (P : Measure _) (P : Measure _) := by
  refine ⟨(rotate U).continuous.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (rotate U).continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact h F.toContinuousMap

/-- The physically rooted field obtained from any finite system has internal symmetry. -/
theorem rooted_invariant (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (A : V → V → ℝ) : AllInternalInvariant (rootedLaw N D A) := by
  intro U
  apply invariant_of_integrals
  intro F
  rw [rootedLaw_integral, rootedLaw_integral]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  let test (σ : V → Spin N) := F (liftAt D v σ)
  have ht : Continuous test := F.continuous.comp (continuous_pi fun x => continuous_apply (D x v))
  change (∫ σ, test (rotate U σ) ∂(sphereGibbs N A : Measure _)) =
    ∫ σ, test σ ∂(sphereGibbs N A : Measure _)
  exact (sphereGibbs_invariant N A U).hasLaw.integral_comp ht.aestronglyMeasurable

/-- Internal symmetry persists on the given field law under weak convergence. -/
theorem invariant_of_tendsto {N : ℕ} {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (hP : Tendsto P atTop (𝓝 Q))
    (hs : ∀ n, AllInternalInvariant (P n)) : AllInternalInvariant Q := by
  intro U
  apply invariant_of_integrals
  intro F
  have h₁ := (ProbabilityMeasure.continuous_integral_continuousMap
    (F.comp (rotate U))).continuousAt.tendsto.comp hP
  have h₂ := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP
  apply tendsto_nhds_unique (h₁.congr' _) h₂
  exact Filter.Eventually.of_forall fun n =>
    (hs n U).hasLaw.integral_comp F.continuous.aestronglyMeasurable

/-- Every weak limit along any sequence of finite ordinary periodic Gibbs laws,
including the baseline subsequences in the state selection, has internal symmetry. -/
theorem cubic_limit_invariant (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides n) (K n)))
      atTop (𝓝 P)) : AllInternalInvariant P :=
  invariant_of_tendsto hP (fun _ => rooted_invariant N _ _)

end IsingScaling.Rotor.PressureSelection.InternalOrthogonal
