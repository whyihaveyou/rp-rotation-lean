import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
Reflection through crossing bonds of a classical vector-spin system.
The index is an arbitrary finite family of half configurations, while the
spin at each site ranges over a real inner product space. The sphere
corollary uses the actual unit sphere in Euclidean space.
-/

noncomputable section

open Matrix Finset Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace

namespace IsingScaling.Rotor

variable {ι E V : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem ones_psd :
    Matrix.PosSemidef (Matrix.of (fun _ _ : ι => (1 : ℝ))) := by
  let u : ι → ℝ := fun _ => 1
  simpa [Matrix.vecMulVec, u, Matrix.of] using
    (Matrix.posSemidef_vecMulVec_self_star u)

/-- Powers applied entrywise preserve positivity, including the constant
kernel at degree zero. -/
private theorem schur_power {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (Matrix.of fun i j => A i j ^ k).PosSemidef := by
  induction k with
  | zero => simpa using (ones_psd (ι := ι))
  | succ k hk =>
    have heq : (Matrix.of fun i j => A i j ^ (k + 1)) =
        (Matrix.of fun i j => A i j ^ k).hadamard A := by
      ext i j
      simp only [Matrix.hadamard_apply, Matrix.of_apply, pow_succ]
    rw [heq]
    exact hk.hadamard hA

/-- The exact exponential interaction, evaluated on any finite family of
real vector spins. The exponential is obtained as an entrywise limit of
Schur powers of the sum of the constant kernel and a scaled Gram matrix. -/
theorem exp_inner_posSemidef (v : ι → E) {β : ℝ} (hβ : 0 ≤ β) :
    (Matrix.of fun i j => Real.exp (β * ⟪v i, v j⟫_ℝ)).PosSemidef := by
  let A (n : ℕ) : Matrix ι ι ℝ :=
    Matrix.of (fun _ _ => 1) + (β / (n : ℝ)) • Matrix.gram ℝ v
  have hA (n : ℕ) : (A n).PosSemidef :=
    ones_psd.add ((Matrix.posSemidef_gram ℝ v).smul (div_nonneg hβ (Nat.cast_nonneg n)))
  apply Matrix.posSemidef_is_closed.mem_of_tendsto (b := atTop) (f := fun n : ℕ =>
    Matrix.of fun i j => (A n i j) ^ n) _ (Eventually.of_forall fun n => schur_power (hA n) n)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun n : ℕ =>
      (1 + (β / (n : ℝ)) * ⟪v i, v j⟫_ℝ) ^ n) atTop
    (𝓝 (Real.exp (β * ⟪v i, v j⟫_ℝ)))
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    Real.tendsto_one_add_div_pow_exp (β * ⟪v i, v j⟫_ℝ)

/-- The complete seam can have a separate nonnegative interaction on
every crossing bond, and different indices may even describe identical
configurations. -/
theorem seam_posSemidef (S : Finset V) (β : V → ℝ)
    (hβ : ∀ x ∈ S, 0 ≤ β x) (σ : ι → V → E) :
    (Matrix.of fun i j => ∏ x ∈ S, Real.exp (β x * ⟪σ i x, σ j x⟫_ℝ)).PosSemidef := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (ones_psd (ι := ι))
  | @insert x S hx ih =>
    have h1 := exp_inner_posSemidef (fun i => σ i x) (hβ x (by simp))
    have h2 := ih (fun y hy => hβ y (Finset.mem_insert_of_mem hy))
    rw [show (Matrix.of fun i j => ∏ y ∈ insert x S,
        Real.exp (β y * ⟪σ i y, σ j y⟫_ℝ)) =
        (Matrix.of fun i j => Real.exp (β x * ⟪σ i x, σ j x⟫_ℝ)).hadamard
        (Matrix.of fun i j => ∏ y ∈ S, Real.exp (β y * ⟪σ i y, σ j y⟫_ℝ)) by
      ext i j
      simp only [Matrix.hadamard_apply, Matrix.of_apply, Finset.prod_insert hx]]
    exact h1.hadamard h2

/-- A finite signed test of the genuine nearest-neighbour seam weight of
unit-sphere spins. Its coefficients can include any positive quadrature
weights and any Gibbs factors internal to each half. -/
theorem sphere_seam_signed_test_nonneg (N : ℕ) (S : Finset V) (β : V → ℝ)
    (hβ : ∀ x ∈ S, 0 ≤ β x)
    (σ : ι → V → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) (f : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, f i * f j * ∏ x ∈ S,
      Real.exp (β x * ⟪(σ i x).val, (σ j x).val⟫_ℝ) := by
  classical
  have h := (seam_posSemidef S β hβ (fun i x => (σ i x).val)).dotProduct_mulVec_nonneg f
  simpa only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
    Matrix.of_apply, ← mul_assoc, mul_right_comm] using h

/-- Averaging the finite Gram test on independent spins gives positivity
for the product integral, for an arbitrary probability measure. -/
theorem integral_nonneg_of_sample_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : X × X → ℝ)
    (hi : Integrable A (μ.prod μ)) (hd : Integrable (fun x => A (x,x)) μ)
    (hpos : ∀ (k : ℕ) (x : Fin k → X), 0 ≤ ∑ i, ∑ j, A (x i, x j)) :
    0 ≤ ∫ z, A z ∂(μ.prod μ) := by
  classical
  let off := ∫ z, A z ∂(μ.prod μ)
  let diag := ∫ x, A (x,x) ∂μ
  have bound (n : ℕ) : 0 ≤ diag + n * off := by
    let I := Fin (n+1)
    let ν : Measure (I → X) := Measure.pi (fun _ => μ)
    have hcoord (i : I) : MeasurePreserving (fun x : I → X => x i) ν μ :=
      measurePreserving_eval (fun _ => μ) i
    have hInd : iIndepFun (fun i (x : I → X) => x i) ν :=
      iIndepFun_pi (X := fun _ : I => id) (fun _ => aemeasurable_id)
    have hpair (i j : I) (h : i ≠ j) : MeasurePreserving (fun x : I → X => (x i, x j))
        ν (μ.prod μ) :=
      ⟨by fun_prop, ((hInd.indepFun h).hasLaw_prod (hcoord i).hasLaw (hcoord j).hasLaw).map_eq⟩
    have hInt (i j : I) : Integrable (fun x : I → X => A (x i, x j)) ν := by
      by_cases h : i = j
      · subst j
        exact (hcoord i).integrable_comp_of_integrable hd
      · exact (hpair i j h).integrable_comp_of_integrable hi
    have hread (i j : I) :
        (∫ x : I → X, A (x i, x j) ∂ν) = (if i = j then diag - off else 0) + off := by
      by_cases h : i = j
      · subst j
        simpa using (hcoord i).hasLaw.integral_comp hd.aestronglyMeasurable
      · simpa [h] using (hpair i j h).hasLaw.integral_comp hi.aestronglyMeasurable
    have hzero : 0 ≤ ∫ x : I → X, ∑ i, ∑ j, A (x i, x j) ∂ν :=
      integral_nonneg (fun x => hpos _ x)
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt i j))] at hzero
    simp_rw [integral_finsetSum _ (fun j _ => hInt _ j), hread] at hzero
    simp [Finset.sum_add_distrib, I] at hzero
    have hc : 0 < (n:ℝ)+1 := by positivity
    exact (nonneg_of_mul_nonneg_right (show 0 ≤ ((n : ℝ) + 1) * (diag + n * off) by
      convert hzero using 1
      ring) hc)

  by_contra! hneg
  change off < 0 at hneg
  obtain ⟨n, hn⟩ := exists_nat_gt (diag / -off)
  have hlt := (div_lt_iff₀ (neg_pos.mpr hneg)).mp hn
  linarith [bound n]
abbrev Spin (N : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- Reflection against any probability law on a half-box, in particular
the finite Gibbs law relative to normalized Haar measure. -/
theorem sphere_seam_integral_nonneg {V : Type*} [Fintype V] (N : ℕ)
    (S : Finset V) (β : V → ℝ) (hβ : ∀ x ∈ S, 0 ≤ β x)
    (μ : Measure (V → Spin N)) [IsProbabilityMeasure μ]
    (f : (V → Spin N) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    0 ≤ ∫ z : (V → Spin N) × (V → Spin N),
      f z.1 * f z.2 * ∏ x ∈ S,
        Real.exp (β x * ⟪(z.1 x).val, (z.2 x).val⟫_ℝ) ∂(μ.prod μ) := by
  classical
  let K (z : (V → Spin N) × (V → Spin N)) :=
    ∏ x ∈ S, Real.exp (β x * ⟪(z.1 x).val, (z.2 x).val⟫_ℝ)
  let A (z : (V → Spin N) × (V → Spin N)) := f z.1 * f z.2 * K z
  have hK : Continuous K := by
    dsimp [K]
    fun_prop
  have hA : Measurable A := (hf.comp measurable_fst |>.mul (hf.comp measurable_snd)).mul hK.measurable
  have hBd (z) : ‖A z‖ ≤ M * M * ∏ x ∈ S, Real.exp (β x) := by
    have hprod : K z ≤ ∏ x ∈ S, Real.exp (β x) := by
      apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      intro x hx
      exact Real.exp_le_exp.mpr <| (mul_le_mul_of_nonneg_left
        (real_inner_le_one_of_norm_eq_one (norm_eq_of_mem_sphere (z.1 x))
          (norm_eq_of_mem_sphere (z.2 x))) (hβ x hx)).trans_eq (mul_one _)
    have hKpos : 0 ≤ K z := Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)
    simp only [A, Real.norm_eq_abs, abs_mul, abs_of_nonneg hKpos]
    exact mul_le_mul (mul_le_mul (hM _) (hM _) (abs_nonneg _) ((abs_nonneg (f z.1)).trans (hM z.1)))
      hprod hKpos (mul_self_nonneg _)
  apply integral_nonneg_of_sample_sum μ A
  · exact Integrable.of_bound hA.aestronglyMeasurable _ (ae_of_all _ hBd)
  · exact Integrable.of_bound (hA.comp (by fun_prop : Measurable fun x : V → Spin N => (x,x))).aestronglyMeasurable _
      (ae_of_all _ fun x => hBd (x,x))
  · intro k x
    exact sphere_seam_signed_test_nonneg N S β hβ x (fun i => f (x i))

end IsingScaling.Rotor
