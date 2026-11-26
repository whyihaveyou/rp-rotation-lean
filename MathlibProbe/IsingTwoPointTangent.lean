import MathlibProbe.CubicIsingTwoPoint
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Cube-normalized lattice two-point measures and their vague tangents.
The finite-to-infinite hypothesis is a limit of explicit Gibbs sums.
Only the microscopic signed permutations are used in this module. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal CompactlySupported
namespace IsingScaling

abbrev Space := EuclideanSpace ℝ (Fin 3)

def susceptibility (g : Site → ℝ) (R : ℕ) : ℝ := ∑ x ∈ cube R, g x

def scaledSite (R : ℕ) (x : Site) : Space :=
  WithLp.toLp 2 (fun i => (x i : ℝ) / (R : ℝ))

/-- For nonnegative correlations and positive cube mass the coefficient is g/χ. -/
def twoPointMeasure (g : Site → ℝ) (R : ℕ) : Measure Space :=
  Measure.sum fun x => ENNReal.ofReal (g x / susceptibility g R) •
    Measure.dirac (scaledSite R x)

/-- Original-model tangent data. Convergence is tested against every real,
compactly supported continuous function and the scales tend to infinity. -/
structure IsTwoPointTangent (β : ℝ) (μ : Measure Space) : Prop where
  realizes : ∃ (g : Site → ℝ) (R : ℕ → ℕ),
    IsFreeTwoPoint β g ∧ (∀ x, 0 ≤ g x) ∧ (∀ j, 0 < susceptibility g (R j)) ∧
    Tendsto R atTop atTop ∧
    ∀ f : C_c(Space, ℝ), Tendsto (fun j => ∫ x, f x ∂twoPointMeasure g (R j))
      atTop (𝓝 (∫ x, f x ∂μ))

theorem twoPointMeasure_map {β g} (hg : IsFreeTwoPoint β g) (R : ℕ)
    (p : Equiv.Perm (Fin 3)) (s) (T : Space ≃ₜ Space)
    (hT : ∀ x, T (scaledSite R x) = scaledSite R (signedPerm p s x)) :
    (twoPointMeasure g R).map T = twoPointMeasure g R := by
  classical
  unfold twoPointMeasure
  rw [Measure.map_sum T.continuous.measurable.aemeasurable]
  ext B hB
  simp only [Measure.sum_apply _ hB, Measure.map_smul,
    Measure.map_dirac' T.continuous.measurable, hT]
  let b (x : Site) := (ENNReal.ofReal (g x / susceptibility g R) •
    Measure.dirac (scaledSite R x)) B
  calc
    _ = ∑' x, b (signedPerm p s x) := by
      apply tsum_congr
      intro x
      simp only [b, freeLimit_signedPerm hg]
    _ = _ := Equiv.tsum_eq (signedPerm p s) b

theorem IsTwoPointTangent.map_eq {β : ℝ} {μ : Measure Space} [μ.Regular] (hμ : IsTwoPointTangent β μ)
    (p : Equiv.Perm (Fin 3)) (s) (T : Space ≃ₜ Space)
    (hT : ∀ R x, T (scaledSite R x) = scaledSite R (signedPerm p s x)) :
    μ.map T = μ := by
  obtain ⟨g, R, hg, _, _, _, hlim⟩ := hμ.realizes
  have : (μ.map T).Regular := Measure.Regular.map T
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fT := f.comp T.toCocompactMap
  have hcomp (ν : Measure Space) : ∫ x, f x ∂ν.map T = ∫ x, fT x ∂ν := by
    exact integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable
  rw [hcomp]
  apply tendsto_nhds_unique (hlim fT)
  have heq (j : ℕ) : ∫ x, fT x ∂twoPointMeasure g (R j) = ∫ x, f x ∂twoPointMeasure g (R j) := by
    rw [← hcomp, twoPointMeasure_map hg _ p s T (hT _)]
  simpa only [heq] using hlim f

/-- The signed coordinate permutation acting on Euclidean three-space. -/
def cubicMotion (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : Space ≃ₗᵢ[ℝ] Space where
  toFun x := WithLp.toLp 2 fun i => if s i then -x (p i) else x (p i)
  invFun y := WithLp.toLp 2 fun j => if s (p.symm j) then -y (p.symm j) else y (p.symm j)
  left_inv x := by
    ext i
    change (if s (p.symm i) then -(if s (p.symm i) then -_ else _) else
      (if s (p.symm i) then -_ else _)) = _
    cases s (p.symm i) <;> simp
  right_inv y := by
    ext i
    change (if s i then -(if s (p.symm (p i)) then -_ else _) else
      (if s (p.symm (p i)) then -_ else _)) = _
    simp only [Equiv.symm_apply_apply]
    cases s i <;> simp
  map_add' x y := by
    ext i
    change (if s i then -(x (p i) + y (p i)) else _) = (if s i then _ else _) + (if s i then _ else _)
    cases s i <;> simp [add_comm]
  map_smul' t x := by
    ext i
    change (if s i then -(t * x (p i)) else _) = t * (if s i then _ else _)
    cases s i <;> simp
  norm_map' x := by
    let y : Space := WithLp.toLp 2 fun i => if s i then -x (p i) else x (p i)
    change ‖y‖ = ‖x‖
    have hh : ‖y‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      calc
        _ = ∑ i, (x (p i))^2 := by
          apply Finset.sum_congr rfl
          intro i _
          change (if s i then -x (p i) else x (p i)) ^ 2 = _
          cases s i <;> simp
        _ = _ := Equiv.sum_comp p (fun i => (x i)^2)
    nlinarith [norm_nonneg y, norm_nonneg x]

@[simp] theorem cubicMotion_scaledSite (p : Equiv.Perm (Fin 3)) (s) (R x) :
    cubicMotion p s (scaledSite R x) = scaledSite R (signedPerm p s x) := by
  ext i
  change (if s i then -((x (p i) : ℝ) / R) else _) =
    (((if s i then -x (p i) else x (p i) : ℤ) : ℝ) / R)
  cases s i <;> simp [scaledSite, neg_div]

theorem IsTwoPointTangent.cubic_invariant {β : ℝ} {μ : Measure Space} [μ.Regular]
    (hμ : IsTwoPointTangent β μ) (p : Equiv.Perm (Fin 3)) (s) :
    μ.map (cubicMotion p s) = μ :=
  hμ.map_eq p s (cubicMotion p s).toHomeomorph (cubicMotion_scaledSite p s)

end IsingScaling
