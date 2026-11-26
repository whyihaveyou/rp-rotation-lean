import MathlibProbe.IsingOffOriginPackets
import MathlibProbe.IsingRotationFromPackets

/-! Physical normal coordinates and the cubic symmetries required to use
the two lattice reflection geometries in the angular theorem. -/
noncomputable section
open MeasureTheory
open scoped Real
namespace IsingRotation

def horizontalFrame (α : ℝ) : Space3 ≃ₗᵢ[ℝ] Space3 where
  toFun p := planeFrequency (-α) (p 0) (p 1) (p 2)
  invFun p := planeFrequency α (p 0) (p 1) (p 2)
  left_inv p := by
    ext i; fin_cases i
    · change _ * Real.cos α - _ * Real.sin α = p 0
      simp [planeFrequency, xyz]
      linear_combination (p 0) * Real.sin_sq_add_cos_sq α
    · change _ * Real.sin α + _ * Real.cos α = p 1
      simp [planeFrequency, xyz]
      linear_combination (p 1) * Real.sin_sq_add_cos_sq α
    · rfl
  right_inv p := by
    ext i; fin_cases i
    · change _ * Real.cos (-α) - _ * Real.sin (-α) = p 0
      simp [planeFrequency, xyz]
      linear_combination (p 0) * Real.sin_sq_add_cos_sq α
    · change _ * Real.sin (-α) + _ * Real.cos (-α) = p 1
      simp [planeFrequency, xyz]
      linear_combination (p 1) * Real.sin_sq_add_cos_sq α
    · rfl
  map_add' p q := by ext i; fin_cases i <;> simp [planeFrequency, xyz] <;> ring
  map_smul' c p := by ext i; fin_cases i <;> simp [planeFrequency, xyz] <;> ring
  norm_map' p := by
    change ‖planeFrequency (-α) (p 0) (p 1) (p 2)‖ = ‖p‖
    have h := norm_planeFrequency_sq (-α) (p 0) (p 1) (p 2)
    have hp : ‖p‖^2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith [norm_nonneg (planeFrequency (-α) (p 0) (p 1) (p 2)), norm_nonneg p]

theorem horizontalFrame_inv (α t u v : ℝ) :
    (horizontalFrame α).symm (xyz t u v) = planeFrequency α t u v := rfl

end IsingRotation
namespace IsingScaling.Packet
open IsingRotation

def frameAngle (d : Bool) : ℝ := if d then -(π/4) else 0
def transverseStretch (d : Bool) : ℝ := if d then Real.sqrt 2 else 1
def normalStretch (d : Bool) : ℝ := 2 * transverseStretch d

theorem transverseStretch_pos (d : Bool) : 0 < transverseStretch d := by
  cases d <;> simp [transverseStretch]

theorem normalStretch_pos (d : Bool) : 0 < normalStretch d :=
  mul_pos (by norm_num) (transverseStretch_pos d)

theorem physical_frame (d : Bool) (t u v : ℝ) :
    (horizontalFrame (frameAngle d)) (packetVector d t u v) =
      xyz (normalStretch d * t) (transverseStretch d * u) v := by
  cases d <;> ext i <;> fin_cases i <;>
    simp [horizontalFrame, frameAngle, normalStretch, transverseStretch,
      packetVector, planeFrequency, xyz, Real.cos_pi_div_four, Real.sin_pi_div_four] <;> ring

/-- For each of the angular charts, one of the two physical transfer
normals suffices, with exactly the same transverse coordinates. -/
theorem tangent_frequency_base {β : ℝ} {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (ht : IsTwoPointTangent β μ) {C : Space → ℝ} (hF : HasTwoPointFourierDensity μ C)
    (hL : LocallyIntegrable C volume) (hc : ContinuousOn C {0}ᶜ) (i : ℤ) :
    ∃ d : Bool, ∀ ω u v, C (planeFrequency ((i:ℝ)*(π/4)) ω u v) =
        C (planeFrequency (frameAngle d) ω u v) := by
  let T := cubicMotion (Equiv.swap 0 1) (fun j => decide (j = 0))
  have hT (x y z : ℝ) : T (xyz x y z) = xyz (-y) x z := by
    ext j; fin_cases j <;> rfl
  have hC (p : Space) := fourierDensity_invariant_of_map_eq hF hL hc T
    (ht.cubic_invariant _ _) p
  have hper (ω u v : ℝ) :
      Function.Periodic (fun α => C (planeFrequency α ω u v)) (π/2) := by
    intro α
    change C (planeFrequency (α+π/2) ω u v) = C (planeFrequency α ω u v)
    rw [← hC (planeFrequency α ω u v)]
    apply congrArg C
    unfold planeFrequency
    rw [hT]
    simp [Real.cos_add, Real.sin_add]
    congr 1
    ring
  let j : ℤ := (i+1)/2
  have hcases : i = 2*j ∨ i = 2*j-1 := by dsimp [j]; omega
  rcases hcases with he | he
  · refine ⟨false, fun ω u v => ?_⟩
    have ha : (i:ℝ)*(π/4) = frameAngle false + (j:ℝ)*(π/2) := by
      rw [he]; simp [frameAngle]; ring
    rw [ha]; exact (hper ω u v).int_mul j _
  · refine ⟨true, fun ω u v => ?_⟩
    have ha : (i:ℝ)*(π/4) = frameAngle true + (j:ℝ)*(π/2) := by
      rw [he]; simp [frameAngle]; ring
    rw [ha]; exact (hper ω u v).int_mul j _

end IsingScaling.Packet
