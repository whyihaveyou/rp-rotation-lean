import MathlibProbe.IsingTangentAnnularPartition
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The mass in a fixed compact observation survives every tangent. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology CompactlySupported
namespace IsingScaling

private def testBump : ContDiffBump (0:Space) := ⟨2,3,by norm_num,by norm_num⟩

private theorem scaled_cube_norm {r : ℕ} (hr : 0<r) {x : Site} (hx : x ∈ cube r) :
    ‖scaledSite r x‖ ≤ 2 := by
  have hr' : 0<(r:ℝ) := by exact_mod_cast hr
  have h (i : Fin 3) : |scaledSite r x i| ≤ 1 := by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
    change |(x i:ℝ)/(r:ℝ)| ≤ 1
    rw [abs_div,abs_of_pos hr',div_le_one hr',abs_le]
    exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
  have hq (i : Fin 3) : (scaledSite r x i)^2 ≤ 1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  nlinarith [EuclideanSpace.real_norm_sq_eq (scaledSite r x), Fin.sum_univ_three
    (fun i => (scaledSite r x i)^2),hq 0,hq 1,hq 2]

/-- A compact bump covering the whole normalization cube retains at least
unit mass in every vague limit of a nonnegative pair kernel. -/
theorem twoPointMeasure_vague_ne_zero {g : Site → ℝ} {R : ℕ → ℕ} {μ : Measure Space}
    (gn : ∀ k, 0 ≤ g k) (hχ : ∀ n, 0 < susceptibility g (R n))
    (hR : Tendsto R atTop atTop)
    (hm : ∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ x, φ x ∂μ))) : μ ≠ 0 := by
  let ψ : C_c(Space,ℝ) := ⟨⟨testBump,testBump.continuous⟩,testBump.hasCompactSupport⟩
  have hl : 1 ≤ ∫ x, ψ x ∂μ := by
    apply ge_of_tendsto (hm ψ)
    filter_upwards [hR.eventually_ge_atTop 1] with n hr
    let r := R n
    have hr' : 0<(r:ℝ) := by exact_mod_cast hr
    have hσ := hχ n
    let b (k : Site) := g k/susceptibility g r * ψ (scaledSite r k)
    have hb (k : Site) : 0 ≤ b k := mul_nonneg (div_nonneg (gn _) hσ.le) testBump.nonneg
    have hz (k : Site) (hk : k ∉ cube (3*r)) : b k = 0 := by
      change _ * testBump _ = 0
      apply mul_eq_zero_of_right
      apply testBump.zero_of_le_dist
      rw [dist_zero_right]
      change 3 ≤ ‖scaledSite r k‖
      by_contra! h
      apply hk
      apply Fintype.mem_piFinset.2
      intro i
      have hci := (PiLp.norm_apply_le (scaledSite r k) i).trans h.le
      change |(k i:ℝ)/(r:ℝ)| ≤ 3 at hci
      rw [abs_div,abs_of_pos hr',div_le_iff₀ hr',abs_le] at hci
      exact Finset.mem_Icc.2 ⟨by exact_mod_cast hci.1,by exact_mod_cast hci.2⟩
    have he (k : Site) (hk : k ∈ cube r) : b k = g k/susceptibility g r := by
      have h1 : testBump (scaledSite r k) = 1 := testBump.one_of_mem_closedBall
        (by simpa [Metric.mem_closedBall,dist_zero_right,testBump,r] using scaled_cube_norm hr hk)
      change _ * testBump _ = _
      rw [h1, mul_one]
    rw [twoPointMeasure,integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (div_nonneg (gn _) hσ.le),smul_eq_mul]
    change 1 ≤ ∑' k, b k
    rw [tsum_eq_sum (s:=cube (3*r)) hz]
    calc
      1 = ∑ k ∈ cube r, b k := by
        rw [Finset.sum_congr rfl he,←Finset.sum_div,←susceptibility,div_self hσ.ne']
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
        intro k hk; apply Fintype.mem_piFinset.2
        intro i
        obtain ⟨hl,hu⟩ := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)
        apply Finset.mem_Icc.2; push_cast; constructor <;> omega)
        (fun k _ _ => hb k)
  intro h
  rw [h] at hl
  norm_num at hl

theorem IsTwoPointTangent.ne_zero {β : ℝ} {μ : Measure Space}
    (ht : IsTwoPointTangent β μ) : μ ≠ 0 := by
  obtain ⟨g,R,_,gn,hχ,hR,hm⟩ := ht.realizes
  exact twoPointMeasure_vague_ne_zero gn hχ hR hm

end IsingScaling
