import MathlibProbe.IsingPacketFrames
import MathlibProbe.FourierShellDensity
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! A finite smooth cover of spatial dyadic shells by triples of physical
normal directions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform Real Topology ContDiff Manifold
namespace IsingScaling.ShellCone
open IsingRotation

abbrev Chart := Equiv.Perm (Fin 3) × (Fin 3 → Bool)
def frame (q : Chart) := cubicMotion q.1 q.2

def baseNormal : Fin 3 → Space := ![xyz 1 0 0,xyz 1 (-1) 0,xyz 1 0 (-1)]
def normal (q : Chart) (j : Fin 3) : Space := (frame q).symm (baseNormal j)

private theorem inner_xyz (a b c : ℝ) (x : Space) :
    inner ℝ (xyz a b c) x = a*x 0 + b*x 1 + c*x 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct,Fin.sum_univ_three,xyz,mul_comm]

theorem projections (q : Chart) (x : Space) :
    (fun j => inner ℝ (normal q j) x) =
      ![(frame q x) 0, (frame q x) 0 - (frame q x) 1, (frame q x) 0 - (frame q x) 2] := by
  funext j
  rw [← (frame q).inner_map_map (normal q j) x]
  simp only [normal, LinearIsometryEquiv.apply_symm_apply]
  fin_cases j <;> simp [baseNormal,inner_xyz,sub_eq_add_neg]

theorem norm_normal_le (q : Chart) (j : Fin 3) : ‖normal q j‖ ≤ 2 := by
  rw [normal,(frame q).symm.norm_map]
  have hh : ‖baseNormal j‖^2 ≤ 4 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    fin_cases j
    · change (1:ℝ)^2+0^2+0^2 ≤ 4; norm_num
    · change (1:ℝ)^2+(-1)^2+0^2 ≤ 4; norm_num
    · change (1:ℝ)^2+0^2+(-1)^2 ≤ 4; norm_num
  nlinarith

theorem linearIndependent_normal (q : Chart) : LinearIndependent ℝ (normal q) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have he : ∑ i, c i • baseNormal i = 0 := by
    calc _ = (frame q).toLinearEquiv.toLinearMap (∑ i, c i • normal q i) := by
               rw [map_sum]; simp [normal]
         _ = _ := by rw [hc,map_zero]
  rw [Fin.sum_univ_three] at he
  have h0 := congrArg (fun x : Space => x 0) he
  have h1 := congrArg (fun x : Space => x 1) he
  have h2 := congrArg (fun x : Space => x 2) he
  change c 0*1 + c 1*1 + c 2*1 = 0 at h0
  change c 0*0 + c 1*(-1) + c 2*0 = 0 at h1
  change c 0*0 + c 1*0 + c 2*(-1) = 0 at h2
  intro j
  fin_cases j
  · change c 0 = 0; linarith
  · change c 1 = 0; linarith
  · change c 2 = 0; linarith

private theorem coord_large (x : Space) {a : ℝ} (ha : 0 < a) (hx : a ≤ ‖x‖) :
    ∃ i, a/3 ≤ |x i| := by
  by_contra! hh
  have hsq (i : Fin 3) : (x i)^2 < (a/3)^2 := sq_lt_sq.mpr
    (by simpa only [abs_of_pos (by positivity : 0<a/3)] using hh i)
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  rw [Fin.sum_univ_three] at hnorm
  nlinarith only [pow_le_pow_left₀ ha.le hx 2,hnorm,hsq 0,hsq 1,hsq 2,sq_pos_of_pos ha]

def shell (a A : ℝ) : Set Space := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ A}
def patch (a A : ℝ) (q : Chart) : Set Space :=
  {x | ‖x‖ < A+1 ∧ ∀ j, a/4 < inner ℝ (normal q j) x}

private theorem patch_open (a A : ℝ) (q : Chart) : IsOpen (patch a A q) := by
  change IsOpen ({x : Space | ‖x‖ < A+1} ∩ {x : Space | ∀ j, a/4 < inner ℝ (normal q j) x})
  apply (isOpen_lt continuous_norm continuous_const).inter
  rw [show {x : Space | ∀ j, a/4 < inner ℝ (normal q j) x} =
      ⋂ j, {x : Space | a/4 < inner ℝ (normal q j) x} by ext; simp]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_const.inner continuous_id)

theorem cover {a A : ℝ} (ha : 0 < a) : shell a A ⊆ ⋃ q, patch a A q := by
  intro x hx
  obtain ⟨i,hi⟩ := coord_large x ha hx.1
  let p := Equiv.swap 0 i
  let s (j : Fin 3) := if j=0 then decide (x (p j) < 0) else decide (0 < x (p j))
  let q : Chart := (p,s)
  have h0 : frame q x 0 = |x i| := by
    change (if s 0 then -(x (p 0)) else x (p 0)) = |x i|
    simp only [s,ite_true,Equiv.swap_apply_left,p,decide_eq_true_eq]
    by_cases h : x i < 0
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_nonneg (le_of_not_gt h)]
  have hj (j : Fin 3) (h : j ≠ 0) : frame q x j ≤ 0 := by
    change (if s j then -(x (p j)) else x (p j)) ≤ 0
    simp only [s,ite_false, h,decide_eq_true_eq]
    split_ifs <;> linarith
  have h1 := hj 1 (by decide)
  have h2 := hj 2 (by decide)
  refine mem_iUnion.mpr ⟨q, hx.2.trans_lt (by linarith),?_⟩
  intro j
  have hh := congrFun (projections q x) j
  rw [hh]
  fin_cases j
  · change a/4 < (frame q x) 0; linarith
  · change a/4 < (frame q x) 0 - (frame q x) 1; linarith
  · change a/4 < (frame q x) 0 - (frame q x) 2; linarith

theorem exists_partition {a A : ℝ} (ha : 0<a) :
    ∃ χ : Chart → Space → ℝ, (∀ q, ContDiff ℝ ∞ (χ q) ∧ HasCompactSupport (χ q) ∧
      tsupport (χ q) ⊆ patch a A q ∧ ∀ x, 0 ≤ χ q x) ∧
      ∀ x ∈ shell a A, ∑ q, χ q x = 1 := by
  classical
  have hclosed : IsClosed (shell a A) :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  obtain ⟨χ,hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Space) hclosed
    (patch a A) (patch_open a A) (cover ha)
  refine ⟨fun q => χ q, fun q => ⟨(χ q).contMDiff.contDiff,?_,hχ q,χ.nonneg q⟩,?_⟩
  · exact (isCompact_closedBall (0:Space) (A+1)).of_isClosed_subset (isClosed_tsupport _)
      (fun x hx => Metric.mem_closedBall.mpr (by simpa using ((hχ q hx).1.le)))
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using χ.sum_eq_one hx

theorem exists_shell_pieces (v : Space → ℝ) (hv : ContDiff ℝ ∞ v)
    (hs : tsupport v ⊆ shell 1 4) :
    ∃ γ : Chart → Space → ℝ, (∀ q, ContDiff ℝ ∞ (γ q) ∧ HasCompactSupport (γ q) ∧
      tsupport (γ q) ⊆ patch 1 4 q) ∧ ∀ x, ∑ q, γ q x = v x := by
  classical
  obtain ⟨χ,hχ,hsum⟩ := exists_partition (A:=4) (show (0:ℝ)<1 by norm_num)
  refine ⟨fun q x => (χ q x)*(v x), fun q => ⟨(hχ q).1.mul hv, (hχ q).2.1.mul_right,?_⟩,?_⟩
  · exact (tsupport_mul_subset_left (f:=χ q) (g:=v)).trans (hχ q).2.2.1
  · intro x
    change (∑ q, χ q x*v x) = v x
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport v
    · simp [hsum x (hs hx)]
    · have hh : v x = 0 := by by_contra hn; exact hx (subset_tsupport v hn)
      simp [hh]

theorem exists_frequency_normal (q : Chart) (p : Space) (hp : p ≠ 0) :
    ∃ j, ‖p‖/6 ≤ |inner ℝ (normal q j) p| := by
  by_contra! hh
  let t := ‖p‖/6
  have ht : 0<t := div_pos (norm_pos_iff.mpr hp) (by norm_num)
  let x := frame q p
  have hpl (j : Fin 3) := congrFun (projections q p) j
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  rw [hpl 0] at h0
  rw [hpl 1] at h1
  rw [hpl 2] at h2
  change |x 0| < t at h0
  change |x 0 - x 1| < t at h1
  change |x 0 - x 2| < t at h2
  obtain ⟨i,hi⟩ := coord_large x (norm_pos_iff.mpr hp) (by dsimp [x]; rw [(frame q).norm_map])
  have h1' : |x 1| < 2*t := by
    rw [show x 1 = x 0 - (x 0-x 1) by ring]
    exact (abs_sub _ _).trans_lt (by linarith)
  have h2' : |x 2| < 2*t := by
    rw [show x 2 = x 0 - (x 0-x 2) by ring]
    exact (abs_sub _ _).trans_lt (by linarith)
  change 0 < ‖p‖ / 6 at ht
  dsimp only [t] at h0 h1' h2'
  fin_cases i
  · change ‖p‖/3 ≤ |x 0| at hi; linarith
  · change ‖p‖/3 ≤ |x 1| at hi; linarith
  · change ‖p‖/3 ≤ |x 2| at hi; linarith

private theorem phase_half {t : ℝ} (ht : t = 1/2 ∨ t = -(1/2)) :
    (Real.fourierChar t : ℂ) = -1 := by
  rw [Real.fourierChar_apply]
  rcases ht with rfl | rfl
  · rw [show 2 * Real.pi * (1/2:ℝ) = Real.pi by ring, Complex.exp_pi_mul_I]
  · rw [show 2 * Real.pi * (-(1/2):ℝ) = -Real.pi by ring,
      Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

private theorem fourier_difference_of_half {v p : Space}
    (hc : (Real.fourierChar (inner ℝ v p) : ℂ) = -1) (f : Space → ℂ)
    (hi : Integrable f) :
    𝓕 (FourierShell.translateDifference v f) p = 2 * 𝓕 f p := by
  have hs := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure Space) (innerₗ Space) f v) p
  change 𝓕 (fun x => f (x+v)) p = Real.fourierChar (inner ℝ v p) • 𝓕 f p at hs
  simp only [Circle.smul_def,hc,neg_one_smul] at hs
  calc 𝓕 (FourierShell.translateDifference v f) p =
        𝓕 f p - 𝓕 (fun x => f (x+v)) p := by
          simp only [Real.fourier_eq, FourierShell.translateDifference,smul_sub]
          exact integral_sub ((Real.fourierIntegral_convergent_iff p).2 hi)
            ((Real.fourierIntegral_convergent_iff p).2 (hi.comp_add_right v))
       _ = _ := by rw [hs]; ring

/-- A positive physical step in one of the three cone normals negates the
Fourier character. The fourth forward difference thus costs exactly a factor
of 16, including frequencies with a negative projection on the chosen normal. -/
theorem exists_halfPeriod (q : Chart) {p : Space} (hp : p ≠ 0) :
    ∃ (j : Fin 3) (h : ℝ), 0 < h ∧ h ≤ 3/‖p‖ ∧
      ∀ f : Space → ℂ, Integrable f → ‖𝓕 f p‖ ≤
        (1/16:ℝ) * ∫ x, ‖((FourierShell.translateDifference (h • normal q j))^[4] f) x‖ := by
  obtain ⟨j,hj⟩ := exists_frequency_normal q p hp
  let a := inner ℝ (normal q j) p
  let h := 1/(2*|a|)
  have hp' := norm_pos_iff.mpr hp
  have ha : 0 < |a| := lt_of_lt_of_le (by positivity : 0<‖p‖/6) hj
  have hpos : 0 < 2*|a| := by positivity
  refine ⟨j,h,by exact div_pos one_pos hpos,(div_le_div_iff₀ hpos hp').2 (by linarith),?_⟩
  have hc : (Real.fourierChar (inner ℝ (h • normal q j) p) : ℂ) = -1 := by
    apply phase_half
    rw [real_inner_smul_left]
    change h*a = _ ∨ h*a = _
    rcases lt_or_gt_of_ne (abs_pos.mp ha) with hn | hp
    · right
      dsimp only [h]; rw [abs_of_neg hn]; field_simp [ne_of_lt hn]
    · left
      dsimp only [h]; rw [abs_of_pos hp]; field_simp
  intro f hi
  let v := h • normal q j
  have hiter (k : ℕ) :
      𝓕 ((FourierShell.translateDifference v)^[k] f) p = (2:ℂ)^k * 𝓕 f p := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',fourier_difference_of_half hc _
        (FourierShell.translateDifference_integrable v hi k),ih,pow_succ]; ring
  have hb := FourierShell.norm_fourier_le_integral ((FourierShell.translateDifference v)^[4] f) p
  rw [hiter 4,norm_mul,norm_pow] at hb
  norm_num at hb
  change 16 * ‖𝓕 f p‖ ≤ ∫x, ‖((FourierShell.translateDifference v)^[4] f) x‖ at hb
  change ‖𝓕 f p‖ ≤ (1/16:ℝ)*∫x, ‖((FourierShell.translateDifference v)^[4] f) x‖
  linarith

end IsingScaling.ShellCone
