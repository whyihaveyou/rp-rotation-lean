import MathlibProbe.FourierShellDensity

/-! Translation estimates for compact smooth cutoffs used on a spatial
annulus. The product formula keeps all intermediate evaluation sites. -/
noncomputable section
open MeasureTheory Set
open scoped Topology NNReal ContDiff
namespace IsingRotation.FourierShell
namespace Cutoff

def diff {F : Type*} [Sub F] (h : V) (f : V → F) (x : V) : F := f x - f (x+h)

private theorem smooth_iter {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiff ℝ ∞ f) (h : V) (k : ℕ) :
    ContDiff ℝ ∞ ((diff h)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.sub (ih.comp (contDiff_id.add contDiff_const))

private theorem fderiv_iter {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiff ℝ ∞ f) (h : V) (k : ℕ) :
    fderiv ℝ ((diff h)^[k] f) = (diff h)^[k] (fderiv ℝ f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    let g := (diff h)^[k] f
    have hd : Differentiable ℝ g := (smooth_iter hf h k).differentiable (by simp)
    funext x
    change fderiv ℝ (fun y => g y - g (y+h)) x = _
    rw [fderiv_fun_sub (hd x) ((differentiableAt_comp_add_right _).2 (hd (x+h))),
        fderiv_comp_add_right]
    change fderiv ℝ g x - fderiv ℝ g (x+h) = _
    simp only [g,ih,diff]

theorem smooth_difference_bound (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : V → F) (hf : ContDiff ℝ ∞ f) (hk : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h x, ‖((diff h)^[k] f) x‖ ≤ C*‖h‖^k := by
  induction k generalizing F with
  | zero =>
    obtain ⟨B,hB⟩ := hk.exists_bound_of_continuousOn hf.continuous.continuousOn
    refine ⟨max B 0, le_max_right .., fun h x => ?_⟩
    simp only [pow_zero,mul_one,Function.iterate_zero_apply]
    by_cases hx : x ∈ tsupport f
    · exact (hB x hx).trans (le_max_left ..)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  | succ k ih =>
    obtain ⟨B,hB,hBd⟩ := ih (fderiv ℝ f) (hf.fderiv_right (by simp)) (hk.fderiv (𝕜:=ℝ))
    refine ⟨B,hB,fun h x => ?_⟩
    let g := (diff h)^[k] f
    let L : ℝ≥0 := ⟨B*‖h‖^k, by positivity⟩
    have hL : LipschitzWith L g := by
      apply lipschitzWith_of_nnnorm_fderiv_le ((smooth_iter hf h k).differentiable (by simp))
      intro z
      change ‖fderiv ℝ ((diff h)^[k] f) z‖ ≤ B*‖h‖^k
      rw [fderiv_iter hf]; exact hBd h z
    rw [Function.iterate_succ_apply']
    change ‖g x-g (x+h)‖ ≤ _
    have hh := hL.dist_le_mul x (x+h)
    change dist (g x) (g (x+h)) ≤ (B*‖h‖^k)*dist x (x+h) at hh
    simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg, pow_succ, mul_assoc] using hh

theorem fourth_product {K : Type*} [CommRing K] (h : V) (u v : V → K) (x : V) :
    ((diff h)^[4] (fun z => u z*v z)) x =
       ((diff h)^[4] u) x * v x +
       4*((diff h)^[3] u) (x+h) * (diff h v) x +
       6*((diff h)^[2] u) (x+(2:ℕ) • h) * ((diff h)^[2] v) x +
       4*(diff h u) (x+(3:ℕ) • h) * ((diff h)^[3] v) x +
       u (x+(4:ℕ) • h) * ((diff h)^[4] v) x := by
  norm_num [Function.iterate_succ_apply',diff, succ_nsmul, ← add_assoc]
  ring

theorem diff_scale (c : ℝ) (h : V) (u : V → ℝ) (k : ℕ) (x : V) :
    ((diff h)^[k] (fun z => u (c • z))) x = ((diff (c • h))^[k] u) (c • x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',diff,ih,smul_add]

theorem diff_of_stencil_zero {F : Type*} [AddGroup F] (h : V) (k : ℕ) (u : V → F) (x : V)
    (hz : ∀ i ≤ k, u (x + i • h) = 0) : ((diff h)^[k] u) x = 0 := by
  induction k generalizing x with
  | zero => simpa using hz 0 (by omega)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change _ - _ = 0
    rw [ih x (fun i hi => hz i (by omega)), ih (x+h) (fun i hi => ?_), sub_self]
    simpa only [succ_nsmul,add_assoc,add_left_comm,add_comm] using hz (i+1) (by omega)

private lemma cutoff_uniform (γ : V → ℝ) (hs : ContDiff ℝ ∞ γ) (hk : HasCompactSupport γ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≤ 4, ∀ w y, ‖((diff w)^[k] γ) y‖ ≤ A*‖w‖^k := by
  choose C hC h using fun k : ℕ => smooth_difference_bound k γ hs hk
  let A := ∑ k ∈ Finset.range 5, C k
  refine ⟨A, Finset.sum_nonneg (fun k _ => hC k), fun k hk w y => (h k w y).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (f:=C) (fun i _ => hC i) (Finset.mem_range.mpr (by omega))

private theorem product_estimate (u v : V → ℝ) (w x : V) {A B r : ℝ}
    (hA : 0≤A) (_hB : 0≤B) (hr : 0≤r)
    (hu : ∀ k ≤ 4, ∀ z, ‖((diff w)^[k] u) z‖ ≤ A*r^k)
    (hv : ∀ k ≤ 4, ‖((diff w)^[k] v) x‖ ≤ B*r^k) :
    ‖((diff w)^[4] (fun z => u z*v z)) x‖ ≤ (16*A*B)*r^4 := by
  let term (i : Fin 5) := (Nat.choose 4 i:ℝ) *
    ((diff w)^[4-i.val] u) (x+i.val • w) * ((diff w)^[i.val] v) x
  have he : ((diff w)^[4] (fun z => u z*v z)) x = ∑ i, term i := by
    rw [fourth_product]
    norm_num [term,Fin.sum_univ_succ,Nat.choose,Function.iterate_succ_apply']
    ring
  rw [he]
  calc
    _ ≤ ∑ i : Fin 5, ‖term i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 5, (Nat.choose 4 i:ℝ) * (A*r^(4-i.val)) * (B*r^i.val) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [term,norm_mul, Real.norm_natCast]
      gcongr
      · exact hu _ (by omega) _
      · exact hv _ (by omega)
    _ = _ := by norm_num [Fin.sum_univ_succ,Nat.choose]; ring

/-- A compact piece supported on a positive cone permits the four-step
product bound even if its first evaluation site lies outside the support. -/
theorem localized_fourth (d : V) (hd : ‖d‖ ≤ 2) (γ f : V → ℝ)
    (hs : ContDiff ℝ ∞ γ) (hk : HasCompactSupport γ)
    (hγ : ∀ y ∈ tsupport γ, 1/4 ≤ inner ℝ d y ∧ ‖y‖ ≤ 5)
    {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ k ≤ 4, ∀ {L t : ℝ}, 1≤L → 0≤t → ∀ x, L/8 ≤ inner ℝ d x →
        ‖((diff (t • d))^[k] f) x‖ ≤ B*(t/L)^k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L t : ℝ}, 1≤L → 0≤t → t≤L/256 → ∀ x,
      let P := (diff (t • d))^[4] (fun z => γ (L⁻¹ • z)*f z)
      ‖P x‖ ≤ C*(t/L)^4 ∧ (6*L ≤ ‖x‖ → P x = 0) := by
  obtain ⟨A,hA,hcut⟩ := cutoff_uniform γ hs hk
  refine ⟨256*A*B,by positivity,?_⟩
  intro L t hL ht hsmall x
  have hL' : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let w := t • d
  let U (z : V) := γ (L⁻¹ • z)
  change ‖((diff w)^[4] (fun z => U z * f z)) x‖ ≤ _ ∧ _
  by_cases hhit : ∃ i : ℕ, i≤4 ∧ L⁻¹ • (x+i • w) ∈ tsupport γ
  · obtain ⟨i,hi,hz⟩ := hhit
    obtain ⟨hproj,hrad⟩ := hγ _ hz
    have hi' : (i:ℝ) ≤ 4 := by exact_mod_cast hi
    have hw : ‖w‖ ≤ 2*t := by
      rw [show ‖w‖ = |t| * ‖d‖ from norm_smul t d,abs_of_nonneg ht,mul_comm]
      gcongr
    have hw' : ‖i • w‖ ≤ 8*t := by
      exact norm_nsmul_le.trans (by nlinarith [mul_le_mul hi' hw (norm_nonneg w) (by norm_num)])
    rw [real_inner_smul_right,inv_mul_eq_div,le_div_iff₀ hL'] at hproj
    rw [inner_add_right] at hproj
    have hcross : inner ℝ d (i • w) ≤ 16*t :=
      (real_inner_le_norm _ _).trans (by nlinarith [mul_le_mul hd hw' (norm_nonneg _) (by norm_num)])
    have hbuf : L/8 ≤ inner ℝ d x := by linarith
    have htr : 0 ≤ t/L := div_nonneg ht hL'.le
    have hU (k : ℕ) (h4 : k ≤ 4) (z : V) : ‖((diff w)^[k] U) z‖ ≤ A*(2*(t/L))^k := by
      rw [show ((diff w)^[k] U) z = _ from diff_scale L⁻¹ w γ k z]
      apply (hcut k h4 _ _).trans
      gcongr
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL'.le), inv_mul_eq_div]
      rw [← mul_div_assoc]; gcongr
    have hv (k : ℕ) (h4 : k≤4) : ‖((diff w)^[k] f) x‖ ≤ B*(2*(t/L))^k :=
      (hf k h4 hL ht x hbuf).trans (by gcongr; linarith)
    refine ⟨(product_estimate U f w x hA hB (by positivity) hU hv).trans_eq (by ring),?_⟩
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hL'.le),inv_mul_eq_div,div_le_iff₀ hL'] at hrad
    have hnx : ‖x‖ ≤ ‖x+i • w‖ + ‖i • w‖ := by simpa using norm_sub_le (x+i • w) (i • w)
    intro hx
    exfalso; linarith
  · push Not at hhit
    have hz := diff_of_stencil_zero w 4 (fun z => U z*f z) x (fun i hi => by
      simp [U,image_eq_zero_of_notMem_tsupport (hhit i hi)])
    exact ⟨hz ▸ (by simp [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 256*A) hB) (by positivity : 0 ≤ (t/L)^4)]),
      fun _ => hz⟩

end Cutoff
end IsingRotation.FourierShell
