import MathlibProbe.IsingTangentCells
import MathlibProbe.IsingAnnularMass
import MathlibProbe.TransversePacketLocalization

/-! Pointwise size of an off-origin spatial two-point limit. The lattice
estimate is the susceptibility-normalized reflected packet bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace IsingScaling.Packet
open IsingRotation

theorem OffOriginLimit.nonneg_of_free {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g)
    (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (x : Space) (hx : x ≠ 0) : 0 ≤ f x := by
  obtain ⟨hn, hχ⟩ := hg.positive_cube_mass hβ
  apply ge_of_tendsto (hsp x hx _ (gridIndex_scaled_tendsto (v := fun _ => x) hR tendsto_const_nhds))
  exact Eventually.of_forall fun n => mul_nonneg (div_nonneg (by positivity) (hχ _).le) (hn _)

theorem site_coordinate_density {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) (a : Site) (i : Fin 3) (r : ℕ)
    (hi : 2 ≤ (a i).natAbs) (hr : 0 < r) :
    ((min (a i).natAbs r : ℕ):ℝ)^3 * g a ≤ 1728*susceptibility g r := by
  let p := Equiv.swap 0 i
  let s : Fin 3 → Bool := fun _ => decide (a i < 0)
  let b := signedPerm p s a
  have h0 : b 0 = ((a i).natAbs : ℤ) := by
    change (if decide (a i < 0) then -(a (p 0)) else a (p 0)) = _
    rw [show p 0 = i from Equiv.swap_apply_left _ _, Int.natCast_natAbs]
    by_cases h : a i < 0
    · simp [h,abs_of_neg h]
    · simp [h,abs_of_nonneg (le_of_not_gt h)]
  have hb : ![((a i).natAbs : ℤ), b 1,b 2] = b := by
    funext j; fin_cases j
    · exact h0.symm
    · rfl
    · rfl
  have H := hg.site_susceptibility_density hβ (a i).natAbs r hi hr (b 1) (b 2)
    (Equiv.refl _) (fun _ => false)
  rw [freeLimit_signedPerm hg, hb, show g b = g a from freeLimit_signedPerm hg p s a] at H
  exact H

/-- The actual coordinate bound keeps its lattice constant after passing to
the moving grid of any thermodynamic two-point limit. -/
theorem OffOriginLimit.coordinate_density {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g)
    (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    (min |x i| 1)^3 * f x ≤ 1728 := by
  by_cases hxi : x i = 0
  · simp [hxi]
  let q (n : ℕ) := gridIndex (R n) x
  let k (n : ℕ) := (q n i).natAbs
  have ht := gridIndex_scaled_tendsto (v := fun _ => x) hR tendsto_const_nhds
  have hcoord := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.tendsto.comp ht
  have ha : Tendsto (fun n => (k n:ℝ)/(R n:ℝ)) atTop (𝓝 |x i|) := by
    have he (n : ℕ) : (k n:ℝ)/(R n:ℝ) = |(scaledSite (R n) (q n)) i| := by
      change (((q n i).natAbs:ℝ) / (R n:ℝ)) = |(q n i:ℝ)/(R n:ℝ)|
      simp only [Nat.cast_natAbs, Int.cast_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (R n) : (0:ℝ) ≤ R n)]
    simp_rw [he]
    exact hcoord.abs
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := ((ha.min hone).pow 3).mul (hsp x hx q ht)
  apply le_of_tendsto hlim
  have hab := abs_pos.mpr hxi
  have h2 : 0 < |x i|/2 := half_pos hab
  have hRR : Tendsto (fun n => (R n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  filter_upwards [ha.eventually_const_lt (half_lt_self hab),
    hRR.eventually_ge_atTop (2/(|x i|/2)),hR.eventually_ge_atTop 1] with n hnear hlarge hpos
  have hr : 0 < (R n:ℝ) := by exact_mod_cast (show 0 < R n by omega)
  have hk : 2 ≤ k n := by
    have h₁ := (lt_div_iff₀ hr).mp hnear
    have h₂ := (div_le_iff₀ h2).mp hlarge
    exact_mod_cast (show (2:ℝ) ≤ (k n:ℝ) by nlinarith only [h₁,h₂])
  have hχ := (hg.positive_cube_mass hβ).2 (R n)
  have hh := site_coordinate_density hg hβ (q n) i (R n) hk (by omega)
  change min ((k n:ℝ)/(R n:ℝ)) 1 ^ 3 * (normalization g (R n)*g (q n)) ≤ _
  have htmin : min ((k n:ℝ)/(R n:ℝ)) 1 = ((min (k n) (R n):ℕ):ℝ)/(R n:ℝ) := by
    simpa only [div_self hr.ne',Nat.cast_min] using min_div_div_right hr.le (k n:ℝ) (R n:ℝ)
  rw [htmin]
  calc _ = ((min (k n) (R n):ℕ):ℝ)^3 * g (q n) / susceptibility g (R n) := by
            unfold normalization; field_simp
       _ ≤ _ := (div_le_iff₀ hχ).2 hh

theorem OffOriginLimit.boundedAwayFromOrigin_of_free {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hsp : OffOriginLimit g R f) : BoundedAwayFromOrigin f := by
  intro ε hε
  let δ := min (ε/3) 1
  have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
  refine ⟨1728/δ^3, fun x hx => ?_⟩
  have hn : x ≠ 0 := norm_pos_iff.mp (hε.trans_le hx)
  have hi : ∃ i, ε/3 ≤ |x i| := by
    by_contra! hh
    have hsq (i : Fin 3) : (x i)^2 < (ε/3)^2 := sq_lt_sq.mpr
      (by simpa only [abs_of_pos (by positivity : 0<ε/3)] using hh i)
    have hnorm := EuclideanSpace.real_norm_sq_eq x
    rw [Fin.sum_univ_three] at hnorm
    have he := pow_le_pow_left₀ hε.le hx 2
    nlinarith only [he,hnorm,hsq 0,hsq 1,hsq 2,sq_pos_of_pos hε]
  obtain ⟨i, hi⟩ := hi
  have hfx := hsp.nonneg_of_free hg hβ hR x hn
  rw [Real.norm_eq_abs, abs_of_nonneg hfx,le_div_iff₀ (pow_pos hδ 3),mul_comm]
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hδ.le (min_le_min_right 1 hi) 3) hfx).trans
    (hsp.coordinate_density hg hβ hR x hn i)

end IsingScaling.Packet
