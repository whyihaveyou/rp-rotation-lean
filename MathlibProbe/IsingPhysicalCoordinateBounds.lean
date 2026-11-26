import MathlibProbe.IsingAnnularGradient
import MathlibProbe.IsingOffOriginBounds

/-! Coordinate-box input for spatial compactness of the actual free Ising
correlation. The mesh size is chosen from one nonzero macroscopic coordinate. -/
noncomputable section
open Filter
open scoped Topology
namespace IsingScaling.Packet

private lemma upper_step (z : Site) (i : Fin 3) :
    latticeDistance z (Function.update z i (z i+1)) = 1 := by
  classical
  unfold latticeDistance
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

private theorem local_values_increments {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (x : Space) (hx : x≠0) :
    ∃ (j : Fin 3) (t B C : ℝ), 0<t ∧ 0≤C ∧ ∀ᶠ n in atTop, ∀ z : Site,
      |(scaledSite (R n) z) j - x j| < t →
      ‖normalization g (R n)*g z‖ ≤ B ∧
      ∀ i : Fin 3, dist (normalization g (R n)*g z)
        (normalization g (R n)*g (Function.update z i (z i+1))) ≤ C/(R n:ℝ) := by
  obtain ⟨j,hj⟩ : ∃ j : Fin 3, x j ≠ 0 := by
    by_contra! h; apply hx; ext j; exact h j
  let t := min (|x j|/2) 1
  let s := t/32
  have ht : 0<t := lt_min (half_pos (abs_pos.mpr hj)) zero_lt_one
  have hs : 0<s := by dsimp [s]; positivity
  have ht1 : t≤1 := min_le_right .. 
  have ht2 : t≤|x j|/2 := min_le_left ..
  refine ⟨j,t,1728/s^3,3456/s^4,ht,by positivity,?_⟩
  have hrr : Tendsto (fun n => (R n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  filter_upwards [hrr.eventually_ge_atTop (32/t),hR.eventually_ge_atTop 1] with n hbig hpos
  intro z hnear
  let r := R n
  have hr : 0<(r:ℝ) := by exact_mod_cast hpos
  have hχ := (hg.positive_cube_mass hβ).2 r
  have hnon := (hg.positive_cube_mass hβ).1
  let k := ⌊t*(r:ℝ)/16⌋₊
  have hlarge : 32≤(r:ℝ)*t := (div_le_iff₀ ht).mp hbig
  rw [mul_comm (r:ℝ) t] at hlarge
  have hk₁ : (k:ℝ)≤t*(r:ℝ)/16 := Nat.floor_le (by positivity)
  have hk₂ : t*(r:ℝ)/16<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk : 0<k := by exact_mod_cast (show 0<(k:ℝ) by linarith only [hlarge,hk₂])
  have hlow : s*(r:ℝ)≤(k:ℝ) := by dsimp [s]; linarith only [hlarge,hk₂]
  have h2kr : 2*k ≤ r := by
    exact_mod_cast (show 2*(k:ℝ)≤r by linarith only [hk₁,mul_le_mul_of_nonneg_right ht1 hr.le])
  have hjj : t < |(scaledSite r z) j| := by
    have hh := abs_sub_le (x j) ((scaledSite r z) j) 0
    simp only [sub_zero,abs_sub_comm (x j)] at hh
    linarith only [hh,hnear,ht2]
  have habs : |(scaledSite r z) j| = ((z j).natAbs:ℝ)/(r:ℝ) := by
    change |(z j:ℝ)/(r:ℝ)| = _
    simp only [Nat.cast_natAbs,Int.cast_abs,abs_div,abs_of_pos hr]
  rw [habs] at hjj
  have hfar : 8*k+1 ≤ (z j).natAbs := by
    exact_mod_cast (show 8*(k:ℝ)+1≤((z j).natAbs:ℝ) by
      linarith only [(lt_div_iff₀ hr).mp hjj,hlarge,hk₁])
  have hcoord : k ≤ min (z j).natAbs r := le_min (by omega) (by omega)
  have hK3 : s^3*(r:ℝ)^3 ≤ ((min (z j).natAbs r:ℕ):ℝ)^3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hs.le hr.le) (hlow.trans (Nat.cast_le.mpr hcoord)) 3
  have hK4 : s^4*(r:ℝ)^4 ≤ AnnularGradient.weight k r := by
    rw [← mul_pow]
    calc
      _ ≤ (k:ℝ)^4 := pow_le_pow_left₀ (mul_nonneg hs.le hr.le) hlow 4
      _ ≤ _ := by
        unfold AnnularGradient.weight
        rw [min_eq_left h2kr]
        push_cast
        nlinarith [show 0≤(k:ℝ)^4 by positivity,show 0≤(k:ℝ)^3 by positivity]
  refine ⟨?_,?_⟩
  · have hbound := (mul_le_mul_of_nonneg_right hK3 (hnon z)).trans
        (site_coordinate_density hg hβ z j r (by omega) hpos)
    change ‖(r:ℝ)^3/susceptibility g r * g z‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (div_nonneg (by positivity) hχ.le) (hnon z))]
    field_simp [hχ.ne',hs.ne']
    nlinarith only [hbound]
  · intro i
    let y := Function.update z i (z i+1)
    have hbound := (mul_le_mul_of_nonneg_right hK4 (abs_nonneg (g z-g y))).trans
        (AnnularGradient.adjacent hg hβ k r hk hpos z y (upper_step z i) ⟨j,hfar⟩)
    change dist ((r:ℝ)^3/susceptibility g r * g z) ((r:ℝ)^3/susceptibility g r * g y) ≤ _
    rw [Real.dist_eq,←mul_sub,abs_mul,abs_of_nonneg (div_nonneg (by positivity) hχ.le)]
    field_simp [hχ.ne',hs.ne',hr.ne']
    nlinarith only [hbound]

theorem physical_coordinate_bounds {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (x : Space) (hx : x≠0) :
    ∃ r C : ℝ, 0<r ∧ 0≤C ∧ ∀ᶠ n in atTop, ∀ z : Site,
      (∀ j, |(scaledSite (R n) z) j-x j|<r) →
      ∀ i : Fin 3, dist (normalization g (R n)*g z)
        (normalization g (R n)*g (Function.update z i (z i+1))) ≤ C/(R n:ℝ) := by
  obtain ⟨j,t,B,C,ht,hC,h⟩ := local_values_increments hg hβ hR x hx
  refine ⟨t,C,ht,hC,?_⟩
  filter_upwards [h] with n hn z hz
  exact (hn z (hz j)).2

theorem physical_coordinate_values {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (x : Space) (hx : x≠0) :
    ∃ B, ∀ᶠ n in atTop, ‖normalization g (R n)*g (gridIndex (R n) x)‖ ≤ B := by
  obtain ⟨j,t,B,C,ht,hC,h⟩ := local_values_increments hg hβ hR x hx
  have H := gridIndex_scaled_tendsto (v := fun _ => x) hR tendsto_const_nhds
  have H' := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousAt.tendsto.comp H
  refine ⟨B,?_⟩
  filter_upwards [h,(Metric.tendsto_nhds.1 H') t ht] with n hn hx
  exact (hn _ (by simpa [Real.dist_eq] using hx)).1

end IsingScaling.Packet
