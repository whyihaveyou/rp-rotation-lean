import MathlibProbe.IsingShellAxialFloor

/-! Relative angular comparison for the free thermodynamic two-point function
on scales carrying a fixed positive fraction of susceptibility in the first shell. -/
noncomputable section
open Filter
open scoped Topology
namespace IsingScaling
open Packet

private theorem normalized_half_axis_upper {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {r : ℕ} (hr : 2 ≤ r) :
    normalization g r * g (Pi.single 0 ((r/2:ℕ):ℤ)) ≤ 5832 := by
  have hh : 0 < r/2 := by omega
  have hr' : 0 < r := by omega
  have hχ := (hg.positive_cube_mass hβ).2 r
  have upper := hg.axial_susceptibility_density hβ (r/2) r hh hr'
  rw [min_eq_left (by omega : r/2 ≤ r)] at upper
  have he : (![(((r/2:ℕ):ℤ)),0,0] : Site) = Pi.single 0 ((r/2:ℕ):ℤ) := by
    ext i
    fin_cases i <;> simp
  rw [he] at upper
  have hs : (r:ℝ) ≤ 3*((r/2:ℕ):ℝ) := by exact_mod_cast (show r ≤ 3*(r/2) by omega)
  have hp := pow_le_pow_left₀ (show (0:ℝ) ≤ r by positivity) hs 3
  have hgp := (hg.positive_cube_mass hβ).1 (Pi.single 0 ((r/2:ℕ):ℤ))
  have H := mul_le_mul_of_nonneg_right hp hgp
  rw [normalization,div_mul_eq_mul_div,div_le_iff₀ hχ]
  nlinarith only [H,upper]

private theorem radial_round_angular {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {k : ℕ → Site} {a D : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ D) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (radialAxisSite (k n))))
      atTop (𝓝 0) := by
  have hd (n : ℕ) :
      0 ≤ ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (radialAxisSite (k n))‖ ∧
      ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (radialAxisSite (k n))‖ ≤ 1/(R n:ℝ) := by
    rw [scaledSite_norm_radius,scaledSite_norm_radius,radius_axis,←sub_div]
    exact ⟨div_nonneg (sub_nonneg.mpr (Int.floor_le _)) (Nat.cast_nonneg _),
      div_le_div_of_nonneg_right (by linarith [Int.lt_floor_add_one (siteRadius (k n))])
        (Nat.cast_nonneg _)⟩
  exact hg.annular_angular_oscillation hβ hR (l:=radialAxisSite ∘ k) ha hk
    (fun n => (sub_nonneg.mp (hd n).1).trans (hk n).2)
    (squeeze_zero (fun n => (hd n).1) (fun n => (hd n).2)
      (tendsto_one_div_atTop_nhds_zero_nat.comp hR))

private theorem relative_of_radial_floor {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {k l : ℕ → Site} {a D : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ D)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ D)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ᶠ n in atTop, c ≤ normalization g (R n) * g (radialAxisSite (k n))) :
    Tendsto (fun n => g (k n) / g (l n)) atTop (𝓝 1) := by
  have ht := hg.annular_angular_oscillation hβ hR ha hk hl hrad
  have hround := radial_round_angular hg hβ hR ha hk
  have hsmall := (ht.sub hround).eventually_lt_const (show (0:ℝ)-0 < c/2 by linarith)
  have hden : ∀ᶠ n in atTop, c/2 ≤ normalization g (R n) * g (l n) := by
    filter_upwards [hfloor,hsmall] with n hn hs
    linarith only [hn,hs]
  apply Metric.tendsto_nhds.mpr
  intro e he
  have hsmall' := ht.abs.eventually_lt_const (show |(0:ℝ)| < e*(c/2) by rw [abs_zero]; positivity)
  filter_upwards [hden,hsmall',hR.eventually_ge_atTop 1] with n hn hs hr
  have hN : 0 < normalization g (R n) := div_pos (pow_pos (by exact_mod_cast hr : (0:ℝ)<R n) _)
    ((hg.positive_cube_mass hβ).2 _)
  have hgl : 0 < g (l n) := pos_of_mul_pos_right (lt_of_lt_of_le (half_pos hc) hn) hN.le
  rw [Real.dist_eq,div_sub_one hgl.ne',abs_div,abs_of_pos hgl,div_lt_iff₀ hgl]
  have H : normalization g (R n) * |g (k n)-g (l n)| < e*(c/2) := by
    simpa only [abs_mul,abs_of_pos hN] using hs
  exact (mul_lt_mul_iff_right₀ hN).mp (by
    calc _ < e*(c/2) := H
         _ ≤ e*(normalization g (R n)*g (l n)) := by gcongr
         _ = normalization g (R n)*(e*g (l n)) := by ring)


/-- Uniform axial lower floor at the floored Euclidean radii of all sites in
a bounded rescaled ball, on scales with nondegenerate susceptibility shell. -/
theorem IsFreeTwoPoint.eventually_shell_radial_floor {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ r : ℕ in atTop,
      1+ε ≤ susceptibility g (2*r) / susceptibility g r →
      ∀ x : Site, ‖scaledSite r x‖ ≤ D → b ≤ normalization g r * g (radialAxisSite x) := by
  obtain ⟨c,hc,hbase⟩ := hg.eventually_shell_axial_floor hβ hε
  obtain ⟨M,hM⟩ := exists_nat_ge D
  let q := c/5832
  let K := 3*M
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q^K*c, mul_pos (pow_pos hq _) hc, ?_⟩
  filter_upwards [hbase,eventually_ge_atTop 2] with r hr hr2
  intro hmass x hx
  specialize hr hmass
  let h := r/2
  let U (n : ℕ) := g (Pi.single 0 (n:ℤ))
  let N := normalization g r
  have hN : 0 < N := div_pos (pow_pos (by exact_mod_cast (show 0<r by omega) : (0:ℝ)<r) _)
    ((hg.positive_cube_mass hβ).2 _)
  have hup : N*U h ≤ 5832 := normalized_half_axis_upper hg hβ hr2
  change c ≤ N * U (2*h) at hr
  have hstep : q*U h ≤ U (2*h) := by
    apply (mul_le_mul_iff_right₀ hN).mp
    calc N * (q * U h) = q*(N*U h) := by ring
         _ ≤ q*5832 := mul_le_mul_of_nonneg_left hup hq.le
         _ = c := by dsimp [q]; ring
         _ ≤ _ := hr
  have hprop : q^K*U h ≤ U ((K+1)*h) := hg.axial_step_propagation hβ h hq.le hstep K
  have hhmono : U (2*h) ≤ U h := hg.axial_antitone hβ (show h ≤ 2*h by omega)
  rw [scaledSite_norm_radius] at hx
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hd : siteRadius x ≤ (M:ℝ)*r := (div_le_iff₀ hrpos).1 (hx.trans hM)
  have hind : ⌊siteRadius x⌋₊ ≤ M*r := by
    exact_mod_cast (Nat.floor_le (norm_nonneg (scaledSite 1 x))).trans hd
  have hindex : M*r ≤ (K+1)*h := by
    calc M*r ≤ M*(3*h) := Nat.mul_le_mul_left _ (show r ≤ 3*h by dsimp [h]; omega)
         _ ≤ (K+1)*h := by dsimp [K]; nlinarith
  have hax := hg.axial_antitone hβ (hind.trans hindex)
  have hxpos : 0 ≤ siteRadius x := norm_nonneg _
  have H : U ((K+1)*h) ≤ g (radialAxisSite x) := by
    simpa only [U,radialAxisSite,Int.natCast_floor_eq_floor hxpos] using hax
  calc q^K*c ≤ q^K*(N*U (2*h)) := mul_le_mul_of_nonneg_left hr (pow_nonneg hq.le _)
       _ ≤ q^K*(N*U h) := by gcongr
       _ = N*(q^K*U h) := by ring
       _ ≤ N*g (radialAxisSite x) := mul_le_mul_of_nonneg_left (hprop.trans H) hN.le

/-- On diverging scales with a nondegenerate first susceptibility shell,
two moving sites in a compact annulus with asymptotically equal radii
have correlation ratio tending to one. -/
theorem IsFreeTwoPoint.relative_annular_angular_oscillation {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : ∀ᶠ n in atTop, (1+ε)*susceptibility g (R n) ≤ susceptibility g (2*R n))
    {k l : ℕ → Site} {a D : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ D)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ D)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) : Tendsto (fun n => g (k n) / g (l n)) atTop (𝓝 1) := by
  obtain ⟨c,hc,hfloor⟩ := hg.eventually_shell_radial_floor hβ hε D
  apply relative_of_radial_floor hg hβ hR ha hk hl hrad hc
  filter_upwards [hR.eventually hfloor,hshell] with n hn hs
  exact hn ((le_div_iff₀ ((hg.positive_cube_mass hβ).2 _)).2 hs) _ (hk n).2

/-- Canonical thermodynamic nearest-neighbour free Ising correlation:
relative angular invariance on a nonvanishing susceptibility shell. -/
theorem thermodynamicTwoPoint_relative_angular_oscillation {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {ε : ℝ} (hε : 0 < ε)
    (hshell : ∀ᶠ n in atTop, (1+ε)*susceptibility (thermodynamicTwoPoint β) (R n) ≤
      susceptibility (thermodynamicTwoPoint β) (2*R n))
    {k l : ℕ → Site} {a D : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ D)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ D)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => thermodynamicTwoPoint β (k n) / thermodynamicTwoPoint β (l n))
      atTop (𝓝 1) :=
  (thermodynamicTwoPoint_isLimit hβ).relative_annular_angular_oscillation hβ hR hε hshell ha hk hl hrad

#print axioms thermodynamicTwoPoint_relative_angular_oscillation
end IsingScaling
