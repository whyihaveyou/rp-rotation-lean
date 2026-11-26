import MathlibProbe.SpatialEnvelopeDoubling
import MathlibProbe.IsingLatticePathCompactness
import MathlibProbe.ModelSpatialPacketRotation

/-! # Local oscillation of a stationary covariance and its spatial tangent

On an annulus choose one nonzero limiting coordinate and a fixed fraction
of its size. At resolution R take an integer l proportional to R, small
enough that all sites in this coordinate neighborhood are outside the cube
of radius D l. The susceptibility envelope bounds U(l) by B χ(R)/l³.
The one-edge case of the lattice oscillation inequality gives increments
bounded by C U(l)/(D l). Multiplication by R³/χ(R) yields bounded values
and increments of order 1/R. Coordinate paths and a diagonal extraction
produce a common moving-site limit on every compact punctured annulus.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped CompactlySupported Topology

namespace IsingScaling.ModelPackets
open IsingRotation Packet SpatialEnvelope

private theorem cube_mass_mono {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    {k r : ℕ} (hkr : k ≤ r) : susceptibility g k ≤ susceptibility g r := by
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun z _ _ => hn z)
  intro z hz
  simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc] at hz ⊢
  intro j
  have := hz j
  omega

private theorem coordinate_neighborhood {g : Site → ℝ} {C : ℝ} {D r₀ : ℕ}
    (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1) (h0 : 0 < g 0)
    (hsym : ∀ z, g (-z) = g z) (hpos : StationaryPositive g)
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {x : Space} (hx : x ≠ 0) :
    ∃ (j : Fin 3) (t B C' : ℝ), 0<t ∧ 0≤C' ∧ ∀ᶠ n in atTop, ∀ z : Site,
      |(scaledSite (R n) z) j-x j| < t →
      ‖normalization g (R n)*g z‖ ≤ B ∧ ∀ i : Fin 3,
        dist (normalization g (R n)*g z)
          (normalization g (R n)*g (Function.update z i (z i+1))) ≤ C'/(R n:ℝ) := by
  obtain ⟨B,hB,henv⟩ := pointwise_envelope_of_stationary hn hb hsym hpos hC hD hosc
  obtain ⟨j,hj⟩ : ∃ j : Fin 3, x j ≠ 0 := by
    by_contra! h
    apply hx
    ext j
    exact h j
  let t := min (|x j|/2) 1
  let s := t/(4*(D:ℝ))
  have ht : 0 < t := lt_min (half_pos (abs_pos.mpr hj)) zero_lt_one
  have ht₁ : t ≤ 1 := min_le_right .. 
  have ht₂ : t ≤ |x j|/2 := min_le_left ..
  have hDp : 0 < D := by omega
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hs : 0 < s := div_pos ht (by positivity)
  have hsD : 4 * (D:ℝ) * s = t := by dsimp [s]; field_simp
  refine ⟨j,t,B/s^3,C*B/s^4,ht,by positivity,?_⟩
  let k₀ := max 40 r₀
  have hrr := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hR
  filter_upwards [hrr.eventually_ge_atTop (((k₀:ℝ)+1)/s),hR.eventually_ge_atTop 1] with n hbig hR₁
  intro z hz
  let r := R n
  have hr : 0 < (r:ℝ) := by exact_mod_cast (show 0<r by omega)
  let l := ⌊2*s*(r:ℝ)⌋₊
  have hlo : (k₀:ℝ)+1 ≤ s*(r:ℝ) := by
    exact ((div_le_iff₀ hs).mp hbig).trans_eq (mul_comm _ _)
  have hfk : (l:ℝ) ≤ 2*s*(r:ℝ) := Nat.floor_le (by positivity)
  have hlk : 2*s*(r:ℝ) < (l:ℝ)+1 := Nat.lt_floor_add_one _
  have hl : s*(r:ℝ) ≤ (l:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) k₀]
  have hl₀ : k₀ ≤ l := by exact_mod_cast (show (k₀:ℝ) ≤ l by linarith)
  have h40 : 40 ≤ l := (le_max_left ..).trans hl₀
  have hlp : 0 < (l:ℝ) := by exact_mod_cast (show 0<l by omega)
  have hDl : (D:ℝ)*(l:ℝ) ≤ t * (r:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hfk hDr.le
    nlinarith only [h,congrArg (fun x : ℝ => x*(r:ℝ)) hsD,
      mul_nonneg (mul_nonneg hDr.le hs.le) hr.le]
  have hll : l ≤ D*l := by
    simpa only [one_mul] using Nat.mul_le_mul_right l (show 1 ≤ D by omega)
  have hkr : l ≤ r := by
    have htR := mul_le_mul_of_nonneg_right ht₁ hr.le
    have hcast : (l:ℝ) ≤ (D:ℝ)*l := by exact_mod_cast hll
    exact_mod_cast (show (l:ℝ) ≤ r by linarith)
  have hχ : 0 < susceptibility g r := by
    have hχ' := Finset.single_le_sum (s:=cube r) (f:=g) (fun x _ => hn x)
      (show (0:Site) ∈ cube r by simp [cube,Fintype.mem_piFinset])
    change g 0 ≤ susceptibility g r at hχ'
    exact h0.trans_le hχ'
  have habs : |(scaledSite r z) j| = ((z j).natAbs:ℝ)/(r:ℝ) := by
    change |(z j:ℝ)/(r:ℝ)| = _
    simp only [Nat.cast_natAbs,Int.cast_abs,abs_div,abs_of_pos hr]
  have hfar : outside (D*l) z := by
    have hne := abs_sub_le (x j) ((scaledSite r z) j) 0
    simp only [sub_zero,abs_sub_comm (x j)] at hne
    have hh : t < |(scaledSite r z) j| := by linarith only [hne,hz,ht₂]
    rw [habs,lt_div_iff₀ hr] at hh
    exact ⟨j,by exact_mod_cast hDl.trans hh.le⟩
  have hfa : outside l z := by
    obtain ⟨i,hi⟩ := hfar
    exact ⟨i,hll.trans hi⟩
  have hTail : tail g l ≤ B*susceptibility g r/(l:ℝ)^3 := by
    apply tail_le (by positivity)
    intro u hu
    obtain ⟨i,hi⟩ := hu
    have H := henv (l:ℝ) (by exact_mod_cast (show 1≤l by omega)) u ⟨i,by exact_mod_cast hi⟩
    rw [Nat.floor_natCast] at H
    exact H.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cube_mass_mono hn hkr) hB.le) (by positivity))
  have hval := (le_tail hb hfa).trans hTail
  have hval' := (le_div_iff₀ (pow_pos hlp 3)).mp hval
  have hcube := pow_le_pow_left₀ (mul_nonneg hs.le hr.le) hl 3
  rw [mul_pow] at hcube
  constructor
  · change ‖(r:ℝ)^3/susceptibility g r*g z‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (div_nonneg (by positivity) hχ.le) (hn z))]
    field_simp [hχ.ne',hs.ne']
    nlinarith only [mul_le_mul_of_nonneg_right hcube (hn z),hval']
  · intro i
    let e : Site := Pi.single i 1
    let y := Function.update z i (z i+1)
    have he : e ∈ cube 1 := by
      simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc]
      intro a
      by_cases ha : a=i <;> simp [e,Pi.single_apply,ha,eq_comm]
    have hz' : z+e = y := by
      ext a
      by_cases ha : a=i <;> simp [e,y,Pi.single_apply,ha,eq_comm]
    have h₀ : r₀ ≤ D*l := (le_max_right 40 r₀).trans (hl₀.trans hll)
    have hosc' := hosc (D*l) h₀ (by positivity) z hfar 1 (by omega) e he
    rw [hz',Nat.mul_div_cancel_left _ hDp] at hosc'
    simp only [Nat.cast_one,mul_one,Nat.cast_mul] at hosc'
    rw [abs_sub_comm] at hosc'
    have hsmall : C/((D:ℝ)*l) ≤ C/l := div_le_div_of_nonneg_left hC hlp (by exact_mod_cast hll)
    have HD := hosc'.trans (mul_le_mul hsmall hTail (tail_nonneg hb _) (div_nonneg hC hlp.le))
    have HD' : |g z-g y| * (l:ℝ)^4 ≤ C*B*susceptibility g r := by
      field_simp [hlp.ne'] at HD
      linarith only [HD]
    have hpow := pow_le_pow_left₀ (mul_nonneg hs.le hr.le) hl 4
    rw [mul_pow] at hpow
    change dist ((r:ℝ)^3/susceptibility g r*g z) ((r:ℝ)^3/susceptibility g r*g y) ≤ _
    rw [Real.dist_eq,←mul_sub,abs_mul,abs_of_nonneg (div_nonneg (by positivity) hχ.le)]
    field_simp [hχ.ne',hs.ne',hr.ne']
    nlinarith only [mul_le_mul_of_nonneg_right hpow (abs_nonneg (g z-g y)),HD']

/-- Extraction uses the physical integer-radius oscillation inequality,
stationary positive definiteness and the same susceptibility at the original
scales. -/
theorem exists_spatial_limit_of_localOscillation {g : Site → ℝ} {C : ℝ} {D r₀ : ℕ}
    (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1) (h0 : 0 < g 0)
    (hsym : ∀ z, g (-z)=g z) (hpos : StationaryPositive g)
    (hC : 0≤C) (hD : 2≤D) (hosc : LocalOscillation g C D r₀)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ OffOriginLimit g (R ∘ u) f := by
  apply extract_of_coordinate_bounds hR
  · intro x hx
    obtain ⟨j,t,B,C',ht,_,h⟩ := coordinate_neighborhood hn hb h0 hsym hpos hC hD hosc hR hx
    have H := gridIndex_scaled_tendsto (v:=fun _ => x) hR tendsto_const_nhds
    have H' := (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.continuousAt.tendsto.comp H
    refine ⟨B,?_⟩
    filter_upwards [h,(Metric.tendsto_nhds.1 H') t ht] with n hn' hx'
    exact (hn' _ (by simpa [Real.dist_eq] using hx')).1
  · intro x hx
    obtain ⟨j,t,B,C',ht,hC',h⟩ := coordinate_neighborhood hn hb h0 hsym hpos hC hD hosc hR hx
    exact ⟨t,C',ht,hC',h.mono (fun _ hh z hz => (hh z (hz j)).2)⟩

#print axioms exists_spatial_limit_of_localOscillation

/-- The microscopic oscillation estimate and the positive lattice packets
imply orthogonal invariance for every locally finite vague limit. The
finite inward shift of the packet is retained up to the macroscopic limit. -/
theorem rotation_of_localOscillation {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ}
    (src : NormalizedPacketSource g R delay) (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1)
    (hpos : StationaryPositive g) {C : ℝ} {D r₀ : ℕ}
    (hC : 0≤C) (hD : 2≤D) (hosc : LocalOscillation g C D r₀)
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ))) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ OffOriginLimit g (R ∘ u) f ∧
      ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  have hsym (z : Site) : g (-z) = g z := src.cubic (Equiv.refl _) (fun _ => true) z
  have h0 : 0 < g 0 := by
    by_contra! h
    have hz (z : Site) : g z = 0 := le_antisymm ((le_origin_of_stationary hsym hpos z).trans h) (hn z)
    have H := src.cube_pos 0
    simp only [susceptibility,hz,Finset.sum_const_zero,lt_self_iff_false] at H
  obtain ⟨u,f,hu,hs⟩ := exists_spatial_limit_of_localOscillation hn hb h0 hsym hpos hC hD hosc hR
  let src' : NormalizedPacketSource g (R ∘ u) delay :=
    ⟨src.moments,src.cubic,fun j => src.cube_pos (u j)⟩
  exact ⟨u,f,hu,hs,fun O => rotation_of_spatial_limit src' hn (hR.comp hu.tendsto_atTop)
    (fun φ => (hv φ).comp hu.tendsto_atTop) hs O⟩

#print axioms rotation_of_localOscillation

end IsingScaling.ModelPackets
