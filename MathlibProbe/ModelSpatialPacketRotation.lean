import MathlibProbe.ReflectedLatticePacket
import MathlibProbe.IsingTwoPointSpatialAssembly
import MathlibProbe.IsingAnnularFourierBounds
import MathlibProbe.IsingAnnularCompactness

/-! # From lattice packets to rotation on the same sequence

Fix a scalar lattice function g, divergent integer scales R and their positive
cube susceptibilities. The lattice reflection form on the coordinate plane
and on the face-diagonal plane gives positive moment measures for packets
built from g. At positive macroscopic time the rounded packet displacements
stay off the origin. The spatial convergence along R therefore identifies
their limits after multiplying each coefficient by the square root of
R³/χ(R). Rescaling lattice eigenvalues gives one positive energy measure
for all positive times. Transverse quadrature and the exact lengths of the
two lattice normals identify its Fourier slice in an orthonormal frame.

For a locally finite vague limit μ of these same lattice measures, discrete
signed permutations pass to μ. The spatial annulus bounds give its punctured
Fourier density. Localizing the two actual packet slices and gluing the
angular continuations proves that μ is invariant under all real orthogonal
maps, including reflections. The proof keeps the atom at zero.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped CompactlySupported Topology NNReal ENNReal FourierTransform SchwartzMap
namespace IsingScaling.ModelPackets
open IsingRotation Packet FourierShell

/-- Package the two reflection forms of the actual scalar displacement kernel
with its cubic group action and the susceptibility used on this sequence. -/
theorem source_of_site_reflection {g : Site → ℝ} {R : ℕ → ℕ}
    (hb : ∀ z, |g z| ≤ 1) (hc : CubicKernel g)
    (hχ : ∀ n, 0 < susceptibility g (R n))
    (ha : SiteReflectedPositive g (fun v => v 0)
      (signedPerm (Equiv.refl _) (fun l => decide (l = 0))))
    (hd : SiteReflectedPositive g (fun v => v 0-v 1)
      (signedPerm (Equiv.swap 0 1) (fun _ => false))) :
    NormalizedPacketSource g R :=
  ⟨fun d {_} _ c x y => gridPacket_spectrum_of_site_reflection hb ha hd d c x y, hc, hχ⟩

private theorem cubic_at_scale {g : Site → ℝ} (hc : CubicKernel g)
    (R : ℕ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    (twoPointMeasure g R).map (cubicMotion p s) = twoPointMeasure g R := by
  classical
  let T := cubicMotion p s
  unfold twoPointMeasure
  rw [Measure.map_sum T.continuous.measurable.aemeasurable]
  ext B hB
  simp only [Measure.sum_apply _ hB, Measure.map_smul,
    Measure.map_dirac' T.continuous.measurable]
  let b (x : Site) := (ENNReal.ofReal (g x / susceptibility g R) •
    Measure.dirac (scaledSite R x)) B
  calc
    _ = ∑' x, b (signedPerm p s x) := by
      apply tsum_congr
      intro x
      change (ENNReal.ofReal (g x / susceptibility g R) •
        Measure.dirac (T (scaledSite R x))) B =
        (ENNReal.ofReal (g (signedPerm p s x) / susceptibility g R) •
          Measure.dirac (scaledSite R (signedPerm p s x))) B
      rw [cubicMotion_scaledSite, hc p s]
    _ = _ := Equiv.tsum_eq (signedPerm p s) b

/-- Only the finite cubic group is transported across vague convergence. -/
theorem cubic_of_vague_limit {g : Site → ℝ} (hc : CubicKernel g)
    {R : ℕ → ℕ} {μ : Measure Space} [μ.Regular]
    (hv : ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ))) : CubicMeasureInvariant μ := by
  intro p s
  let T := (cubicMotion p s).toHomeomorph
  have : (μ.map T).Regular := Measure.Regular.map T
  change μ.map T = μ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fT := f.comp T.toCocompactMap
  have hc' (ν : Measure Space) : ∫ x, f x ∂ν.map T = ∫ x, fT x ∂ν :=
    integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable
  rw [hc']
  apply tendsto_nhds_unique (hv fT)
  have heq (j : ℕ) : ∫ x, fT x ∂twoPointMeasure g (R j) =
      ∫ x, f x ∂twoPointMeasure g (R j) := by
    rw [← hc']
    exact congrArg (fun m : Measure Space => ∫ x, f x ∂m) (cubic_at_scale hc (R j) p s)
  simpa only [heq] using hv f

private theorem spatial_even {g : Site → ℝ} (hc : CubicKernel g) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {f : Space → ℝ} (hsp : OffOriginLimit g R f) (x : Space) :
    f (-x) = f x := by
  by_cases hx : x = 0
  · simp [hx]
  let q (n : ℕ) := gridIndex (R n) x
  have hq : Tendsto (fun n => scaledSite (R n) (q n)) atTop (𝓝 x) :=
    gridIndex_scaled_tendsto hR tendsto_const_nhds
  have hneg (r : ℕ) (a : Site) : scaledSite r (-a) = -scaledSite r a := by
    ext i
    change (((-(a i):ℤ):ℝ)/(r:ℝ)) = -((a i:ℝ)/(r:ℝ))
    simp only [Int.cast_neg,neg_div]
  have hgn (a : Site) : g (-a) = g a := hc (Equiv.refl _) (fun _ => true) a
  have hq' := hsp (-x) (neg_ne_zero.mpr hx) (fun n => -q n) (by simpa only [hneg] using hq.neg)
  exact tendsto_nhds_unique (by simpa only [hgn] using hq') (hsp x hx q hq)

/-- Transverse displacements in the positive time half-space are bounded by
the one-site packet at any earlier positive time. Both sides use the one
spatial profile, including when its normalization vanishes off the origin. -/
private theorem coordinate_packet_majorant {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) (x y : ℝ) :
    |f (xyz (2*t) x y)| ≤ f (xyz (2*a) 0 0) := by
  have htp := ha.trans_le ht
  have hf := hsp.continuousOn hR
  have quad (b : ℝ) : 0 ≤ (1+b*b)*f (xyz (2*t) 0 0)+(2*b)*f (xyz (2*t) x y) := by
    let c : Fin 2 → ℝ := ![1,b]
    let X : Fin 2 → ℝ := ![x,0]
    let Y : Fin 2 → ℝ := ![y,0]
    obtain ⟨ρ,H⟩ := finiteTimePacket_laplace_of_moments src.moments src.cube_pos
      hR hf hsp false c X Y
    have hnon : 0 ≤ ∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ :=
      integral_nonneg (fun E => (Real.exp_pos (-t*(E:ℝ))).le)
    have hn : 0 ≤ finiteTimePacket f false c X Y t := (H t htp).2 ▸ hnon
    have hswap := packet_transverse_swap_of_cubic src.cubic hR hsp false htp x 0 y 0
    simp only [sub_zero,zero_sub] at hswap
    simp only [finiteTimePacket,Fin.sum_univ_two,c,X,Y,Matrix.cons_val_zero,Matrix.cons_val_one,
      sub_self,sub_zero,zero_sub,one_mul,mul_one] at hn
    rw [← hswap] at hn
    change 0 ≤ f (xyz (2*t) 0 0) + b * f (xyz (2*t) x y) +
      (b * f (xyz (2*t) x y) + b * b * f (xyz (2*t) 0 0)) at hn
    linarith only [hn]
  have hbounded : |f (xyz (2*t) x y)| ≤ f (xyz (2*t) 0 0) :=
    abs_le.mpr ⟨by linarith [quad 1], by linarith [quad (-1)]⟩
  obtain ⟨ρ,H'⟩ := finiteTimePacket_laplace_of_moments src.moments src.cube_pos
    hR hf hsp false (fun _ : Unit => (1:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
  have H (u : ℝ) (hu : 0 < u) : Integrable (fun E : ℝ≥0 => Real.exp (-u*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-u*(E:ℝ)) ∂ρ) = f (xyz (2*u) 0 0) := by
    simpa [finiteTimePacket,packetVector] using H' u hu
  refine hbounded.trans ?_
  rw [← (H t htp).2, ← (H a ha).2]
  exact integral_mono (H t htp).1 (H a ha).1 (fun E =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ht) E.2))

/-- Once the off-origin profile is realized, positive normal-time packets
already give its uniform bounds on the full complement of every ball. -/
theorem boundedAwayFromOrigin_of_source {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) : BoundedAwayFromOrigin f := by
  intro ε hε
  refine ⟨f (xyz (2*(ε/6)) 0 0), fun x hx => ?_⟩
  have hi : ∃ i, ε/3 ≤ |x i| := by
    by_contra! hh
    have hsq (i : Fin 3) : (x i)^2 < (ε/3)^2 := sq_lt_sq.mpr
      (by simpa only [abs_of_pos (by positivity : 0<ε/3)] using hh i)
    have hnorm := EuclideanSpace.real_norm_sq_eq x
    rw [Fin.sum_univ_three] at hnorm
    have he := pow_le_pow_left₀ hε.le hx 2
    nlinarith only [he,hnorm,hsq 0,hsq 1,hsq 2,sq_pos_of_pos hε]
  obtain ⟨i,hi⟩ := hi
  let p : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  let s := fun _: Fin 3 => decide (x i < 0)
  let T := cubicMotion p s
  let w := T x
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hε.trans_le hx)
  have hq := gridIndex_scaled_tendsto (v := fun _ => x) hR tendsto_const_nhds
  let q (n : ℕ) := gridIndex (R n) x
  have hq' : Tendsto (fun n => scaledSite (R n) (signedPerm p s (q n))) atTop (𝓝 w) := by
    simpa only [Function.comp_def,w,T,cubicMotion_scaledSite,q] using
      T.continuous.continuousAt.tendsto.comp hq
  have hw0 : w ≠ 0 := fun h => hx0 (T.injective (h.trans T.map_zero.symm))
  have heq : f w = f x := by
    apply tendsto_nhds_unique (hsp w hw0 _ hq')
    simpa only [src.cubic p s] using hsp x hx0 q hq
  have hfirst : w 0 = |x i| := by
    change (if decide (x i < 0) then -(x (p 0)) else x (p 0)) = |x i|
    rw [show p 0 = i from Equiv.swap_apply_left _ _]
    by_cases hn : x i < 0
    · simp [hn,abs_of_neg hn]
    · simp [hn,abs_of_nonneg (le_of_not_gt hn)]
  have hrepr : w = xyz (2*(w 0/2)) (w 1) (w 2) := by
    ext j
    fin_cases j
    · change w 0 = 2*(w 0/2)
      ring
    · rfl
    · rfl
  rw [Real.norm_eq_abs,← heq]
  conv_lhs => rw [hrepr]
  exact coordinate_packet_majorant src hR hsp (by positivity) (by linarith [hfirst,hi]) _ _

/-- Every input refers to the same lattice function, scaling sequence and
spatial profile. The two estimates on its concrete large spatial shells
give the Fourier density. The normal packet spectra in the continuum
are consequences. The off-origin representative may take any value at zero. -/
theorem rotation_of_volume_shells {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : NormalizedPacketSource g R delay) (hn : ∀ x, 0 ≤ g x)
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ)))
    {f : Space → ℝ} (hsp : OffOriginLimit g R f) (hB : BoundedAwayFromOrigin f)
    {A : ℝ} (hsh : VolumeShellBounds (fun j x => (spatialShell f j x : ℂ)) A)
    (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  let F (x : Space) := max (f x) 0
  have hF (x : Space) (hx : x ≠ 0) : F x = f x := by
    apply max_eq_left
    apply ge_of_tendsto' (hsp x hx _ (gridIndex_scaled_tendsto (v := fun _ => x) hR tendsto_const_nhds))
    exact fun n => mul_nonneg (div_nonneg (by positivity) (src.cube_pos n).le) (hn _)
  have hnF (x : Space) : 0 ≤ F x := le_max_right _ _
  have hspF : OffOriginLimit g R F := fun x hx q hq => hF x hx ▸ hsp x hx q hq
  have hBF : BoundedAwayFromOrigin F := by
    intro ε hε
    obtain ⟨B,h⟩ := hB ε hε
    exact ⟨B,fun x hx => (hF x (norm_pos_iff.mp (hε.trans_le hx))) ▸ h x hx⟩
  have hsc (j : ℕ) (x : Space) : spatialShell F j x = spatialShell f j x := by
    by_cases hx : x = 0
    · simp [hx,spatialShell,spatialShellMother]
    · simp only [spatialShell,hF x hx]
  have hsF : VolumeShellBounds (fun j x => (spatialShell F j x : ℂ)) A := by
    simpa only [hsc] using hsh
  have hf := hspF.continuousOn hR
  have hL := offOrigin_locallyIntegrable hn hR src.cube_pos hf hspF
  have hμ := tangent_eq_contact_add_density hn hR src.cube_pos hspF hv
  have hp := spatialShell_test_partition hL hBF (measurable_of_continuousOn_compl_singleton 0 hf)
    hnF hμ
  have he := spatial_even src.cubic hR hspF
  obtain ⟨C,hFourier,hcont,hbound⟩ := exists_puncturedFourierDensity_of_volume_shells μ
    (μ {0}).toReal (spatialShellInner F) (spatialShell F) (spatialShellInner_integrable hL)
    (spatialShellInner_even he) hsF (spatialShell_even he) (fun ψ => (hp ψ).2)
  let c := (μ {0}).toNNReal
  have hce : (c:ℝ≥0∞) = μ {0} := ENNReal.coe_toNNReal measure_singleton_lt_top.ne
  rw [← hce] at hμ
  have hspec : HasPhysicalPacketProfiles C :=
    physical_spectralSlice_profile_of_source src hR hf hspF hL hBF hnF c hμ hFourier hcont hbound
  obtain ⟨hmap,hd⟩ := rotation_of_cubic_punctured_physical_profiles (cubic_of_vague_limit src.cubic hv)
    hFourier hcont hbound (fun ψ => (hp ψ).1) hspec O
  refine ⟨hmap,fun x hx => ?_⟩
  have hOF := (ENNReal.ofReal_eq_ofReal_iff (hnF _) (hnF _)).1
    (hd c (by simp) _ (measurable_of_continuousOn_compl_singleton 0 hf).ennreal_ofReal
      (ENNReal.continuous_ofReal.comp_continuousOn hf) hμ x hx)
  simpa only [hF x hx,hF (O x) ((map_ne_zero_iff O O.injective).2 hx)] using hOF

#print axioms source_of_site_reflection
#print axioms rotation_of_volume_shells

/-- Every moving-site spatial limit of the same susceptibility-normalized
lattice kernel is orthogonally invariant, including its contact measure.
Both the size and the Fourier estimates for its expanding annuli follow
from the two reflected lattice packets. -/
theorem rotation_of_spatial_limit {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : NormalizedPacketSource g R delay) (hn : ∀ x, 0 ≤ g x)
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ)))
    {f : Space → ℝ} (hsp : OffOriginLimit g R f) (O : Space ≃ₗᵢ[ℝ] Space) :
    μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  have hB := boundedAwayFromOrigin_of_source src hR hsp
  obtain ⟨A,hsh⟩ := hsp.exists_volume_shell_bounds_of_source src hR (hsp.continuousOn hR) hB
  exact rotation_of_volume_shells src hn hR hv hsp hB hsh O

/-- Lattice estimates at rounded sites and in their neighborhoods suffice
for every given vague limit. One subsequence and its spatial profile work
for all orthogonal transformations. -/
theorem rotation_of_site_oscillation {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : NormalizedPacketSource g R delay) (hn : ∀ x, 0 ≤ g x)
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ v, φ v ∂twoPointMeasure g (R n))
      atTop (𝓝 (∫ v, φ v ∂μ)))
    (hval : ∀ x : Space, x ≠ 0 → ∃ B : ℝ, ∀ᶠ n in atTop,
      ‖normalization g (R n)*g (gridIndex (R n) x)‖ ≤ B)
    (hosc : ∀ x : Space, x ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ k l : Site, dist (scaledSite (R n) k) x < δ → dist (scaledSite (R n) l) x < δ →
      dist (normalization g (R n)*g k) (normalization g (R n)*g l) < ε) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ OffOriginLimit g (R ∘ u) f ∧
      ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ ∧ ∀ x ≠ 0, f (O x) = f x := by
  obtain ⟨u,f,hu,hs⟩ := extract_of_site_oscillation hR hval hosc
  let src' : NormalizedPacketSource g (R ∘ u) delay :=
    ⟨src.moments,src.cubic,fun j => src.cube_pos (u j)⟩
  exact ⟨u,f,hu,hs,fun O => rotation_of_spatial_limit src' hn (hR.comp hu.tendsto_atTop)
    (fun φ => (hv φ).comp hu.tendsto_atTop) hs O⟩

#print axioms rotation_of_spatial_limit
#print axioms rotation_of_site_oscillation

end IsingScaling.ModelPackets
