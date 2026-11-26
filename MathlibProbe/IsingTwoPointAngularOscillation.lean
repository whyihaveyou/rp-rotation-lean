import MathlibProbe.IsingTwoPointRotation
import MathlibProbe.IsingTangentExistence
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Angular oscillation of the original, susceptibility-normalized lattice
two-point function along moving sites. The subsequences used to prove
convergence of the difference may have different radial profiles. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology CompactlySupported ENNReal
namespace IsingScaling
open Packet IsingRotation

private theorem angular_difference_of_extraction {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β)
    (extract : ∀ {r : ℕ → ℕ}, Tendsto r atTop atTop →
      ∃ (u : ℕ → ℕ) (μ : Measure Space) (f : Space → ℝ),
        StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ OffOriginLimit g (r ∘ u) f ∧
        ∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (r (u n)))
          atTop (𝓝 (∫ x, φ x ∂μ)))
    (rot : ∀ {μ : Measure Space} [IsLocallyFiniteMeasure μ], IsTwoPointTangent β μ →
        ∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0) := by
  obtain ⟨hn,hχ⟩ := hg.positive_cube_mass hβ
  apply tendsto_of_subseq_tendsto
  intro a ha
  obtain ⟨b,μ,f,hb,hfin,hsp,hm⟩ := extract (hR.comp ha)
  let := hfin
  have htR := (hR.comp ha).comp hb.tendsto_atTop
  have ht : IsTwoPointTangent β μ :=
    ⟨g,(R ∘ a) ∘ b,hg,hn,fun n => hχ _,htR,hm⟩
  have hden := tangent_eq_contact_add_density hn htR (fun _ => hχ _) hsp hm
  have hf := hsp.continuousOn htR
  have hline := spatialDensity_invariant_of_map_eq μ (μ {0}) measure_singleton_lt_top.ne
    (fun v => ENNReal.ofReal (f v)) (measurable_of_continuousOn_compl_singleton 0 hf).ennreal_ofReal
    (ENNReal.continuous_ofReal.comp_continuousOn hf) hden O (rot ht O) x hx
  have hOx := (map_ne_zero_iff O O.injective).2 hx
  have hfx : f (O x) = f x := (ENNReal.ofReal_eq_ofReal_iff
    (hsp.nonneg_of_free hg hβ htR (O x) hOx) (hsp.nonneg_of_free hg hβ htR x hx)).1 hline
  have hk' := hsp x hx _ ((hk.comp ha).comp hb.tendsto_atTop)
  have hl' := hsp (O x) hOx _ ((hl.comp ha).comp hb.tendsto_atTop)
  refine ⟨b,?_⟩
  simpa only [Function.comp_apply,mul_sub,hfx,sub_self] using hk'.sub hl'

/-- Direct full-sequence lattice statement, allowing independent rounding of
the two displacements. Their common macroscopic radius is positive. -/
theorem IsFreeTwoPoint.angular_oscillation {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (O : Space ≃ₗᵢ[ℝ] Space) {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0) :=
  angular_difference_of_extraction hg hβ (fun hr => extract_physical_tangent hg hβ hr)
    (fun ht O => ht.rotation_invariant hβ O) hR O hx hk hl

/-- For the canonical free-boundary infinite-volume Ising correlation the
only inputs are ferromagnetism, diverging scales and the site geometry. -/
theorem thermodynamicTwoPoint_angular_oscillation {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => ((R n:ℝ)^3 / susceptibility (thermodynamicTwoPoint β) (R n)) *
      (thermodynamicTwoPoint β (k n) - thermodynamicTwoPoint β (l n))) atTop (𝓝 0) :=
  (thermodynamicTwoPoint_isLimit hβ).angular_oscillation hβ hR O hx hk hl

#print axioms thermodynamicTwoPoint_angular_oscillation

/-- A formulation entirely in finite free-box spin observables. At each
macroscopic scale the same box is used for both spin pairs and for the
susceptibility. Its threshold may depend on the scale and on all four sites. -/
theorem freePair_angular_oscillation_iterated {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {a b c d : ℕ → Site}
    (hab : Tendsto (fun n => scaledSite (R n) (a n - b n)) atTop (𝓝 x))
    (hcd : Tendsto (fun n => scaledSite (R n) (c n - d n)) atTop (𝓝 (O x))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ L : ℕ in atTop,
      |(R n : ℝ)^3 / susceptibility (freeTwoPoint β L) (R n) *
        (freePair β L (a n) (b n) - freePair β L (c n) (d n))| < ε := by
  intro ε hε
  have hrot := thermodynamicTwoPoint_angular_oscillation hβ hR O hx hab hcd
  filter_upwards [hrot.abs.eventually_lt_const (by simpa using hε)] with n hn
  have hg := thermodynamicTwoPoint_isLimit hβ
  have hp := thermodynamicTwoPoint_stationary hβ
  have hχ : Tendsto (fun L => susceptibility (freeTwoPoint β L) (R n)) atTop
      (𝓝 (susceptibility (thermodynamicTwoPoint β) (R n))) :=
    tendsto_finsetSum _ fun i _ => hg i
  have hnorm := (tendsto_const_nhds (x := (R n : ℝ)^3)).div hχ
    ((hg.positive_cube_mass hβ).2 (R n)).ne'
  exact (hnorm.mul ((hp (a n) (b n)).sub (hp (c n) (d n)))).abs.eventually_lt_const hn

#print axioms freePair_angular_oscillation_iterated

/-- Uniform angular interpretation on any compact annulus. The two lattice
directions can move independently and need not have limits. -/
theorem IsFreeTwoPoint.annular_angular_oscillation {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {k l : ℕ → Site} {a D : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ D)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ D)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0) := by
  let K := Metric.closedBall (0:Space) D
  let V (n : ℕ) := (scaledSite (R n) (k n),scaledSite (R n) (l n))
  have hm (n : ℕ) : V n ∈ K ×ˢ K := by
    simpa only [Set.mem_prod,V,K,Metric.mem_closedBall,dist_zero_right] using And.intro (hk n).2 (hl n)
  apply tendsto_of_subseq_tendsto
  intro u hu
  obtain ⟨⟨x,y⟩,_,v,hv,hxy⟩ := ((isCompact_closedBall (0:Space) D).prod
    (isCompact_closedBall (0:Space) D)).tendsto_subseq (x:=V ∘ u) (fun n => hm _)
  have hseq := hu.comp hv.tendsto_atTop
  have hx := (continuous_fst.tendsto (x,y)).comp hxy
  have hy := (continuous_snd.tendsto (x,y)).comp hxy
  have hxpos : a ≤ ‖x‖ := ge_of_tendsto' hx.norm (fun n => (hk _).1)
  have hne : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hxpos)
  have he : ‖x‖ = ‖y‖ := sub_eq_zero.mp (tendsto_nhds_unique (hx.norm.sub hy.norm) (hrad.comp hseq))
  let O := (Submodule.span ℝ ({x-y} : Set Space))ᗮ.reflection
  have hO : O x = y := Submodule.reflection_sub he
  refine ⟨v, hg.angular_oscillation hβ (hR.comp hseq) O hne hx ?_⟩
  rw [hO]
  exact hy

#print axioms IsFreeTwoPoint.annular_angular_oscillation

/-- Euclidean radius in lattice units, before any scale normalization. -/
def siteRadius (x : Site) : ℝ := ‖scaledSite 1 x‖

/-- The axis site at the integer part of the Euclidean lattice radius. -/
def radialAxisSite (x : Site) : Site := Pi.single 0 ⌊siteRadius x⌋

theorem scaledSite_norm_radius (r : ℕ) (x : Site) :
    ‖scaledSite r x‖ = siteRadius x / r := by
  have he : scaledSite r x = (r:ℝ)⁻¹ • scaledSite 1 x := by
    ext i
    change (x i:ℝ)/r = (r:ℝ)⁻¹ * ((x i:ℝ)/(1:ℕ))
    simp [div_eq_inv_mul]
  rw [he,norm_smul,Real.norm_of_nonneg (by positivity),div_eq_inv_mul]
  rfl

theorem radius_axis (x : Site) : siteRadius (radialAxisSite x) = (⌊siteRadius x⌋:ℤ) := by
  have he : scaledSite 1 (radialAxisSite x) =
      PiLp.single 2 (0:Fin 3) ((⌊siteRadius x⌋:ℤ):ℝ) := by
    ext i
    by_cases hi : i=0
    · subst i; simp [scaledSite,radialAxisSite]
    · simp [scaledSite,radialAxisSite,hi]
  rw [siteRadius,he,PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg]
  exact_mod_cast Int.floor_nonneg.mpr (norm_nonneg _)

private theorem siteRadius_cube {r : ℕ} {x : Site} (hx : x ∈ cube r) :
    siteRadius x ≤ 2*r := by
  have hs (i : Fin 3) : |scaledSite 1 x i| ≤ r := by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hx) i)
    change |(x i:ℝ)/(1:ℕ)| ≤ r
    simp only [Nat.cast_one,div_one,abs_le]
    exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
  have hs' (i : Fin 3) : (scaledSite 1 x i)^2 ≤ (r:ℝ)^2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg (Nat.cast_nonneg r : (0:ℝ)≤r)] using hs i
  have hsq := EuclideanSpace.real_norm_sq_eq (scaledSite 1 x)
  rw [Fin.sum_univ_three] at hsq
  unfold siteRadius
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith only [hsq,hs' 0,hs' 1,hs' 2,sq_nonneg (r:ℝ)]

theorem siteRadius_outside {r : ℕ} {x : Site} (hx : x ∉ cube r) :
    (r:ℝ) ≤ siteRadius x := by
  apply le_of_not_gt
  intro hh
  apply hx
  apply Fintype.mem_piFinset.mpr
  intro i
  have hc := (PiLp.norm_apply_le (scaledSite 1 x) i).trans hh.le
  change |(x i:ℝ)/(1:ℕ)| ≤ r at hc
  simp only [Nat.cast_one,div_one,abs_le] at hc
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hc.1,by exact_mod_cast hc.2⟩

private theorem rounded_uniform_on_shell {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) (rep : Site → Site) {b : ℝ}
    (hrep : ∀ x, 0 ≤ siteRadius x - siteRadius (rep x) ∧ siteRadius x - siteRadius (rep x) ≤ b)
    (s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x ∈ cube (s*r) \ cube r,
      |normalization g r * (g x - g (rep x))| < ε := by
  classical
  by_contra h
  obtain ⟨u,hu,hbad⟩ := exists_seq_forall_of_frequently (p := fun r : ℕ =>
    ¬ ∀ x ∈ cube (s*r) \ cube r, |normalization g r * (g x - g (rep x))| < ε)
      (l:=atTop) (by simpa only [Filter.Frequently,not_not] using h)
  have hb (n : ℕ) := hbad n
  push Not at hb
  choose k hmem herr using hb
  have hpos (n : ℕ) : 0 < u n := by
    by_contra! hh
    have hz : u n = 0 := by omega
    simpa [hz] using hmem n
  have hp (n : ℕ) : 0 < (u n:ℝ) := by exact_mod_cast hpos n
  have hgeom (n : ℕ) : 1 ≤ ‖scaledSite (u n) (k n)‖ ∧
      ‖scaledSite (u n) (k n)‖ ≤ 2*s := by
    rw [scaledSite_norm_radius]
    obtain ⟨hi,ho⟩ := Finset.mem_sdiff.mp (hmem n)
    exact ⟨(one_le_div (hp n)).2 (siteRadius_outside ho),
      (div_le_iff₀ (hp n)).2 (by simpa [Nat.cast_mul,mul_assoc] using siteRadius_cube hi)⟩
  have hdiff (n : ℕ) : 0 ≤ ‖scaledSite (u n) (k n)‖ -
      ‖scaledSite (u n) (rep (k n))‖ ∧
      ‖scaledSite (u n) (k n)‖ - ‖scaledSite (u n) (rep (k n))‖ ≤ b/(u n:ℝ) := by
    rw [scaledSite_norm_radius,scaledSite_norm_radius,←sub_div]
    exact ⟨div_nonneg (hrep _).1 (hp n).le,
      (div_le_div_iff_of_pos_right (hp n)).2 (hrep _).2⟩
  have ht := hg.annular_angular_oscillation hβ hu (k:=k) (l:=rep ∘ k)
    (show (0:ℝ)<1 by norm_num) hgeom
    (fun n => (sub_nonneg.mp (hdiff n).1).trans (hgeom n).2)
    (squeeze_zero (fun n => (hdiff n).1) (fun n => (hdiff n).2)
      (by simpa only [Function.comp_apply,mul_zero, mul_one_div] using
        (tendsto_one_div_atTop_nhds_zero_nat.comp hu).const_mul b))
  have ht' : ∀ᶠ n : ℕ in atTop, |normalization g (u n) * (g (k n)-g (rep (k n)))| < ε :=
    ht.abs.eventually_lt_const (by simpa using hε)
  obtain ⟨n,hn⟩ := ht'.exists
  exact (not_lt_of_ge (herr n)) hn

theorem shell_card_bound (s r : ℕ) (hr : 0 < r) :
    ((cube (s*r) \ cube r).card:ℝ) ≤ (2*(s:ℝ)+1)^3*(r:ℝ)^3 := by
  have h : (cube (s*r) \ cube r).card ≤ (cube (s*r)).card :=
    Finset.card_le_card Finset.sdiff_subset
  have hc (n : ℕ) : (cube n).card = (2*n+1)^3 := by
    rw [cube,Fintype.card_piFinset_const,Int.card_Icc]
    have : ((n:ℤ)+1 - (-(n:ℤ))).toNat = 2*n+1 := by omega
    rw [this]
  rw [hc] at h
  apply (Nat.cast_le.mpr h : ((cube (s*r) \ cube r).card:ℝ) ≤ _).trans
  push_cast
  rw [←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hh : (1:ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

private theorem susceptibility_shell_rounded {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) (rep : Site → Site) {b : ℝ}
    (hrep : ∀ x, 0 ≤ siteRadius x - siteRadius (rep x) ∧ siteRadius x - siteRadius (rep x) ≤ b)
    (s : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun r : ℕ =>
      |susceptibility g (s*r) - susceptibility g r -
        ∑ x ∈ cube (s*r) \ cube r, g (rep x)| / susceptibility g r) atTop (𝓝 0) := by
  classical
  let K := (2*(s:ℝ)+1)^3
  have hK : 0 < K := by unfold K; positivity
  obtain ⟨_,gχ⟩ := hg.positive_cube_mass hβ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e := ε/(2*K)
  have he : 0 < e := by unfold e; positivity
  filter_upwards [rounded_uniform_on_shell hg hβ rep hrep s he, eventually_ge_atTop 1] with r hh hr
  let S := cube (s*r) \ cube r
  let d (x : Site) := g x-g (rep x)
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hχ := gχ r
  have hr3 := pow_pos hr' 3
  have hsub : cube r ⊆ cube (s*r) := by
    have hsr : r ≤ s*r := Nat.le_mul_of_pos_left _ hs
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hx) i)
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hsum : ∑ x ∈ S, d x = susceptibility g (s*r)-susceptibility g r -
      ∑ x ∈ S, g (rep x) := by
    simp only [S,d, Finset.sum_sub_distrib, Finset.sum_sdiff_eq_sub hsub,susceptibility]
    abel
  have hsumBound : |∑ x ∈ S, normalization g r * d x| ≤ ((r:ℝ)^3*K)*e := by
    calc _ ≤ ∑ x ∈ S, |normalization g r * d x| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _x ∈ S, e := Finset.sum_le_sum (fun x hx => (hh x hx).le)
         _ = (S.card:ℝ)*e := by simp
         _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa [S,K,mul_comm] using shell_card_bound s r hr) he.le
  have hN : 0 ≤ normalization g r := div_nonneg hr3.le hχ.le
  rw [← Finset.mul_sum,abs_mul,abs_of_nonneg hN] at hsumBound
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (abs_nonneg _) hχ.le),←hsum]
  have hscaled : (1/(r:ℝ)^3) * (normalization g r * |∑ x ∈ S, d x|) =
      |∑ x ∈ S, d x| / susceptibility g r := by
    unfold normalization; field_simp
  rw [←hscaled]
  refine (mul_le_mul_of_nonneg_left hsumBound (by positivity : 0≤1/(r:ℝ)^3)).trans_lt ?_
  dsimp only [e]; field_simp; linarith

/-- Susceptibility in a fixed-ratio cubic annulus can be read entirely
from the axial correlation at the floored Euclidean radius. -/
theorem IsFreeTwoPoint.susceptibility_shell_radial_axis {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) (s : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun r : ℕ =>
      |susceptibility g (s*r) - susceptibility g r -
        ∑ x ∈ cube (s*r) \ cube r, g (radialAxisSite x)| / susceptibility g r) atTop (𝓝 0) := by
  apply susceptibility_shell_rounded hg hβ radialAxisSite (b:=1) _ s hs
  intro x
  rw [radius_axis]
  exact ⟨sub_nonneg.mpr (Int.floor_le _), by linarith [Int.lt_floor_add_one (siteRadius x)]⟩

#print axioms IsFreeTwoPoint.susceptibility_shell_radial_axis

/-- Index on the even axial lattice on which the physical one-site packet
has an established Hausdorff representation. -/
def evenRadialIndex (x : Site) : ℕ := ⌊siteRadius x/2⌋₊

def evenRadialSite (x : Site) : Site := Pi.single 0 (2*evenRadialIndex x:ℕ)

/-- A finite polynomial with nonnegative integer coefficients, defined also
at the spectral endpoints. A zero exponent contributes one at t=0. -/
def evenShellKernel (s r : ℕ) (t : Packet.UnitInterval) : ℝ :=
  ∑ x ∈ cube (s*r) \ cube r, (t:ℝ)^evenRadialIndex x

theorem evenShellKernel_nonneg (s r : ℕ) (t : Packet.UnitInterval) :
    0 ≤ evenShellKernel s r t :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg t.property.1 _)

private theorem even_radius_error (x : Site) :
    0 ≤ siteRadius x-siteRadius (evenRadialSite x) ∧
    siteRadius x-siteRadius (evenRadialSite x) ≤ 2 := by
  let k := evenRadialIndex x
  have he : scaledSite 1 (evenRadialSite x) = PiLp.single 2 (0:Fin 3) (2*(k:ℝ)) := by
    ext i
    by_cases h : i=0
    · subst i; simp [scaledSite,evenRadialSite,k]
    · simp [scaledSite,evenRadialSite,h]
  have hrad : siteRadius (evenRadialSite x) = 2*(k:ℝ) := by
    rw [siteRadius,he,PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h0 : 0 ≤ siteRadius x/2 := div_nonneg (norm_nonneg _) (by norm_num)
  have hlow : (k:ℝ) ≤ siteRadius x/2 := Nat.floor_le h0
  have hhigh : siteRadius x/2 < (k:ℝ)+1 := Nat.lt_floor_add_one _
  rw [hrad]; constructor <;> linarith

private theorem actual_even_axial_law {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, IsProbabilityMeasure (μ : Measure Packet.UnitInterval) ∧
      ∀ n : ℕ, g (Pi.single 0 (2*n:ℕ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval) := by
  obtain ⟨μ,hμ⟩ := Packet.axis_evenPacket_spectrum (hg.stationary_pair_limit hβ)
    (fun _ : Unit => (1:ℝ)) (fun _ => 0) (fun _ => 0)
  have H (n : ℕ) : g (Pi.single 0 (2*n:ℕ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval) := by
    have he : (![((2*n:ℕ):ℤ),0,0] : Site) = Pi.single 0 (2*n:ℕ) := by
      ext i
      fin_cases i <;> simp
    simpa only [evenPacket,Fintype.sum_unique,sub_self,one_mul,he] using (hμ n).symm
  have hg0 : g 0 = 1 := tendsto_nhds_unique (hg 0)
    (by simp only [freeTwoPoint_zero]; exact tendsto_const_nhds)
  have hmass : 1 = ((μ:Measure Packet.UnitInterval) Set.univ).toReal := by
    simpa [hg0, measureReal_def] using H 0
  refine ⟨μ,⟨?_⟩,H⟩
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    congrArg ENNReal.ofReal hmass.symm

/-- A single probability measure of the thermodynamic Ising correlation
represents every even-rounded axial shell exactly. Its positive polynomials
then read the original all-scale susceptibility increments up to o(χ_R). -/
theorem IsFreeTwoPoint.susceptibility_evenShell_spectrum {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, IsProbabilityMeasure (μ : Measure Packet.UnitInterval) ∧
      (∀ n : ℕ, g (Pi.single 0 (2*n:ℕ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval)) ∧
      (∀ s r : ℕ, (∑ x ∈ cube (s*r) \ cube r, g (evenRadialSite x)) =
        ∫ t, evenShellKernel s r t ∂(μ:Measure Packet.UnitInterval)) ∧
      ∀ s : ℕ, 1 ≤ s → Tendsto (fun r : ℕ => susceptibility g (s*r) / susceptibility g r -
        (1 + (∫ t, evenShellKernel s r t ∂(μ:Measure Packet.UnitInterval)) / susceptibility g r))
        atTop (𝓝 0) := by
  obtain ⟨μ,hprob,hm⟩ := actual_even_axial_law hg hβ
  have hsum (s r : ℕ) : (∑ x ∈ cube (s*r) \ cube r, g (evenRadialSite x)) =
      ∫ t, evenShellKernel s r t ∂(μ:Measure Packet.UnitInterval) := by
    unfold evenShellKernel
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun x _ => hm (evenRadialIndex x))
    · intro x _
      exact (continuous_subtype_val.pow (evenRadialIndex x)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine ⟨μ,hprob,hm,hsum,?_⟩
  intro s hs
  have hh := susceptibility_shell_rounded hg hβ evenRadialSite even_radius_error s hs
  have hpos := (hg.positive_cube_mass hβ).2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hh.congr
  intro r
  rw [hsum,Real.norm_eq_abs,←abs_of_pos (hpos r),←abs_div]
  congr 1
  rw [abs_of_pos (hpos r)]
  field_simp [(hpos r).ne']
  ring

#print axioms IsFreeTwoPoint.susceptibility_evenShell_spectrum

end IsingScaling
