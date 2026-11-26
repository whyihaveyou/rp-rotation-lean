import MathlibProbe.RotorPacketParitySmoothing
import MathlibProbe.IsingTangentExistence
import MathlibProbe.VagueSmallTranslations

/-! # Fixed lattice smoothing and susceptibility-normalized tangents

Both marks use the same 27-point product tent. Its displacements lie in the
radius-two cube, so the two cube sums differ by at most the mass of the
four-layer collar. The central pair in the tent bounds the original kernel
by 64 times the smoothed one. Apply the spatial density envelope of the
smoothed kernel at the *inner* collar radius: its cube sum there is bounded
by the original susceptibility at the requested radius. The relative collar
error is therefore O(1/R). The measure itself is a finite convex mixture
of lattice translations of size O(1/R), with this one normalization factor.
-/

noncomputable section
open Finset MeasureTheory Filter
open scoped Topology ENNReal CompactlySupported

namespace IsingScaling.Packet.ParitySmoothing

private theorem cube_subset_of_le {r s : ℕ} (h : r ≤ s) : cube r ⊆ cube s := by
  intro x hx
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  intro i
  have := hx i
  omega

private theorem cube_mono_mass {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    {r s : ℕ} (h : r ≤ s) : susceptibility g r ≤ susceptibility g s :=
  Finset.sum_le_sum_of_subset_of_nonneg (cube_subset_of_le h) (fun x _ _ => hn x)

private theorem cube_pos_mass {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) (r : ℕ) : 0 < susceptibility g r := by
  apply lt_of_lt_of_le h0
  apply Finset.single_le_sum (f := g) (fun x _ => hn x)
  simp [cube, Fintype.mem_piFinset]

private theorem offset_mem {r : ℕ} {x : Site} (hx : x ∈ cube r) (a b : Offset) :
    x + place a - place b ∈ cube (r+2) := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  intro i
  simp only [Pi.add_apply, Pi.sub_apply]
  have := hx i
  have := place_bound a i
  have := place_bound b i
  omega

private theorem translate_upper {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (r : ℕ) (a b : Offset) :
    (∑ x ∈ cube r, g (x + place a - place b)) ≤ susceptibility g (r+2) := by
  classical
  let f (x : Site) := x + place a - place b
  have hi : Function.Injective f := fun x y h => by
    change x + place a - place b = y + place a - place b at h
    exact add_right_cancel (sub_left_inj.mp h)
  have hsub : (cube r).image f ⊆ cube (r+2) := by
    rintro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact offset_mem hx a b
  calc
    _ = ∑ y ∈ (cube r).image f, g y := (Finset.sum_image (fun _ _ _ _ h => hi h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hn x)

private theorem translate_lower {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (r : ℕ) (a b : Offset) :
    susceptibility g r ≤ ∑ x ∈ cube (r+2), g (x + place a - place b) := by
  classical
  let f (x : Site) := x + place a - place b
  have hi : Function.Injective f := fun x y h => by
    change x + place a - place b = y + place a - place b at h
    exact add_right_cancel (sub_left_inj.mp h)
  have hsub : cube r ⊆ (cube (r+2)).image f := by
    intro z hz
    refine Finset.mem_image.mpr ⟨z + place b - place a, offset_mem hz b a, ?_⟩
    dsimp [f]; abel
  calc
    _ ≤ ∑ y ∈ (cube (r+2)).image f, g y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hn x)
    _ = _ := Finset.sum_image (fun _ _ _ _ h => hi h)

private theorem cube_sum_smooth (g : Site → ℝ) (r : ℕ) :
    susceptibility (smooth g) r =
      ∑ a : Offset, ∑ b : Offset, (mass a * mass b) *
        ∑ x ∈ cube r, g (x + place a - place b) := by
  classical
  unfold susceptibility smooth
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

private theorem weight_constant (v : ℝ) :
    (∑ a : Offset, ∑ b : Offset, mass a * mass b * v) = v := by
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sum_mass, one_mul]

/-- The right and left cube inclusions cost exactly two lattice layers. -/
theorem chi_smooth_sandwich {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x) (r : ℕ) :
    susceptibility (smooth g) r ≤ susceptibility g (r+2) ∧
    susceptibility g r ≤ susceptibility (smooth g) (r+2) := by
  constructor
  · rw [cube_sum_smooth, ← weight_constant (susceptibility g (r+2))]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left (translate_upper hn r a b) (mul_nonneg (mass_nonneg a) (mass_nonneg b))
  · rw [cube_sum_smooth, ← weight_constant (susceptibility g r)]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left (translate_lower hn r a b) (mul_nonneg (mass_nonneg a) (mass_nonneg b))

private theorem cube_cardinality (m : ℕ) : (cube m).card = (2*m+1)^3 := by
  rw [cube, Fintype.card_piFinset_const, Int.card_Icc]
  have hh : ((m:ℤ)+1 - (-(m:ℤ))).toNat = 2*m+1 := by omega
  rw [hh]

/-- Hypothesis (4.4) only for the covariance of smoothed marks. -/
def SmoothDensityEnvelope (g : Site → ℝ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Site,
    (∃ i : Fin 3, r ≤ ((x i).natAbs : ℝ)) →
      smooth g x ≤ B * susceptibility (smooth g) ⌊r⌋₊ / r^3

/-- Explicit relative susceptibility error at every integer scale at least four. -/
theorem susceptibility_smooth_relative {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) (he : SmoothDensityEnvelope g) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 4 ≤ r →
      |susceptibility (smooth g) r / susceptibility g r - 1| ≤ C / (r:ℝ) := by
  classical
  obtain ⟨B,hB,henv⟩ := he
  refine ⟨262144*B, by positivity, ?_⟩
  intro r hr
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, r = t+4 := ⟨r-4,by omega⟩
  let A := (cube (t+6)) \ (cube (t+2))
  let χ := susceptibility g (t+4)
  have hχ : 0 < χ := cube_pos_mass hn h0 _
  have hsub : cube (t+2) ⊆ cube (t+6) := cube_subset_of_le (by omega)
  have hm : (0:ℝ) < (t:ℝ)+2 := by positivity
  have hd : (0:ℝ) < (t:ℝ)+4 := by positivity
  have hpoint (x) (hx : x ∈ A) : g x ≤ 64*B*χ/((t:ℝ)+2)^3 := by
    have hout : x ∉ cube (t+2) := (Finset.mem_sdiff.mp hx).2
    simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hout
    push Not at hout
    obtain ⟨i,hi⟩ := hout
    have hcoord : t+2 ≤ (x i).natAbs := by omega
    have hv := henv ((t:ℝ)+2) (by linarith [Nat.cast_nonneg (α:=ℝ) t] : (1:ℝ) ≤ (t:ℝ)+2) x
      ⟨i,by exact_mod_cast hcoord⟩
    have hf : ⌊(t:ℝ)+2⌋₊ = t+2 := by
      rw [← Nat.cast_ofNat (n:=2), ← Nat.cast_add, Nat.floor_natCast]
    rw [hf] at hv
    have hs := (chi_smooth_sandwich hn (t+2)).1
    change susceptibility (smooth g) (t+2) ≤ χ at hs
    calc
      _ ≤ 64 * smooth g x := original_le_smooth hn x
      _ ≤ 64 * (B * χ / ((t:ℝ)+2)^3) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hv.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hB.le) (by positivity))
      _ = _ := by ring
  have hsum : susceptibility g (t+6) - susceptibility g (t+2) = ∑ x ∈ A, g x := by
    apply sub_eq_iff_eq_add.mpr
    exact (Finset.sum_sdiff hsub).symm
  have hcard : (A.card : ℝ) =
      (2*((t:ℝ)+6)+1)^3 - (2*((t:ℝ)+2)+1)^3 := by
    dsimp [A]
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [cube_cardinality,cube_cardinality]
    push_cast
    rfl
  have hpoly : ((2*((t:ℝ)+6)+1)^3-(2*((t:ℝ)+2)+1)^3) * ((t:ℝ)+4)
      ≤ 4096*((t:ℝ)+2)^3 := by
    nlinarith [sq_nonneg (t:ℝ), show 0 ≤ (t:ℝ)^3 by positivity]
  have hcollar : susceptibility g (t+6) - susceptibility g (t+2)
      ≤ 262144*B/((t:ℝ)+4) * χ := by
    rw [hsum]
    calc
      _ ≤ ∑ _x ∈ A, (64*B*χ/((t:ℝ)+2)^3) := Finset.sum_le_sum hpoint
      _ = (A.card:ℝ) * (64*B*χ/((t:ℝ)+2)^3) := by simp
      _ ≤ _ := by
        rw [hcard]
        field_simp
        nlinarith only [hpoly]
  have hinterval : |susceptibility (smooth g) (t+4)-χ| ≤
      susceptibility g (t+6) - susceptibility g (t+2) := by
    have hleft := (chi_smooth_sandwich hn (t+2)).2
    have hright := (chi_smooth_sandwich hn (t+4)).1
    have hlow : susceptibility g (t+2) ≤ χ := cube_mono_mass hn (by omega)
    have hhigh : χ ≤ susceptibility g (t+6) := cube_mono_mass hn (by omega)
    apply abs_le.mpr
    constructor <;> linarith
  change |susceptibility (smooth g) (t+4) / χ - 1| ≤ _
  rw [show susceptibility (smooth g) (t+4) / χ - 1 =
    (susceptibility (smooth g) (t+4) - χ) / χ by field_simp]
  rw [abs_div, abs_of_pos hχ]
  push_cast
  exact (div_le_iff₀ hχ).mpr (hinterval.trans hcollar)

theorem tendsto_susceptibility_smooth_ratio {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) (he : SmoothDensityEnvelope g) :
    Tendsto (fun r => susceptibility (smooth g) r / susceptibility g r) atTop (𝓝 1) := by
  obtain ⟨C,_,hC⟩ := susceptibility_smooth_relative hn h0 he
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop 4] with r hr
    exact hC r hr
  · simpa [div_eq_mul_inv] using
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul C)

private abbrev Stencil := Offset × Offset
private def w (p : Stencil) := mass p.1 * mass p.2
private def d (p : Stencil) := place p.1 - place p.2

private theorem w_nonneg (p : Stencil) : 0 ≤ w p :=
  mul_nonneg (mass_nonneg _) (mass_nonneg _)

private theorem w_sum : ∑ p : Stencil, w p = 1 := by
  rw [Fintype.sum_prod_type]
  change (∑ a : Offset, ∑ b : Offset, mass a * mass b) = 1
  simp only [←Finset.mul_sum, sum_mass, mul_one]

private theorem smooth_stencil (g : Site → ℝ) (x : Site) :
    smooth g x = ∑ p : Stencil, w p * g (x + d p) := by
  simp only [smooth, Fintype.sum_prod_type, w, d, add_sub_assoc]

private def grid (r : ℕ) (c : Site → ℝ≥0∞) : Measure Space :=
  Measure.sum (fun z => c z • Measure.dirac (scaledSite r z))

private theorem grid_mul (r : ℕ) (q : ℝ≥0∞) (c : Site → ℝ≥0∞) :
    grid r (fun z => q * c z) = q • grid r c := by
  ext S hS
  simp only [grid, Measure.sum_apply _ hS, Measure.smul_apply, smul_eq_mul]
  simp only [mul_assoc, ENNReal.tsum_mul_left]

private theorem grid_finsetSum {ι : Type*} [Fintype ι] (r : ℕ) (c : ι → Site → ℝ≥0∞) :
    grid r (fun z => ∑ i, c i z) = ∑ i, grid r (c i) := by
  ext S hS
  simp only [grid, Measure.finsetSum_apply, Measure.sum_apply _ hS, Measure.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

private theorem grid_mono (r : ℕ) {c b : Site → ℝ≥0∞} (h : ∀ x, c x ≤ b x) :
    grid r c ≤ grid r b := by
  apply Measure.le_iff.mpr
  intro S hS
  simp only [grid, Measure.sum_apply _ hS, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_right (h x) bot_le)

private theorem scaled_add_opp (r : ℕ) (x z : Site) :
    scaledSite r (x + z) + scaledSite r (-z) = scaledSite r x := by
  ext i
  change (((x i + z i : ℤ) : ℝ) / r + ((-z i : ℤ) : ℝ) / r) = _
  push_cast
  change ((x i : ℝ) + (z i : ℝ)) / r + - (z i : ℝ) / r = (x i : ℝ) / r
  ring

private theorem grid_shift (r : ℕ) (c : Site → ℝ≥0∞) (z : Site) :
    grid r (fun k => c (k+z)) =
      (grid r c).map (fun x => x + scaledSite r (-z)) := by
  classical
  let T (x : Space) := x + scaledSite r (-z)
  have hT : Measurable T := (continuous_id.add continuous_const).measurable
  unfold grid
  change _ = Measure.map T _
  rw [Measure.map_sum hT.aemeasurable]
  ext S hS
  simp only [Measure.sum_apply _ hS, Measure.map_smul, Measure.map_dirac' hT]
  let f (x : Site) := (c x • Measure.dirac (T (scaledSite r x))) S
  calc
    _ = ∑' k : Site, f (k+z) := by
      apply tsum_congr
      intro k
      simp only [f,T,scaled_add_opp]
    _ = ∑' k : Site, f k := (Equiv.addRight z).tsum_eq f

private theorem smooth_zero_pos {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) : 0 < smooth g 0 := by linarith [original_le_smooth hn 0]

/-- Exact identity for the two physical lattice measures at the *same*
scale. The prefactor retains the two different cube susceptibilities. -/
theorem measure_smooth_stencil {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) (r : ℕ) :
    ENNReal.ofReal (susceptibility (smooth g) r / susceptibility g r) •
        twoPointMeasure (smooth g) r =
      ∑ p : Offset × Offset, ENNReal.ofReal (mass p.1 * mass p.2) •
        (twoPointMeasure g r).map (fun x => x + scaledSite r (-(place p.1 - place p.2))) := by
  classical
  let a := susceptibility g r
  let b := susceptibility (smooth g) r
  have ha : 0 < a := cube_pos_mass hn h0 _
  have hb : 0 < b := cube_pos_mass (smooth_nonneg hn) (smooth_zero_pos hn h0) _
  change ENNReal.ofReal (b/a) • grid r (fun x => ENNReal.ofReal (smooth g x / b)) =
    ∑ p : Stencil, ENNReal.ofReal (w p) •
      (grid r (fun x => ENNReal.ofReal (g x/a))).map (fun x => x + scaledSite r (-(d p)))
  rw [←grid_mul]
  calc
    _ = grid r (fun z => ∑ p : Stencil,
          ENNReal.ofReal (w p) * ENNReal.ofReal (g (z+d p)/a)) := by
      apply congrArg (grid r)
      funext z
      rw [←ENNReal.ofReal_mul (div_nonneg hb.le ha.le)]
      rw [show b/a*(smooth g z/b) = smooth g z/a by field_simp]
      rw [smooth_stencil,Finset.sum_div,ENNReal.ofReal_sum_of_nonneg
        (fun p _ => div_nonneg (mul_nonneg (w_nonneg p) (hn _)) ha.le)]
      apply Finset.sum_congr rfl
      intro p _
      rw [←ENNReal.ofReal_mul (w_nonneg p)]
      apply congrArg ENNReal.ofReal
      ring
    _ = _ := by
      rw [grid_finsetSum]
      apply Finset.sum_congr rfl
      intro p _
      rw [grid_mul]
      exact congrArg (fun ν : Measure Space => ENNReal.ofReal (w p) • ν)
        (grid_shift r (fun z => ENNReal.ofReal (g z/a)) (d p))

private theorem original_measure_le {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) {r : ℕ}
    (hr : susceptibility (smooth g) r / susceptibility g r ≤ 2) :
    twoPointMeasure g r ≤ (128 : ℝ≥0∞) • twoPointMeasure (smooth g) r := by
  let a := susceptibility g r
  let b := susceptibility (smooth g) r
  have ha : 0 < a := cube_pos_mass hn h0 _
  have hb : 0 < b := cube_pos_mass (smooth_nonneg hn) (smooth_zero_pos hn h0) _
  change b/a ≤ 2 at hr
  have hb2 := (div_le_iff₀ ha).mp hr
  change grid r (fun x => ENNReal.ofReal (g x/a)) ≤
    (128 : ℝ≥0∞) • grid r (fun x => ENNReal.ofReal (smooth g x/b))
  rw [←grid_mul]
  apply grid_mono
  intro x
  rw [show (128 : ℝ≥0∞) = ENNReal.ofReal (128:ℝ) by norm_num,
    ←ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  calc
    g x / a ≤ 64*smooth g x / a :=
      div_le_div_of_nonneg_right (original_le_smooth hn x) ha.le
    _ ≤ 128 * (smooth g x / b) := by
      rw [←mul_div_assoc,div_le_div_iff₀ ha hb]
      nlinarith only [mul_le_mul_of_nonneg_right hb2 (smooth_nonneg hn x)]

private theorem integral_smooth_stencil {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) {r : ℕ} (hr : 0 < r) (φ : C_c(Space,ℝ)) :
    susceptibility (smooth g) r / susceptibility g r *
        (∫ x, φ x ∂twoPointMeasure (smooth g) r) =
      ∑ p : Stencil, w p * ∫ x, φ (x + scaledSite r (-(d p))) ∂twoPointMeasure g r := by
  classical
  let _ := finite_on_compacts_twoPointMeasure g hr
  let a := susceptibility (smooth g) r / susceptibility g r
  let T (p : Stencil) := Homeomorph.addRight (scaledSite r (-(d p)))
  have ha : 0 ≤ a := div_nonneg
    (cube_pos_mass (smooth_nonneg hn) (smooth_zero_pos hn h0) r).le (cube_pos_mass hn h0 r).le
  have hmeas (p : Stencil) : Measurable (T p) := (T p).continuous.measurable
  have hin (p : Stencil) :
      Integrable φ ((twoPointMeasure g r).map (T p)) := by
    apply (integrable_map_measure φ.continuous.aestronglyMeasurable (hmeas p).aemeasurable).mpr
    exact (φ.comp (T p).toCocompactMap).integrable
  have H := congrArg (fun ν : Measure Space => ∫ x, φ x ∂ν) (measure_smooth_stencil hn h0 r)
  change (∫ x, φ x ∂(ENNReal.ofReal a • twoPointMeasure (smooth g) r)) =
    (∫ x, φ x ∂∑ p : Stencil, ENNReal.ofReal (w p) • (twoPointMeasure g r).map (T p)) at H
  rw [integral_finsetSum_measure (fun p _ => (hin p).smul_measure ENNReal.ofReal_ne_top)] at H
  simp only [integral_smul_measure, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal (w_nonneg _), smul_eq_mul] at H
  change a * _ = _
  apply H.trans
  refine Finset.sum_congr rfl (fun p _ => ?_)
  apply congrArg (fun v : ℝ => w p * v)
  exact integral_map (f := (φ : Space → ℝ)) (hmeas p).aemeasurable φ.continuous.aestronglyMeasurable

private theorem tendsto_scaled_fixed {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (x : Site) :
    Tendsto (fun n => scaledSite (R n) x) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => ((R n : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hR
  have hEq (r) : scaledSite r x = ((r:ℝ)⁻¹) • scaledSite 1 x := by
    ext i
    change (x i : ℝ)/r = ((r:ℝ)⁻¹)*((x i:ℝ)/(1:ℕ))
    simp [div_eq_mul_inv,mul_comm]
  have ht : Tendsto (fun n => ((R n : ℝ)⁻¹) • scaledSite 1 x) atTop (𝓝 0) := by
    simpa only [zero_smul] using hi.smul_const (scaledSite 1 x)
  exact ht.congr' (Eventually.of_forall (fun n => (hEq (R n)).symm))

/-- The smoothed and original physical two-point measures have exactly the
same vague limits on every *prescribed* diverging sequence, with the cube
susceptibility of each kernel in its own measure. The target may have an
atom at the origin. -/
theorem vague_smooth_iff {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : 0 < g 0) (he : SmoothDensityEnvelope g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {μ : Measure Space} :
    (∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure (smooth g) (R n))
        atTop (𝓝 (∫ x, φ x ∂μ))) ↔
    (∀ φ : C_c(Space, ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure g (R n))
        atTop (𝓝 (∫ x, φ x ∂μ))) := by
  classical
  let S n := max (R n) 1
  have hS : S =ᶠ[atTop] R := by
    filter_upwards [hR.eventually_ge_atTop 1] with n hn
    exact max_eq_left hn
  have ht : Tendsto S atTop atTop := hR.congr' hS.symm
  have hp (n) : 0 < S n := by dsimp [S]; omega
  let _ : ∀ n, IsFiniteMeasureOnCompacts (twoPointMeasure g (S n)) :=
    fun n => finite_on_compacts_twoPointMeasure g (hp n)
  let _ : ∀ n, IsFiniteMeasureOnCompacts (twoPointMeasure (smooth g) (S n)) :=
    fun n => finite_on_compacts_twoPointMeasure (smooth g) (hp n)
  have hq := (tendsto_susceptibility_smooth_ratio hn h0 he).comp ht
  have hbound := hq.eventually_lt_const (by norm_num : (1:ℝ) < 2)
  have hdom : ∀ᶠ n in atTop, twoPointMeasure g (S n) ≤
      (128 : ℝ≥0∞) • twoPointMeasure (smooth g) (S n) := by
    filter_upwards [hbound] with n h
    exact original_measure_le hn h0 h.le
  have hcore := vague_finite_stencil_iff (μ := μ) hq w w_sum
    (fun p n => scaledSite (S n) (-(d p))) (fun p => tendsto_scaled_fixed ht (-(d p)))
    (fun φ => Eventually.of_forall (fun n => integral_smooth_stencil hn h0 (hp n) φ))
    hdom
  have replace (b : Site → ℝ) :
      (∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure b (S n)) atTop
          (𝓝 (∫ x, φ x ∂μ))) ↔
      (∀ φ : C_c(Space,ℝ), Tendsto (fun n => ∫ x, φ x ∂twoPointMeasure b (R n)) atTop
          (𝓝 (∫ x, φ x ∂μ))) := by
    have eqφ (φ : C_c(Space,ℝ)) :
        (fun n => ∫ x, φ x ∂twoPointMeasure b (S n)) =ᶠ[atTop]
        (fun n => ∫ x, φ x ∂twoPointMeasure b (R n)) := by
      filter_upwards [hS] with n hn using congrArg (fun r => ∫ x, φ x ∂twoPointMeasure b r) hn
    exact ⟨fun h φ => (h φ).congr' (eqφ φ), fun h φ => (h φ).congr' (eqφ φ).symm⟩
  exact (replace (smooth g)).symm.trans (hcore.trans (replace g))

end IsingScaling.Packet.ParitySmoothing
