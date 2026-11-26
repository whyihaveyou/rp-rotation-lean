import MathlibProbe.RotorHeisenbergRotateComplexField

/-!
# Three real directions for the finite Heisenberg Lee–Yang cone

For a compact subset of the open complex field half-plane, one real centre
and one radius larger than one work for all affine paths to this compact set.
The three nearly longitudinal real spin directions span the internal spin
space. Local complex perturbations have a uniform radius in every one of
their rotated cones. The bounds are independent of the vertex set.
-/

noncomputable section

open Metric Set Finset MeasureTheory
open scoped InnerProductSpace Classical
namespace IsingScaling.Rotor.HeisenbergField.FieldCone
open ComplexPartition

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Frame := Space ≃ₗᵢ[ℝ] Space
abbrev std (i : Fin 3) : Space := EuclideanSpace.single i 1

/-- The interpolating field is uniform before a single marked-site perturbation. -/
def path (h₀ : ℝ) (h w : ℂ) : ℂ := (h₀ : ℂ) + w * (h - h₀)

theorem compact_path {K : Set ℂ} (hk : IsCompact K)
    (hpos : ∀ h ∈ K, 0 < h.re) :
    ∃ h₀ ρ a M : ℝ, 0 < h₀ ∧ 1 < ρ ∧ 0 < a ∧ 0 < M ∧
      ∀ h ∈ K, ∀ w : ℂ, ‖w‖ ≤ ρ →
        a ≤ (path h₀ h w).re ∧ ‖path h₀ h w‖ ≤ M := by
  by_cases hne : K.Nonempty
  · obtain ⟨hm, hmin, hmle⟩ := hk.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨hb, hbK, hble⟩ := hk.exists_isMaxOn hne (continuous_norm (E := ℂ)).continuousOn
    have hmpos := hpos hm hmin
    let h₀ := (‖hb‖^2 + 1) / hm.re
    have hc : 0 < h₀ := by dsimp [h₀]; positivity
    have hprod : h₀ * hm.re = ‖hb‖^2 + 1 := div_mul_cancel₀ _ hmpos.ne'
    have inside (h : ℂ) (hh : h ∈ K) : ‖h - (h₀ : ℂ)‖ < h₀ := by
      have h1 : h₀ * hm.re ≤ h₀ * h.re := mul_le_mul_of_nonneg_left (hmle hh) hc.le
      have h2 : ‖h‖^2 ≤ ‖hb‖^2 := by
        have hle : ‖h‖ ≤ ‖hb‖ := hble hh
        gcongr
      have hs : ‖h - (h₀ : ℂ)‖^2 = ‖h‖^2 + h₀^2 - 2*(h.re*h₀) := by
        rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm h, Complex.normSq_ofReal]
        simp [sq]
      nlinarith [norm_nonneg (h-(h₀:ℂ)), sq_nonneg ‖hb‖]
    obtain ⟨hd, hdK, hmax⟩ := hk.exists_isMaxOn hne
      ((continuous_id.sub (continuous_const (y := (h₀:ℂ)))).norm.continuousOn)
    let D := ‖hd-(h₀:ℂ)‖
    have hD : 0 ≤ D := norm_nonneg _
    have hDc : D < h₀ := inside hd hdK
    let k := (h₀-D)/(2*(D+1))
    have hkpos : 0 < k := by dsimp [k]; positivity
    have hkprod : k * (2*(D+1)) = h₀-D := by
      exact div_mul_cancel₀ _ (by positivity)
    have gap : 0 < h₀ - (1+k)*D := by nlinarith [mul_nonneg hkpos.le hD]
    refine ⟨h₀, 1+k, h₀-(1+k)*D, 2*h₀, hc, by linarith, gap, by positivity, ?_⟩
    intro h hh w hw
    have hhD : ‖h-(h₀:ℂ)‖ ≤ D := hmax hh
    have hn : ‖w * (h - h₀)‖ ≤ (1+k)*D := by
      rw [norm_mul]
      exact mul_le_mul hw hhD (norm_nonneg _) (by linarith)
    constructor
    · change h₀ - _ ≤ ((h₀ : ℂ) + _).re
      rw [Complex.add_re, Complex.ofReal_re]
      linarith [Complex.abs_re_le_norm (w*(h-h₀)), neg_abs_le (w*(h-h₀)).re]
    · calc ‖path h₀ h w‖ ≤ ‖(h₀:ℂ)‖ + ‖w*(h-h₀)‖ := norm_add_le _ _
           _ ≤ 2*h₀ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]; linarith
  · exact ⟨1,2,1,2,by norm_num,by norm_num,by norm_num,by norm_num,
      fun h hh => (hne ⟨h,hh⟩).elim⟩

structure Tilt where
  d : ℝ
  pos : 0 < d
  small : d ≤ 1/2

def Tilt.c (t : Tilt) : ℝ := Real.sqrt (1-t.d^2)

theorem Tilt.c_sq (t : Tilt) : t.c^2 + t.d^2 = 1 := by
  have hh : 0 ≤ 1-t.d^2 := by nlinarith [t.pos,t.small,mul_nonneg t.pos.le (show 0 ≤ 1-t.d by linarith [t.small])]
  rw [Tilt.c, Real.sq_sqrt hh]
  ring

theorem Tilt.c_bounds (t : Tilt) : 1/2 ≤ t.c ∧ t.c ≤ 1 := by
  have hc : 0 ≤ t.c := Real.sqrt_nonneg _
  have h₁ : 0 ≤ 1/2-t.d := by linarith [t.small]
  have h₂ : 0 ≤ 1/2+t.d := by linarith [t.pos]
  have hd : t.d^2 ≤ 1/4 := by nlinarith [mul_nonneg h₁ h₂]
  constructor <;> nlinarith [t.c_sq,sq_nonneg t.d]

/-- The longitudinal axis and its tilts towards the two transverse coordinates. -/
def Tilt.axis (t : Tilt) (j : Fin 3) : Spin 3 :=
  if hj : j = 0 then firstSpin else
  ⟨EuclideanSpace.single 0 t.c + EuclideanSpace.single j t.d, by
    rw [mem_sphere_zero_iff_norm]
    have h : ‖(EuclideanSpace.single 0 t.c : Space) + EuclideanSpace.single j t.d‖^2 =
        1 := by
      simpa [norm_add_sq_real,EuclideanSpace.inner_single_left,PiLp.single_apply,Ne.symm hj,
        sq_abs] using t.c_sq
    nlinarith [norm_nonneg ((EuclideanSpace.single 0 t.c : Space) + EuclideanSpace.single j t.d)]⟩

/-- A common orthogonal change of coordinates whose first column is the desired spin axis. -/
def frame (u : Spin 3) : Frame :=
  (Submodule.span ℝ ({firstSpin.val-u.val} : Set Space))ᗮ.reflection

theorem frame_zero (u : Spin 3) : frame u (std 0) = u.val :=
  Submodule.reflection_sub (v := firstSpin.val) (by simp [norm_eq_of_mem_sphere])

theorem frame_involutive (u : Spin 3) (v : Space) : frame u (frame u v) = v :=
  Submodule.reflection_reflection _ _

/-- Longitudinal input projected onto each physical column of the frame. -/
theorem frame_at_zero (u : Spin 3) (i : Fin 3) : (frame u (std i)) 0 = u.val i := by
  have hs := (frame u).inner_map_map (std i) u.val
  have hi : frame u u.val = std 0 := by
    rw [← frame_zero u]
    exact frame_involutive _ _
  rw [hi] at hs
  simpa [EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right] using hs

theorem inner_frame_axis (u : Spin 3) (i : Fin 3) :
    ⟪frame u (std i), u.val⟫_ℝ = if i = 0 then 1 else 0 := by
  rw [← frame_zero u,(frame u).inner_map_map]
  by_cases hi : i = 0 <;> simp [hi,EuclideanSpace.inner_single_left]

variable {V : Type*}

/-- Coordinates of the physical complex field in the common real orthogonal frame. -/
def coordinate (O : Frame) (H : ComplexPartition.Field V) (x : V) (i : Fin 3) : ℂ :=
  rotateField O H x i

def margin (O : Frame) (H : ComplexPartition.Field V) (x : V) : ℝ :=
  (coordinate O H x 0).re - ‖coordinate O H x 1‖ - ‖coordinate O H x 2‖

def InCone (O : Frame) (H : ComplexPartition.Field V) : Prop := ∀ x, 0 < margin O H x

theorem inCone_iff (O : Frame) (H : ComplexPartition.Field V) :
    InCone O H ↔ ∀ x, ‖rotateField O H x 1‖ + ‖rotateField O H x 2‖ <
      (rotateField O H x 0).re := by
  constructor <;> intro hh x <;> specialize hh x <;> unfold margin coordinate at * <;> linarith

/-- Consume the ordinary, unrotated finite-volume Lee–Yang statement for this graph. -/
theorem partition_ne_zero_of_cone [Fintype V] (J : V → V → ℝ)
    (hLY : ∀ F : ComplexPartition.Field V, (∀ x, ‖F x 1‖ + ‖F x 2‖ < (F x 0).re) →
      partition J F ≠ 0) (O : Frame) (H : ComplexPartition.Field V) (hH : InCone O H) :
    partition J H ≠ 0 := by
  rw [← partition_rotateField J O H]
  exact hLY _ ((inCone_iff _ _).mp hH)

theorem coordinate_uniform (u : Spin 3) (h : ℂ) (x : V) (i : Fin 3) :
    coordinate (frame u) (uniform h) x i = h * (u.val i : ℂ) := by
  simp [coordinate,rotateField,uniform,ite_mul,frame_at_zero]

theorem coordinate_addAt (O : Frame) (H : ComplexPartition.Field V) (x y : V) (u : Spin 3) (z : ℂ) (i : Fin 3) :
    coordinate O (addAt H x u z) y i = coordinate O H y i +
      if y=x then z * (⟪O (std i),u.val⟫_ℝ : ℂ) else 0 := by
  classical
  by_cases hy : y=x
  · simp [coordinate,rotateField, addAt,hy,add_mul,Finset.sum_add_distrib,PiLp.inner_apply,
      Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
  · simp [coordinate,rotateField,addAt,hy]

theorem margin_addAt_lower (O : Frame) (H : ComplexPartition.Field V) (x y : V) (u : Spin 3) (z : ℂ) :
    margin O H y - 3*‖z‖ ≤ margin O (addAt H x u z) y := by
  classical
  let e (i : Fin 3) := if y=x then z*(⟪O (std i),u.val⟫_ℝ : ℂ) else 0
  have he (i : Fin 3) : ‖e i‖ ≤ ‖z‖ := by
    by_cases hy : y=x
    · simp only [e,hy,ite_true,norm_mul,Complex.norm_real]
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa [norm_eq_of_mem_sphere] using norm_inner_le_norm (𝕜 := ℝ) (O (std i)) u.val
    · simp [e,hy]
  have hadd (i : Fin 3) : coordinate O (addAt H x u z) y i = coordinate O H y i + e i :=
    coordinate_addAt _ _ _ _ _ _ _
  simp only [margin,hadd,Complex.add_re]
  linarith [he 0,he 1,he 2,Complex.abs_re_le_norm (e 0),neg_abs_le (e 0).re,
    norm_add_le (coordinate O H y 1) (e 1),norm_add_le (coordinate O H y 2) (e 2)]

/-- Shifting at one arbitrary site by a right-half-plane field in the first frame axis
increases the Lee–Yang margin by its real part there and leaves every other margin fixed. -/
theorem margin_axis_shift (u : Spin 3) (H : ComplexPartition.Field V) (x y : V) (z : ℂ) :
    margin (frame u) (addAt H x u z) y =
      margin (frame u) H y + if y = x then z.re else 0 := by
  classical
  by_cases hy : y=x <;> simp [margin,coordinate_addAt,inner_frame_axis,hy] <;> ring

theorem Tilt.margin_uniform_lower (t : Tilt) (j : Fin 3) {a M : ℝ} (ha : 0 < a)
    {H : ℂ} (hre : a ≤ H.re) (hn : ‖H‖ ≤ M) (hsmall : t.d*M ≤ a/4) (x : V) :
    a/4 ≤ margin (frame (t.axis j)) (uniform H) x := by
  have hc := t.c_bounds
  have hprod : a/2 ≤ H.re*t.c :=
    calc a/2 = a*(1/2) := by ring
         _ ≤ H.re*t.c := mul_le_mul hre hc.1 (by norm_num) (by linarith)
  have hd : ‖H‖*t.d ≤ a/4 := by
    calc ‖H‖*t.d ≤ M*t.d := mul_le_mul_of_nonneg_right hn t.pos.le
         _ ≤ a/4 := by simpa [mul_comm] using hsmall
  fin_cases j <;>
    simp [margin,coordinate_uniform,Tilt.axis,firstSpin,Complex.mul_re,
      Real.norm_eq_abs,abs_of_pos t.pos] <;> linarith

theorem affine_mark_path (h₀ : ℝ) (h : ℂ) (y : V) (v : Spin 3) (z w : ℂ) :
    affine (uniform h₀) (addAt (uniform h) y v z - uniform h₀) w =
      addAt (uniform (path h₀ h w)) y v (w*z) := by
  classical
  funext x i
  by_cases hy : x=y <;> by_cases hi : i=0 <;>
    simp [affine,uniform,addAt,path,hy,hi] <;> ring

/-- All quantifiers over vertices, volumes, marked spin directions and complex
local fields are inside one choice of compact-set parameters. The last displacement
has arbitrary nonnegative real part and arbitrary imaginary part. -/
theorem disk_cones {K : Set ℂ} (hk : IsCompact K) (hpos : ∀ h ∈ K, 0 < h.re) :
    ∃ (h₀ ρ δ : ℝ) (t : Tilt), 0 < h₀ ∧ 1 < ρ ∧ 0 < δ ∧
      ∀ h ∈ K, ∀ {W : Type*} (x y : W) (j : Fin 3) (v : Spin 3) {z w l : ℂ},
      ‖z‖ ≤ δ → ‖w‖ ≤ ρ → 0 ≤ l.re →
      InCone (frame (t.axis j)) (addAt
        (affine (uniform h₀) (addAt (uniform h) y v z - uniform h₀) w) x (t.axis j) l) := by
  obtain ⟨h₀,ρ,a,M,hc,hr,ha,hM,hpath⟩ := compact_path hk hpos
  have hr0 : 0 < ρ := by linarith
  let t : Tilt := ⟨min (1/2) (a/(4*M)),lt_min (by norm_num) (by positivity),min_le_left _ _⟩
  have ht : t.d * M ≤ a/4 := by
    have hl : t.d ≤ a/(4*M) := min_le_right _ _
    have h4 : 0 < 4*M := by positivity
    have hh := (le_div_iff₀ h4).mp hl
    linarith
  let δ := a/(24*ρ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hs : ρ*δ = a/24 := by
    dsimp [δ]
    field_simp [hr0.ne']
  refine ⟨h₀,ρ,δ,t,hc,hr,hδ,?_⟩
  intro h hh W x y j v z w l hz hw hl k
  rw [affine_mark_path,margin_axis_shift]
  have hq := hpath h hh w hw
  have hbase := t.margin_uniform_lower j ha hq.1 hq.2 ht k
  have hn : ‖w*z‖ ≤ a/24 := by
    rw [norm_mul, ← hs]
    exact mul_le_mul hw hz (norm_nonneg _) hr0.le
  have hmark := margin_addAt_lower (frame (t.axis j)) (uniform (path h₀ h w)) y k v (w*z)
  have hlast : 0 ≤ if k = x then l.re else (0:ℝ) := by split_ifs <;> positivity
  linarith

/-- Pair readout normalized by the same physical partition function before
and after the finite change of spin coordinates. -/
def projectedPair [Fintype V] (J : V → V → ℝ) (H : ComplexPartition.Field V) (x y : V) (u v : Spin 3) : ℂ :=
  marked J H (complexMark (component x u * component y v)) / partition J H

def Tilt.coeff (t : Tilt) (k i : Fin 3) : ℝ :=
  if k = 0 then (if i = 0 then 1 else 0)
  else if i = 0 then -t.c/t.d else if k = i then 1/t.d else 0

theorem Tilt.inner_axis (t : Tilt) (i : Fin 3) (s : Spin 3) :
    ⟪(t.axis i).val,s.val⟫_ℝ =
    if i = 0 then s.val 0 else t.c*s.val 0 + t.d*s.val i := by
  by_cases hi : i=0 <;>
    simp [Tilt.axis,hi,firstSpin,inner_add_left,EuclideanSpace.inner_single_left]

theorem Tilt.coordinate_expansion (t : Tilt) (s : Spin 3) (k : Fin 3) :
    s.val k = ∑ i : Fin 3, t.coeff k i * ⟪(t.axis i).val,s.val⟫_ℝ := by
  fin_cases k <;> simp [Fin.sum_univ_three,Tilt.coeff,t.inner_axis] <;>
    field_simp [t.pos.ne'] <;> ring

def Tilt.dotCoeff (t : Tilt) (i : Fin 3 × Fin 3 × Fin 3) : ℝ :=
  t.coeff i.1 i.2.1 * t.coeff i.1 i.2.2

theorem Tilt.dot_expansion (t : Tilt) (s s' : Spin 3) :
    ⟪s.val,s'.val⟫_ℝ = ∑ i : Fin 3 × Fin 3 × Fin 3, t.dotCoeff i *
      (⟪(t.axis i.2.1).val,s.val⟫_ℝ * ⟪(t.axis i.2.2).val,s'.val⟫_ℝ) := by
  rw [show ⟪s.val,s'.val⟫_ℝ = ∑ k : Fin 3, s.val k * s'.val k by
    simp only [PiLp.inner_apply,Real.inner_apply]]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_lhs => rw [t.coordinate_expansion s' k,t.coordinate_expansion s k]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Tilt.dotCoeff]
  ring

def originalDot (x y : V) : C(Config V,ℝ) where
  toFun s := ⟪(s x).val,(s y).val⟫_ℝ
  continuous_toFun := by fun_prop

private theorem ratio_of_expansion [Fintype V] {I : Type*} [Fintype I]
    (J : V → V → ℝ) (H : ComplexPartition.Field V) (F : C(Config V,ℝ))
    (B : I → C(Config V,ℝ)) (c : I → ℝ) (he : ∀ s, F s = ∑ i, c i * B i s) :
    marked J H (complexMark F) / partition J H =
      ∑ i, (c i : ℂ) * (marked J H (complexMark (B i)) / partition J H) := by
  have hb (i : I) : Integrable (fun s => (c i:ℂ) * (weight J H s * complexMark (B i) s))
      (surfaceProduct V) := ((continuous_const.mul ((weight J H).continuous.mul
        (complexMark (B i)).continuous))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  unfold marked
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ => hb i)]
  apply integral_congr_ae
  filter_upwards [] with s
  change weight J H s * (F s : ℂ) = _
  rw [he, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [complexMark,mul_left_comm]

theorem Tilt.dot_ratio [Fintype V] (t : Tilt) (J : V → V → ℝ) (H : ComplexPartition.Field V) (x y : V) :
    marked J H (complexMark (originalDot x y)) / partition J H =
      ∑ i : Fin 3 × Fin 3 × Fin 3, (t.dotCoeff i : ℂ) *
        projectedPair J H x y (t.axis i.2.1) (t.axis i.2.2) := by
  apply ratio_of_expansion J H (originalDot x y)
    (fun i => component x (t.axis i.2.1) * component y (t.axis i.2.2)) t.dotCoeff
  exact fun s => t.dot_expansion (s x) (s y)

def Tilt.dotCost (t : Tilt) := ∑ i : Fin 3 × Fin 3 × Fin 3, |t.dotCoeff i|

theorem Tilt.dotCost_eq (t : Tilt) : t.dotCost = 1 + 2*((1+t.c)/t.d)^2 := by
  have hc : 0 ≤ t.c := Real.sqrt_nonneg _
  simp [Tilt.dotCost,Fintype.sum_prod_type,Fin.sum_univ_three,Tilt.dotCoeff,Tilt.coeff,
    abs_mul,abs_div,abs_of_nonneg hc,abs_of_pos t.pos] <;> ring

theorem Tilt.dotCost_le (t : Tilt) : t.dotCost ≤ 1+8/t.d^2 := by
  have hc := t.c_bounds
  have hd := t.pos
  have h₁ : 0 ≤ 1-t.c := by linarith
  have h₂ : 0 ≤ 3+t.c := by linarith
  have hs : (1+t.c)^2 ≤ 4 := by nlinarith [mul_nonneg h₁ h₂]
  rw [t.dotCost_eq,div_pow]
  field_simp [hd.ne']
  nlinarith

/-- An arbitrary finite-volume dot is bounded by the nine normalized spin-direction
products. The cost depends just on the compact-set tilt. -/
theorem Tilt.norm_dot_ratio [Fintype V] (t : Tilt) (J : V → V → ℝ) (H : ComplexPartition.Field V) (x y : V)
    {B : ℝ} (hb : ∀ i j, ‖projectedPair J H x y (t.axis i) (t.axis j)‖ ≤ B) :
    ‖marked J H (complexMark (originalDot x y)) / partition J H‖ ≤ t.dotCost*B := by
  rw [t.dot_ratio]
  apply (norm_sum_le _ _).trans
  rw [Tilt.dotCost, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  gcongr
  exact hb _ _

#print axioms disk_cones
#print axioms Tilt.dot_ratio
#print axioms Tilt.norm_dot_ratio

end IsingScaling.Rotor.HeisenbergField.FieldCone
