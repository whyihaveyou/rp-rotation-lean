import MathlibProbe.RotorHeisenbergComplexPartition
import MathlibProbe.RotorLargeFieldCommonLimit
import MathlibProbe.RotorRightHalfPlaneVitali

/-!
# Positive-field continuation of the two Heisenberg dot comparisons

The finite functions are ratios of the actual spin integrals for each free
graph. For cubes we use fixed lattice sites as soon as the volume contains
them. The rectangle uses the two physical ports of the bond reflection.
Large real fields supply the real uniqueness interval. The analytic inputs
are nonzero finite partition functions and a compact-uniform bound for the
normalized two-spin insertions, on both sequences of graphs.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators

namespace IsingScaling.Rotor.HeisenbergField.PositiveFieldContinuation
open ComplexPartition PressureSelection PressureSelection.LocalGibbs

variable {V : Type*} [Fintype V]

def dotMark (i j : V) : C(Config V, ℝ) where
  toFun s := ⟪(s i).val, (s j).val⟫_ℝ
  continuous_toFun := by fun_prop

def finiteDot (J : V → V → ℝ) (i j : V) (z : ℂ) : ℂ :=
  marked J (uniform z) (complexMark (dotMark i j)) / partition J (uniform z)

/-- The indicated fixed components at the indicated physical vertices. -/
def coordinateMark (i j : V) (a b : Fin 3) : C(Config V,ℝ) where
  toFun s := (s i).val a * (s j).val b
  continuous_toFun := by fun_prop

def coordinateRatio (J : V → V → ℝ) (i j : V) (a b : Fin 3) (z : ℂ) : ℂ :=
  marked J (uniform z) (complexMark (coordinateMark i j a b)) / partition J (uniform z)

/-- The sum uses one physical partition for all three coordinate insertions.
The two chosen vertices may coincide. -/
theorem finiteDot_eq_sum_coordinateRatios (J : V → V → ℝ) (i j : V) (z : ℂ) :
    finiteDot J i j z = ∑ a : Fin 3, coordinateRatio J i j a a z := by
  have mc (a : Fin 3) : Continuous (fun s : Config V =>
      weight J (uniform z) s * complexMark (coordinateMark i j a a) s) :=
    (weight J (uniform z)).continuous.mul (complexMark (coordinateMark i j a a)).continuous
  have mark_eq : marked J (uniform z) (complexMark (dotMark i j)) =
      ∑ a : Fin 3, marked J (uniform z) (complexMark (coordinateMark i j a a)) := by
    unfold marked
    rw [← integral_finsetSum _ (fun a _ => (mc a).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [← Finset.mul_sum]
    congr 1
    simp [dotMark, coordinateMark, complexMark, PiLp.inner_apply, mul_comm]
  unfold finiteDot coordinateRatio
  rw [mark_eq, Finset.sum_div]

theorem norm_finiteDot_le_three_mul (J : V → V → ℝ) (i j : V) (z : ℂ) {B : ℝ}
    (hb : ∀ a : Fin 3, ‖coordinateRatio J i j a a z‖ ≤ B) : ‖finiteDot J i j z‖ ≤ 3 * B := by
  rw [finiteDot_eq_sum_coordinateRatios]
  calc
    _ ≤ ∑ a : Fin 3, ‖coordinateRatio J i j a a z‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, B := Finset.sum_le_sum fun a _ => hb a
    _ = _ := by simp

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

/-- Each hypothesis concerns the finite partition and a dot insertion on the
same graph in the family. The compact bound is uniform in the two vertices. -/
structure FreeDotControl (V : ℕ → Type) [∀ n, Fintype (V n)]
    (J : (n : ℕ) → V n → V n → ℝ) : Prop where
  nonzero : ∀ n z, z ∈ rightHalfPlane → partition (J n) (uniform z) ≠ 0
  bounded : ∀ K : Set ℂ, IsCompact K → K ⊆ rightHalfPlane →
    ∃ M : ℝ, ∀ n (i j : V n) z, z ∈ K → ‖finiteDot (J n) i j z‖ ≤ M

/-- The arbitrary value used before the fixed site enters the free cube. -/
def cubePort (n : ℕ) (x : Site) : BoxSite n :=
  if hx : x ∈ cube n then ⟨x,hx⟩ else ⟨0,by simp [cube, Fintype.mem_piFinset]⟩

def rectangleCoupling (n : ℕ) (β : ℝ) (i j : BondMirror.V n) : ℝ :=
  nearestCoupling β (FreeInduced.rectIndex n j - FreeInduced.rectIndex n i)

private theorem cube_dot_real (β h : ℝ) (x y : Site) :
    ∀ᶠ n in atTop, finiteDot (cubeCoupling n β) (cubePort n x) (cubePort n y) (h : ℂ) =
      Complex.ofReal (∫ s, fieldDot 3 x y s ∂(cubeLaw β h n : Measure _)) := by
  filter_upwards [BondMirror.ev_cube x, BondMirror.ev_cube y] with n hx hy
  rw [cubeLaw_eq_complex_moment]
  simp [finiteDot, marked, complexMark, dotMark, cubePort, hx, hy, fieldDot, extendCube]

private theorem rectangle_dot_real (β h : ℝ) (n : ℕ) (x y : Site) :
    finiteDot (rectangleCoupling n β) (true,BondMirror.port n x) (false,BondMirror.port n y)
        (h : ℂ) =
      (BondRectangle.crossPair (fieldPrior h) β (BondMirror.port n x) (BondMirror.port n y) : ℂ) := by
  let i := BondMirror.port n x
  let j := BondMirror.port n y
  have e := (FreeInduced.indexed_dot_integral (FreeInduced.rectIndex n) β h (true,i) (false,j)).symm.trans
    (FreeInduced.rect_pair_integral β h n i j)
  exact (real_uniform_ratio (rectangleCoupling n β) h (dotMark (true,i) (false,j))).symm.trans
    (congrArg (fun w : ℝ => (w : ℂ)) e)

/-- Apply the disk continuation to two named finite spin integrals, whose
difference equals a real physical record for all sufficiently large volumes. -/
private theorem continuation {V W : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Fintype (W n)]
    {J : (n : ℕ) → V n → V n → ℝ} {T : (n : ℕ) → W n → W n → ℝ}
    (A : FreeDotControl V J) (B : FreeDotControl W T)
    (i j : ∀ n, V n) (k l : ∀ n, W n) (realRecord : ℝ → ℕ → ℝ)
    (physical : ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
      finiteDot (J n) (i n) (j n) (t : ℂ) - finiteDot (T n) (k n) (l n) (t : ℂ) =
        (realRecord t n : ℂ))
    (tail : ∀ᶠ t : ℝ in atTop, Tendsto (realRecord t) atTop (𝓝 0))
    {h : ℝ} (hh : 0 < h) : Tendsto (realRecord h) atTop (𝓝 0) := by
  let d (n : ℕ) (z : ℂ) := finiteDot (J n) (i n) (j n) z - finiteDot (T n) (k n) (l n) z
  have holo (n : ℕ) : DifferentiableOn ℂ (d n) rightHalfPlane :=
    ((entire_marked_uniform _ _).differentiableOn.div (entire_partition_uniform _).differentiableOn
      (A.nonzero n)).sub
    ((entire_marked_uniform _ _).differentiableOn.div (entire_partition_uniform _).differentiableOn
      (B.nonzero n))
  have bound (K : Set ℂ) (hc : IsCompact K) (hs : K ⊆ rightHalfPlane) :
      ∃ M : ℝ, ∀ n z, z ∈ K → ‖d n z‖ ≤ M := by
    obtain ⟨m,hm⟩ := A.bounded K hc hs
    obtain ⟨p,hp⟩ := B.bounded K hc hs
    exact ⟨m+p,fun n z hz => (norm_sub_le ..).trans
      (add_le_add (hm n (i n) (j n) z hz) (hp n (k n) (l n) z hz))⟩
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.1 tail
  let a := max t₀ 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right t₀ 0]
  have high (t : ℝ) (ht : a < t) (_ : t < a + 1) :
      Tendsto (fun n => d n (t : ℂ)) atTop (𝓝 0) := by
    have ht₀' : t₀ ≤ t := by dsimp [a] at ht; linarith [le_max_left t₀ 0]
    have hc : Tendsto (fun n => (realRecord t n : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp (ht₀ t ht₀')
    apply hc.congr'
    filter_upwards [physical t (ha.trans ht)] with n eq using eq.symm
  have hcont := RotorVitali.rightHalfPlane_vitali_zero ha (by linarith : a < a+1)
    holo bound high hh
  have castlim : Tendsto (fun n => (realRecord h n : ℂ)) atTop (𝓝 0) :=
    hcont.congr' (physical h hh)
  simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp castlim

/-- The two required finite-volume comparisons hold on every positive real
field once the physical normalized dots satisfy the compact complex bounds. -/
theorem freeDotComparison_of_complex_control {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    {h : ℝ} (hh : 0 < h) : FreeDotComparison β h id := by
  have high : ∀ᶠ t : ℝ in atTop, FreeDotComparison β t id := by
    filter_upwards [LargeField.common_free_limit_eventually hβ] with t ⟨_,_,_,H⟩
    exact H.dotComparison
  constructor
  · intro x y
    apply continuation C C (fun n => cubePort n x) (fun n => cubePort n y)
      (fun n => cubePort n 0) (fun n => cubePort n (x-y))
      (fun t n => (∫ s, fieldDot 3 x y s ∂(cubeLaw β t n : Measure _)) -
        ∫ s, fieldDot 3 0 (x-y) s ∂(cubeLaw β t n : Measure _)) _ _ hh
    · intro t _
      filter_upwards [cube_dot_real β t x y, cube_dot_real β t 0 (x-y)] with n h₁ h₂
      rw [h₁,h₂,Complex.ofReal_sub]
    · exact high.mono fun _ H => H.translate x y
  · intro x y hx hy
    apply continuation D C (fun n => (true,BondMirror.port n x)) (fun n => (false,BondMirror.port n y))
      (fun n => cubePort n x) (fun n => cubePort n (BondMirror.reflected y))
      (fun t n => BondRectangle.crossPair (fieldPrior t) β (BondMirror.port n x) (BondMirror.port n y) -
        ∫ s, fieldDot 3 x (BondMirror.reflected y) s ∂(cubeLaw β t n : Measure _)) _ _ hh
    · intro t _
      filter_upwards [cube_dot_real β t x (BondMirror.reflected y)] with n hn
      rw [rectangle_dot_real,hn,Complex.ofReal_sub]
    · exact high.mono fun _ H => H.rectangle x y hx hy

/-- The full volume sequence of the actual cube dot has a limit at each
positive real field. Identification of all spin laws is unnecessary. -/
theorem cube_dot_limit_of_complex_control {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    {h : ℝ} (hh : 0 < h) (x y : Site) :
    ∃ b : ℝ, Tendsto (fun n => ∫ s, fieldDot 3 x y s ∂(cubeLaw β h n : Measure _))
      atTop (𝓝 b) := by
  let F (n : ℕ) := finiteDot (cubeCoupling n β) (cubePort n x) (cubePort n y)
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.1 (LargeField.common_free_limit_eventually hβ)
  let a := max t₀ 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right t₀ 0]
  have high (t : ℝ) (ht : a < t) (_ : t < a+1) :
      ∃ l : ℂ, Tendsto (fun n => F n t) atTop (𝓝 l) := by
    have ht₀' : t₀ ≤ t := by dsimp [a] at ht; linarith [le_max_left t₀ 0]
    obtain ⟨P,_,_,H⟩ := ht₀ t ht₀'
    have pt := (ProbabilityMeasure.continuous_integral_continuousMap
      (fieldDot 3 x y)).continuousAt.tendsto.comp H.centered
    refine ⟨Complex.ofReal (∫ s, fieldDot 3 x y s ∂(P : Measure _)), ?_⟩
    apply (Complex.continuous_ofReal.continuousAt.tendsto.comp pt).congr'
    filter_upwards [cube_dot_real β t x y] with n eq using eq.symm
  obtain ⟨l,hl⟩ := RotorVitali.rightHalfPlane_vitali_limit_exists (F := F) ha
    (by linarith : a < a+1) (fun n => (entire_marked_uniform _ _).differentiableOn.div
      (entire_partition_uniform _).differentiableOn (C.nonzero n)) (fun K hc hs => by
        obtain ⟨M,hM⟩ := C.bounded K hc hs
        exact ⟨M,fun n z hz => hM n (cubePort n x) (cubePort n y) z hz⟩) high hh
  refine ⟨l.re,?_⟩
  have castlim : Tendsto
      (fun n => Complex.ofReal (∫ s, fieldDot 3 x y s ∂(cubeLaw β h n : Measure _))) atTop (𝓝 l) :=
    hl.congr' (cube_dot_real β h x y)
  simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp castlim

/-- A single fixed-spacing kernel is read by all cube dots and the
bond-centred rectangle dots at each strictly positive field. -/
theorem exists_common_free_dot_kernel {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    {h : ℝ} (hh : 0 < h) :
    ∃ g : Site → ℝ,
      (∀ x y, Tendsto (fun n => ∫ s, fieldDot 3 x y s ∂(cubeLaw β h n : Measure _))
        atTop (𝓝 (g (x-y)))) ∧
      ∀ x y : Site, 0 < x 0 → 0 < y 0 →
        Tendsto (fun n => BondRectangle.crossPair (fieldPrior h) β
          (BondMirror.port n x) (BondMirror.port n y)) atTop (𝓝 (g (x-BondMirror.reflected y))) := by
  choose g hg using fun y => cube_dot_limit_of_complex_control hβ C hh 0 y
  have H := freeDotComparison_of_complex_control hβ C D hh
  have cubes (x y : Site) : Tendsto (fun n => ∫ s, fieldDot 3 x y s ∂(cubeLaw β h n : Measure _))
      atTop (𝓝 (g (x-y))) := by
    simpa only [id_eq, sub_add_cancel, zero_add] using (H.translate x y).add (hg (x-y))
  refine ⟨g,cubes,fun x y hx hy => ?_⟩
  simpa only [id_eq, sub_add_cancel, zero_add] using
    (H.rectangle x y hx hy).add (cubes x (BondMirror.reflected y))

/-- Every iterated weak limit from the actual prescribed free cube laws
satisfies both the zero-field specification and the dot forms giving spatial
rotation. The outer sequence need not be monotone in field. -/
theorem gibbs_dotForms_of_complex_control {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    {h : ℕ → ℝ} (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    {P : ℕ → ProbabilityMeasure (SpinField 3)} {Q : ProbabilityMeasure (SpinField 3)}
    (hQ : Tendsto P atTop (𝓝 Q))
    (inner : ∀ j, ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
      Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) :
    IsNearestGibbs 3 β Q ∧ DotForms Q := by
  apply gibbs_dotForms_of_free_field_limits hβ (fun j => (hp j).le) hz hQ
  intro j
  obtain ⟨L,hL,hP⟩ := inner j
  exact ⟨L,hL,hP,(freeDotComparison_of_complex_control hβ C D (hp j)).subsequence hL⟩

/-- The finite cube integrals themselves supply all weak accumulation points
and a zero-field Gibbs probability with the physical dot reflection forms. -/
theorem exists_gibbs_dotForms_of_complex_control {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    {h : ℕ → ℝ} (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ (Q : ProbabilityMeasure (SpinField 3)) (u : ℕ → ℕ) (P : ℕ → ProbabilityMeasure (SpinField 3)),
      StrictMono u ∧ Tendsto (P ∘ u) atTop (𝓝 Q) ∧
      (∀ j, ∃ L : ℕ → ℕ, StrictMono L ∧ Tendsto (fun n => cubeLaw β (h j) (L n)) atTop (𝓝 (P j))) ∧
      IsNearestGibbs 3 β Q ∧ DotForms Q :=
  exists_free_field_limit_of_dot_comparisons hβ (fun j => (hp j).le) hz
    (fun j => freeDotComparison_of_complex_control hβ C D (hp j))

#print axioms freeDotComparison_of_complex_control
#print axioms finiteDot_eq_sum_coordinateRatios
#print axioms norm_finiteDot_le_three_mul
#print axioms cube_dot_limit_of_complex_control
#print axioms exists_common_free_dot_kernel
#print axioms gibbs_dotForms_of_complex_control
#print axioms exists_gibbs_dotForms_of_complex_control

end IsingScaling.Rotor.HeisenbergField.PositiveFieldContinuation
