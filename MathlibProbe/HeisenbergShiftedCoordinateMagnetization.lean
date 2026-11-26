import MathlibProbe.RotorHeisenbergFiniteLeeYangRotation

/-!
# Uniform bounds for physical single-coordinate insertions in perturbed fields

On a compact set of longitudinal fields in the open right half-plane, a pointwise
complex neighbourhood of the uniform field works for every finite vertex set.
The three tilted axes have a common cone margin along the full interpolation
disk. A rectangular bound on the three coordinate errors costs at most nine
times its radius in the margin after an orthogonal change of basis.
-/

noncomputable section
open Metric Set MeasureTheory
open scoped InnerProductSpace Classical
namespace IsingScaling.Rotor.HeisenbergField.ShiftedCoordinates
open ComplexPartition ComplexBounds FieldCone FiniteLeeYangRotation

/-- Unit direction of the physical spin coordinate. -/
def axis (i : Fin 3) : Spin 3 := ⟨EuclideanSpace.single i 1, by simp⟩

variable {V : Type*}

private def scaleField (w : ℂ) (P : ComplexPartition.Field V) : ComplexPartition.Field V := fun x i => w * P x i

private theorem affine_perturbed (h₀ : ℝ) (h w : ℂ) (P : ComplexPartition.Field V) :
    affine (uniform h₀) ((uniform h + P) - uniform h₀) w =
      uniform (path h₀ h w) + scaleField w P := by
  funext x i
  by_cases hi : i = 0 <;> simp [affine, uniform, path, scaleField, hi]
  ring

private theorem coord_add (O : Frame) (A P : ComplexPartition.Field V) (x : V) (i : Fin 3) :
    coordinate O (A + P) x i = coordinate O A x i + coordinate O P x i := by
  simp [coordinate, rotateField, add_mul, Finset.sum_add_distrib]

private theorem coord_norm (O : Frame) (P : ComplexPartition.Field V) (x : V) (i : Fin 3) {d : ℝ}
    (hP : ∀ j, ‖P x j‖ ≤ d) : ‖coordinate O P x i‖ ≤ 3 * d := by
  change ‖∑ j : Fin 3, P x j * ((O (std i) j : ℝ) : ℂ)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ j : Fin 3, ‖P x j * ((O (std i) j : ℝ) : ℂ)‖ ≤ ∑ _j : Fin 3, d := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real]
      exact (mul_le_of_le_one_right (norm_nonneg _) (by
        simpa [std] using (PiLp.norm_apply_le (O (std i)) j))).trans (hP j)
    _ = 3 * d := by simp

private theorem margin_add_lower (O : Frame) (A P : ComplexPartition.Field V) (x : V) {d : ℝ}
    (hP : ∀ j, ‖P x j‖ ≤ d) : margin O A x - 9 * d ≤ margin O (A + P) x := by
  simp only [margin, coord_add, Complex.add_re]
  linarith [coord_norm O P x 0 hP, coord_norm O P x 1 hP, coord_norm O P x 2 hP,
    Complex.abs_re_le_norm (coordinate O P x 0), neg_abs_le (coordinate O P x 0).re,
    norm_add_le (coordinate O A x 1) (coordinate O P x 1),
    norm_add_le (coordinate O A x 2) (coordinate O P x 2)]

/-- Along the real-centred interpolation disk every physical perturbation in the
pointwise complex box lies in all three tilted cones. -/
theorem compact_tilted_disk (k : ℕ) {K : Set ℂ} (hk : IsCompact K)
    (hpos : ∀ h ∈ K, 0 < h.re) :
    ∃ (h₀ ρ δ : ℝ) (t : Tilt), 1 < ρ ∧ 0 < δ ∧
      ∀ h ∈ K, ∀ {W : Type*} (P : ComplexPartition.Field W),
      (∀ x i, ‖P x i‖ ≤ ((k : ℝ) + 1) * δ) →
      ∀ j : Fin 3, ∀ w : ℂ, ‖w‖ ≤ ρ →
        InCone (frame (t.axis j)) (affine (uniform h₀) ((uniform h + P) - uniform h₀) w) := by
  obtain ⟨h₀,ρ,a,M,_,hr,ha,hM,hpath⟩ := compact_path hk hpos
  have hr0 : 0 < ρ := by linarith
  let t : Tilt := ⟨min (1/2) (a/(4*M)),lt_min (by norm_num) (by positivity),min_le_left _ _⟩
  have ht : t.d * M ≤ a/4 := by
    have hl : t.d ≤ a/(4*M) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 4*M by positivity)).mp hl
    linarith
  let δ := a / (72 * ρ * ((k : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hk' : (k : ℝ) + 1 ≠ 0 := by positivity
  have hs : ρ * (((k : ℝ) + 1) * δ) = a/72 := by
    dsimp [δ]
    field_simp [hr0.ne', hk']
  refine ⟨h₀,ρ,δ,t,hr,hδ,?_⟩
  intro h hh W P hp j w hw x
  rw [affine_perturbed]
  have hfield (i : Fin 3) : ‖scaleField w P x i‖ ≤ a/72 := by
    change ‖w * P x i‖ ≤ _
    rw [norm_mul, ← hs]
    exact mul_le_mul hw (hp x i) (norm_nonneg _) hr0.le
  have hq := hpath h hh w hw
  have hbase := t.margin_uniform_lower j ha hq.1 hq.2 ht x
  have hmark := margin_add_lower (frame (t.axis j)) (uniform (path h₀ h w))
    (scaleField w P) x hfield
  linarith

/-- Change of real spin basis inside the actual complex normalized Gibbs integral. -/
theorem coordinate_magnetization_eq [Fintype V] (t : Tilt) (J : V → V → ℝ)
    (H : ComplexPartition.Field V) (x : V) (i : Fin 3) :
    magnetization J H x (axis i) =
      ∑ j : Fin 3, (t.coeff i j : ℂ) * magnetization J H x (t.axis j) := by
  have hc (s : Config V) : component x (axis i) s =
      ∑ j : Fin 3, t.coeff i j * component x (t.axis j) s := by
    simpa [component, axis, EuclideanSpace.inner_single_left] using t.coordinate_expansion (s x) i
  have hb (j : Fin 3) : Integrable
      (fun s => (t.coeff i j : ℂ) * (weight J H s * complexMark (component x (t.axis j)) s))
      (surfaceProduct V) :=
    (continuous_const.mul ((weight J H).continuous.mul (complexMark (component x (t.axis j))).continuous)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [magnetization, insertion_eq_marked, ← mul_div_assoc, ← Finset.sum_div]
  congr 1
  unfold marked
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun j _ => hb j)]
  apply integral_congr_ae
  filter_upwards [] with s
  change weight J H s * ((component x (axis i) s : ℝ) : ℂ) = _
  rw [hc, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [complexMark,mul_left_comm]

/-- One radius and one magnetization bound work at every site, including coincident
marks, throughout all finite graphs satisfying the physical Lee–Yang cone. -/
theorem compact_coordinate_bounds (k : ℕ) {K : Set ℂ} (hk : IsCompact K)
    (hpos : ∀ h ∈ K, 0 < h.re) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
      ∀ {W : Type*} [Fintype W] (J : W → W → ℝ), FiniteLeeYang J →
      ∀ h ∈ K, ∀ P : ComplexPartition.Field W, (∀ x i, ‖P x i‖ ≤ ((k : ℝ) + 1) * δ) →
        partition J (uniform h + P) ≠ 0 ∧
        ∀ x i, ‖magnetization J (uniform h + P) x (axis i)‖ ≤ B := by
  obtain ⟨h₀,ρ,δ,t,hρ,hδ,cones⟩ := compact_tilted_disk k hk hpos
  let M := 1 + 6/(ρ-1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let cost (i : Fin 3) := ∑ j : Fin 3, |t.coeff i j|
  have hc (i : Fin 3) : 0 ≤ cost i := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨δ, (∑ i, cost i)*M, hδ, mul_nonneg (Finset.sum_nonneg fun i _ => hc i) hM, ?_⟩
  intro W _ J hLY h hh P hP
  constructor
  · have hC := cones h hh P hP 0 1 (by simpa using hρ.le)
    have hterminal : affine (uniform (V := W) h₀) ((uniform h + P) - uniform h₀) 1 = uniform h + P := by
      funext x i
      simp [affine]
    exact partition_ne_zero_of_cone J hLY _ _ (hterminal ▸ hC)
  · intro x i
    have hmag (j : Fin 3) : ‖magnetization J (uniform h + P) x (t.axis j)‖ ≤ M := by
      apply norm_magnetization_of_nonvanishing J h₀ _ _ _ hρ
      intro w hw v hv
      apply partition_ne_zero_of_cone J hLY (frame (t.axis j))
      intro y
      rw [margin_axis_shift]
      have hC := cones h hh P hP j w (mem_ball_zero_iff.mp hw).le y
      have hadd : 0 ≤ if y = x then v.re else (0 : ℝ) := by split_ifs <;> positivity
      linarith
    rw [coordinate_magnetization_eq t]
    apply (norm_sum_le _ _).trans
    calc
      ∑ j : Fin 3, ‖(t.coeff i j : ℂ) * magnetization J (uniform h + P) x (t.axis j)‖
          ≤ cost i * M := by
        rw [show cost i = ∑ j : Fin 3, |t.coeff i j| from rfl, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j _
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hmag j) (abs_nonneg _)
      _ ≤ (∑ j, cost j) * M :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)) hM

#print axioms compact_tilted_disk
#print axioms coordinate_magnetization_eq
#print axioms compact_coordinate_bounds

end IsingScaling.Rotor.HeisenbergField.ShiftedCoordinates
