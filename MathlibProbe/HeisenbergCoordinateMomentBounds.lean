import MathlibProbe.RotorHeisenbergComplexMomentBound
import MathlibProbe.HeisenbergShiftedCoordinateMagnetization

/-!
# Arbitrary coordinate moments of the finite Heisenberg Gibbs integral

Fix a finite graph, a complex background field H, a maximal order k, and a radius δ>0.
Suppose the original finite partition function does not vanish and every normalized
single-coordinate magnetization has modulus at most M throughout the coordinatewise
field neighborhood of radius kδ. The bound M and δ may be chosen uniformly in the
graph. For each list of j≤k site-coordinate marks let T be its product integral
divided by that same partition function.

Differentiating the numerator of T in a complex field t at one site-coordinate
inserts its real spin coordinate. Differentiating the denominator inserts its
magnetization. Thus the derivative of T at 0 is its new (j+1)-coordinate moment
minus T times the magnetization. If the existing offset is at most rδ and
r+j+1≤k, the whole next closed disk of radius δ stays in the order-j induction
region, including at a previously marked site. Cauchy's derivative bound costs
C_j/δ. The product term costs C_j M. Starting at C₀=1 this gives
C_j=(δ⁻¹+M)^j, uniformly in all sites and volumes. The coordinate marks below
are actual functions of the original spins, with all multiplicities retained.
-/

noncomputable section

open Set Metric MeasureTheory
namespace IsingScaling.Rotor.HeisenbergField.CoordinateMoments

open ComplexPartition

variable {V : Type*}

/-- The real unit vector defining a marked Cartesian spin coordinate. -/
def axis (i : Fin 3) : Spin 3 := ⟨EuclideanSpace.single i 1, by simp⟩

/-- The actual real spin monomial in an ordered list of labelled coordinates. -/
def coordinateProduct : List (V × Fin 3) → C(Config V, ℝ)
  | [] => 1
  | q :: qs => component q.1 (axis q.2) * coordinateProduct qs

@[simp] theorem coordinateProduct_apply (marks : List (V × Fin 3)) (s : Config V) :
    coordinateProduct marks s = (marks.map (fun q => (s q.1).val q.2)).prod := by
  induction marks with
  | nil => rfl
  | cons q qs ih =>
    simp [coordinateProduct, ih, component, axis, EuclideanSpace.inner_single_left]

variable [Fintype V]

/-- The finite normalized sphere-product Gibbs integral of the listed spin coordinates. -/
def ratio (J : V → V → ℝ) (H : ComplexPartition.Field V) (qs : List (V × Fin 3)) : ℂ :=
  marked J H (complexMark (coordinateProduct qs)) / partition J H

/-- On the real axis this is the original normalized finite Gibbs expectation
of the coordinate product with exactly the indicated multiplicities. -/
theorem ratio_uniform_real (J : V → V → ℝ) (h : ℝ) (qs : List (V × Fin 3)) :
    ratio J (uniform (h : ℂ)) qs = Complex.ofReal
      (∫ s, (qs.map (fun q => (s q.1).val q.2)).prod
        ∂((Measure.pi fun _ : V => fieldPrior h).tilted (PressureSelection.energy J))) := by
  simpa only [ratio, coordinateProduct_apply] using (real_uniform_ratio J h (coordinateProduct qs)).symm

theorem ratio_nil (J : V → V → ℝ) (H : ComplexPartition.Field V) (hZ : partition J H ≠ 0) :
    ratio J H [] = 1 := by
  have he : complexMark (coordinateProduct ([] : List (V × Fin 3))) = 1 := by ext s; simp [complexMark]
  simp only [ratio, he, marked, ContinuousMap.one_apply, mul_one]
  exact div_self hZ

private def direction (q : V × Fin 3) : ComplexPartition.Field V := by
  classical
  exact fun k i => if k = q.1 then ((axis q.2).val i : ℂ) else 0

omit [Fintype V] in
private theorem affine_direction (H : ComplexPartition.Field V) (q : V × Fin 3) (z : ℂ) :
    affine H (direction q) z = addAt H q.1 (axis q.2) z := by
  classical
  funext k i
  by_cases h : k = q.1 <;> simp [affine, direction, addAt, h]

private theorem eval_direction (q : V × Fin 3) :
    fieldEvaluation (direction q) = complexMark (component q.1 (axis q.2)) := by
  classical
  ext s
  simp only [fieldEvaluation, direction, ContinuousMap.coe_mk, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    complexMark, component, PiLp.inner_apply, Real.inner_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]

/-- Exact derivative of the physical quotient, valid also for a repeated mark. -/
theorem hasDerivAt_ratio (J : V → V → ℝ) (H : ComplexPartition.Field V) (q : V × Fin 3)
    (qs : List (V × Fin 3)) (hZ : partition J H ≠ 0) :
    HasDerivAt (fun z => ratio J (addAt H q.1 (axis q.2) z) qs)
      (ratio J H (q :: qs) - ratio J H qs * ComplexBounds.magnetization J H q.1 (axis q.2)) 0 := by
  have hm : complexMark (coordinateProduct qs) * complexMark (component q.1 (axis q.2)) =
      complexMark (coordinateProduct (q :: qs)) := by
    ext s
    simp [complexMark, coordinateProduct, mul_comm]
  have hn := hasDerivAt_marked_affine J H (direction q) (complexMark (coordinateProduct qs)) 0
  simp only [affine_direction, addAt_zero, eval_direction, hm] at hn
  have hd := hasDerivAt_partition_addAt J H q.1 (axis q.2) 0
  rw [addAt_zero] at hd
  have hquot := hn.fun_div hd (show partition J (addAt H q.1 (axis q.2) 0) ≠ 0 by
    simpa only [addAt_zero] using hZ)
  simp only [addAt_zero] at hquot
  unfold ratio ComplexBounds.magnetization
  apply hquot.congr_deriv
  field_simp [hZ]

private theorem diffOn_ratio (J : V → V → ℝ) (H : ComplexPartition.Field V) (q : V × Fin 3)
    (qs : List (V × Fin 3)) {S : Set ℂ} (hZ : ∀ z ∈ S, partition J (addAt H q.1 (axis q.2) z) ≠ 0) :
    DifferentiableOn ℂ (fun z => ratio J (addAt H q.1 (axis q.2) z) qs) S := by
  unfold ratio
  simp only [← affine_direction]
  exact (entire_marked_affine J H _ _).differentiableOn.div
    (entire_partition_affine J H _).differentiableOn (by simpa only [affine_direction] using hZ)

omit [Fintype V] in
private theorem addAt_sum (H P : ComplexPartition.Field V) (q : V × Fin 3) (z : ℂ) :
    addAt (H + P) q.1 (axis q.2) z = H + addAt P q.1 (axis q.2) z := by
  classical
  funext x i
  simp [addAt, add_assoc]

omit [Fintype V] in
private theorem offset_bound (P : ComplexPartition.Field V) (q : V × Fin 3)
    {r : ℕ} {δ : ℝ} (hP : ∀ x i, ‖P x i‖ ≤ (r : ℝ) * δ) {z : ℂ} (hz : ‖z‖ ≤ δ) :
    ∀ x i, ‖addAt P q.1 (axis q.2) z x i‖ ≤ ((r+1 : ℕ) : ℝ) * δ := by
  classical
  intro x i
  have hδ := (norm_nonneg z).trans hz
  have hs : ‖(if x = q.1 then z * (((axis q.2).val i : ℝ) : ℂ) else 0 : ℂ)‖ ≤ δ := by
    by_cases hx : x = q.1
    · by_cases hi : i = q.2
      · subst i
        simpa [hx, axis, PiLp.single_apply] using hz
      · simpa [hx, axis, PiLp.single_apply, hi, Ne.symm hi] using hδ
    · simpa [hx] using hδ
  exact (norm_add_le _ _).trans ((add_le_add (hP x i) hs).trans_eq (by push_cast; ring))

/-- At an existing offset of radius rδ the same bound holds whenever r+length≤k. -/
theorem norm_ratio_at_offset (J : V → V → ℝ) (H : ComplexPartition.Field V) (k : ℕ)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hphys : ∀ P : ComplexPartition.Field V, (∀ x i, ‖P x i‖ ≤ (k : ℝ) * δ) →
      partition J (H + P) ≠ 0 ∧
      ∀ x i, ‖ComplexBounds.magnetization J (H + P) x (axis i)‖ ≤ M)
    (qs : List (V × Fin 3)) {r : ℕ} (hr : r + qs.length ≤ k)
    (P : ComplexPartition.Field V) (hP : ∀ x i, ‖P x i‖ ≤ (r : ℝ) * δ) :
    ‖ratio J (H + P) qs‖ ≤ (δ⁻¹ + M) ^ qs.length := by
  induction qs generalizing r P with
  | nil =>
    have hr' : r ≤ k := by simpa using hr
    have hZ := (hphys P (fun x i => (hP x i).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hr') hδ.le))).1
    simp [ratio_nil J (H+P) hZ]
  | cons q qs ih =>
    have hr' : r ≤ k := by simp only [List.length_cons] at hr; omega
    have hroom : (r+1)+qs.length ≤ k := by simp only [List.length_cons] at hr; omega
    obtain ⟨hZ, hmag⟩ := hphys P (fun x i => (hP x i).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hr') hδ.le))
    let G := fun z => ratio J (addAt (H+P) q.1 (axis q.2) z) qs
    have hsup (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) δ) : ‖G z‖ ≤ (δ⁻¹ + M) ^ qs.length := by
      dsimp only [G]
      rw [addAt_sum]
      exact ih hroom _ (offset_bound P q hP (mem_closedBall_zero_iff.mp hz))
    have hnz (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) δ) :
        partition J (addAt (H+P) q.1 (axis q.2) z) ≠ 0 := by
      rw [addAt_sum]
      apply (hphys _ ?_).1
      have hh : r+1 ≤ k := by omega
      exact fun x i => (offset_bound P q hP (mem_closedBall_zero_iff.mp hz) x i).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hδ.le)
    have hd := (diffOn_ratio J (H+P) q qs hnz).diffContOnCl_ball Subset.rfl
    have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hd
      (fun z hz => hsup z (sphere_subset_closedBall hz))
    rw [(hasDerivAt_ratio J (H+P) q qs hZ).deriv] at hder
    have hbase : ‖ratio J (H+P) qs‖ ≤ (δ⁻¹+M)^qs.length := by
      simpa only [G, addAt_zero] using hsup 0 (mem_closedBall_self hδ.le)
    let factor := ratio J (H+P) qs * ComplexBounds.magnetization J (H+P) q.1 (axis q.2)
    calc ‖ratio J (H+P) (q::qs)‖ ≤ ‖ratio J (H+P) (q::qs) - factor‖ + ‖factor‖ :=
            norm_le_norm_sub_add _ _
         _ ≤ (δ⁻¹+M)^qs.length / δ + (δ⁻¹+M)^qs.length * M := by
            apply add_le_add hder
            dsimp only [factor]
            rw [norm_mul]
            exact mul_le_mul hbase (hmag q.1 q.2) (norm_nonneg _) (pow_nonneg (by positivity) _)
         _ = (δ⁻¹+M)^(q::qs).length := by rw [List.length_cons, pow_succ, div_eq_mul_inv]; ring

/-- Specialization to the unperturbed physical field, for arbitrary mark lists. -/
theorem norm_ratio_le (J : V → V → ℝ) (H : ComplexPartition.Field V) (k : ℕ)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hphys : ∀ P : ComplexPartition.Field V, (∀ x i, ‖P x i‖ ≤ (k : ℝ) * δ) →
      partition J (H + P) ≠ 0 ∧
      ∀ x i, ‖ComplexBounds.magnetization J (H + P) x (axis i)‖ ≤ M)
    (qs : List (V × Fin 3)) (hk : qs.length ≤ k) :
    ‖ratio J H qs‖ ≤ (δ⁻¹ + M) ^ qs.length := by
  simpa using norm_ratio_at_offset J H k hδ hM hphys qs (r := 0) (by simpa using hk) 0
    (fun x i => by simp)

/-- A uniform bound on every finite graph satisfying the physical finite Lee–Yang
cone theorem, for every marked site-coordinate list of the prescribed maximal degree
and every longitudinal field in a fixed compact subset of the right half-plane. -/
theorem compact_coordinate_moments (k : ℕ) {K : Set ℂ} (hk : IsCompact K)
    (hpos : ∀ h ∈ K, 0 < h.re) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {W : Type*} [Fintype W] (J : W → W → ℝ), FiniteLeeYangRotation.FiniteLeeYang J →
      ∀ h ∈ K, ∀ qs : List (W × Fin 3), qs.length ≤ k →
        ‖ratio J (uniform h) qs‖ ≤ C := by
  obtain ⟨δ, M, hδ, hM, hinput⟩ := ShiftedCoordinates.compact_coordinate_bounds k hk hpos
  let b : ℝ := max 1 (δ⁻¹ + M)
  have hb : 1 ≤ b := le_max_left _ _
  refine ⟨b^k, pow_nonneg (zero_le_one.trans hb) _, ?_⟩
  intro W _ J hLY h hh qs hlen
  have hd := norm_ratio_le J (uniform h) k hδ hM (fun P hP => by
    apply hinput J hLY h hh P
    intro x i
    exact (hP x i).trans (by nlinarith)) qs hlen
  exact hd.trans ((pow_le_pow_left₀ (by positivity) (le_max_right 1 (δ⁻¹+M)) _).trans
    (pow_le_pow_right₀ hb hlen))

end IsingScaling.Rotor.HeisenbergField.CoordinateMoments
