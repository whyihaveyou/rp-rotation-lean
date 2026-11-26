import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

/-!
# Reflection of the inverse of a finite precision matrix

The open positive half and its reflected copy are indexed by the same finite
type. A third finite type indexes the sites fixed by the reflection, and may
be empty. The input on the open half is positivity of the negative
cross-block of the precision.

For a test f on the closed positive half, the odd source f−Rf has an odd
maximizer (v,−v,0) in the Gaussian quadratic variational formula. The even
source f+Rf is tested at (v,v,0). The linear terms agree even when f has
nonzero wall values. Replacing the odd trial by the even one decreases the
precision energy by four times the quadratic form of its negative cross-block.
The difference of the two inverse energies is four times the reflected
covariance tested by f.
-/

namespace IsingScaling.Rotor.PrecisionReflection

open Matrix
open scoped BigOperators

section Variational

variable {T : Type*} [Fintype T] [DecidableEq T]
variable {Q : Matrix T T ℝ}

omit [DecidableEq T] in
private theorem bilinear_symm (h : Q.IsHermitian) (x y : T → ℝ) :
    x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  have hs : Qᵀ = Q := (Matrix.isHermitian_iff_isSymm.mp h).eq
  simpa only [hs] using Matrix.dotProduct_transpose_mulVec Q x y

private theorem solve_precision (h : Q.PosDef) (a : T → ℝ) :
    Q *ᵥ (Q⁻¹ *ᵥ a) = a := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q (Q.isUnit_iff_isUnit_det.mp h.isUnit),
    Matrix.one_mulVec]

private theorem variational_le (h : Q.PosDef) (a z : T → ℝ) :
    2 * (a ⬝ᵥ z) - z ⬝ᵥ (Q *ᵥ z) ≤ a ⬝ᵥ (Q⁻¹ *ᵥ a) := by
  let y := Q⁻¹ *ᵥ a
  have hy : Q *ᵥ y = a := solve_precision h a
  have hp : 0 ≤ (y-z) ⬝ᵥ (Q *ᵥ (y-z)) := by
    simpa using h.posSemidef.dotProduct_mulVec_nonneg (y-z)
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    bilinear_symm h.isHermitian y z, hy, dotProduct_comm z a, dotProduct_comm y a] at hp
  change 2 * (a ⬝ᵥ z) - z ⬝ᵥ (Q *ᵥ z) ≤ a ⬝ᵥ y
  linarith

end Variational

variable {V W : Type*}

abbrev Sites (V W : Type*) := V ⊕ (V ⊕ W)

/-- Interchange the two open halves and fix the wall pointwise. -/
def mirror : Sites V W → Sites V W
  | .inl v => .inr (.inl v)
  | .inr (.inl v) => .inl v
  | .inr (.inr w) => .inr (.inr w)

@[simp] theorem mirror_mirror (i : Sites V W) : mirror (mirror i) = i := by
  rcases i with i | i
  · rfl
  · rcases i with i | w <;> rfl

private def mirrorEquiv : Sites V W ≃ Sites V W :=
  ⟨mirror, mirror, mirror_mirror, mirror_mirror⟩

def reflect (v : Sites V W → ℝ) (i : Sites V W) : ℝ := v (mirror i)

private def openTest (x : V → ℝ) : Sites V W → ℝ
  | .inl i => x i
  | .inr _ => 0

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The sign convention is the one for walk precision Q = M I − A. -/
def negativeCross (Q : Matrix (Sites V W) (Sites V W) ℝ) : Matrix V V ℝ :=
  fun i j => -Q (.inl i) (.inr (.inl j))

omit [DecidableEq V] [DecidableEq W] in
private theorem equivariant_mulVec {Q : Matrix (Sites V W) (Sites V W) ℝ}
    (h : ∀ i j, Q (mirror i) (mirror j) = Q i j) (v : Sites V W → ℝ) :
    Q *ᵥ reflect v = reflect (Q *ᵥ v) := by
  funext i
  change (∑ j, Q i j * v (mirror j)) = ∑ j, Q (mirror i) j * v j
  calc
    _ = ∑ j, Q (mirror i) (mirror j) * v (mirror j) := by simp only [h]
    _ = _ := Equiv.sum_comp (mirrorEquiv (V:=V) (W:=W))
      (fun j => Q (mirror i) j * v j)

omit [DecidableEq V] [DecidableEq W] in
private theorem open_cross (Q : Matrix (Sites V W) (Sites V W) ℝ) (v : V → ℝ) :
    openTest v ⬝ᵥ (Q *ᵥ reflect (openTest v)) = -(v ⬝ᵥ (negativeCross Q *ᵥ v)) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, openTest, reflect, mirror,
    negativeCross, Finset.sum_neg_distrib]

/-- Arbitrary signed tests on the open half together with its fixed wall
have nonnegative reflected covariance for the inverse precision. -/
theorem inverse_reflected_nonneg {Q : Matrix (Sites V W) (Sites V W) ℝ} (hQ : Q.PosDef)
    (hinv : ∀ i j, Q (mirror i) (mirror j) = Q i j)
    (hcross : (negativeCross Q).PosSemidef)
    (f : Sites V W → ℝ) (hf : ∀ i, f (.inr (.inl i)) = 0) :
    0 ≤ f ⬝ᵥ (Q⁻¹ *ᵥ reflect f) := by
  let a := f - reflect f
  let u := Q⁻¹ *ᵥ a
  have hu : Q *ᵥ u = a := solve_precision hQ a
  have ha : reflect a = -a := by
    funext i
    simp [a, reflect]
  have huodd : reflect u = -u := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hQ.isUnit)
    rw [equivariant_mulVec hinv u, Matrix.mulVec_neg, hu, ha]
  let v : V → ℝ := fun j => u (.inl j)
  let x : Sites V W → ℝ := openTest v
  let y := reflect x
  have hdec : u = x - y := by
    funext i
    rcases i with j | i
    · simp [x, y, v, openTest, reflect, mirror]
    · rcases i with j | w
      · have hj := congrFun huodd (.inl j)
        change u (.inr (.inl j)) = -u (.inl j) at hj
        simpa [x, y, v, openTest, reflect, mirror] using hj
      · have hw := congrFun huodd (.inr (.inr w))
        change u (.inr (.inr w)) = -u (.inr (.inr w)) at hw
        simp [x, y, openTest, reflect, mirror]
        linarith
  have hlin₁ : f ⬝ᵥ y = 0 := by
    simp [dotProduct, Fintype.sum_sum_type, x, y, openTest, reflect, mirror, hf]
  have hlin₂ : reflect f ⬝ᵥ x = 0 := by
    simp [dotProduct, Fintype.sum_sum_type, x, openTest, reflect, mirror, hf]
  have hlin : (f + reflect f) ⬝ᵥ (x+y) = a ⬝ᵥ u := by
    rw [hdec]
    simp only [a, add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, hlin₁, hlin₂]
    ring
  have hxy : x ⬝ᵥ (Q *ᵥ y) ≤ 0 := by
    have h := hcross.dotProduct_mulVec_nonneg v
    rw [show x ⬝ᵥ (Q *ᵥ y) = -(v ⬝ᵥ (negativeCross Q *ᵥ v)) from open_cross Q v]
    simpa using h
  have htrial : (x+y) ⬝ᵥ (Q *ᵥ (x+y)) ≤ u ⬝ᵥ (Q *ᵥ u) := by
    rw [hdec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
      dotProduct_add, dotProduct_sub, bilinear_symm hQ.isHermitian y x]
    linarith
  have hv := variational_le hQ (f + reflect f) (x+y)
  rw [hlin] at hv
  rw [hu, dotProduct_comm u a] at htrial
  have hcomp : (f-reflect f) ⬝ᵥ (Q⁻¹ *ᵥ (f-reflect f)) ≤
      (f+reflect f) ⬝ᵥ (Q⁻¹ *ᵥ (f+reflect f)) := by
    change a ⬝ᵥ u ≤ _
    linarith
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, bilinear_symm hQ.inv.isHermitian (reflect f) f] at hcomp
  linarith

/-- Include the closed half into the whole finite system. -/
def closedSite : V ⊕ W → Sites V W
  | .inl i => .inl i
  | .inr w => .inr (.inr w)

private def closedTest (b : V ⊕ W → ℝ) : Sites V W → ℝ
  | .inl i => b (.inl i)
  | .inr (.inl _) => 0
  | .inr (.inr w) => b (.inr w)

/-- The covariance at a positive-half point and a reflected positive-half
point, including every wall point on both sides of the matrix. -/
def closedReflected (C : Matrix (Sites V W) (Sites V W) ℝ) : Matrix (V ⊕ W) (V ⊕ W) ℝ :=
  fun i j => C (closedSite i) (mirror (closedSite j))

/-- Matrix form of the inverse reflection theorem on the closed half. -/
theorem inverse_closedReflected_posSemidef {Q : Matrix (Sites V W) (Sites V W) ℝ}
    (hQ : Q.PosDef) (hinv : ∀ i j, Q (mirror i) (mirror j) = Q i j)
    (hcross : (negativeCross Q).PosSemidef) : (closedReflected Q⁻¹).PosSemidef := by
  let e := mirrorEquiv (V:=V) (W:=W)
  have hsub : Q.submatrix e e = Q := Matrix.ext fun i j => hinv i j
  have hi : ∀ i j, Q⁻¹ (mirror i) (mirror j) = Q⁻¹ i j := by
    have h := Matrix.inv_submatrix_equiv Q e e
    rw [hsub] at h
    exact fun i j => congr_fun (congr_fun h.symm i) j
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    change star (Q⁻¹ (closedSite j) (mirror (closedSite i))) =
      Q⁻¹ (closedSite i) (mirror (closedSite j))
    rw [hQ.inv.isHermitian.apply]
    simpa using hi (closedSite i) (mirror (closedSite j))
  · intro b
    have h := inverse_reflected_nonneg hQ hinv hcross (closedTest b) (fun _ => rfl)
    simpa [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, closedTest, reflect, mirror,
      closedReflected, closedSite] using h

#print axioms inverse_reflected_nonneg
#print axioms inverse_closedReflected_posSemidef

section RowBounds

variable {T : Type*} [Fintype T] [DecidableEq T]

private theorem eigenvalue_lower_row {S : Matrix T T ℝ} (hs : S.IsHermitian) (i : T) :
    ∃ k, S k k - ∑ j ∈ Finset.univ.erase k, ‖S k j‖ ≤ hs.eigenvalues i := by
  have he : Module.End.HasEigenvalue S.toLin' (hs.eigenvalues i) :=
    .of_mem_spectrum (by simpa only [Matrix.spectrum_toLin'] using hs.eigenvalues_mem_spectrum_real i)
  obtain ⟨k,hk⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall, Real.dist_eq] at hk
  exact ⟨k, by linarith [(abs_le.mp hk).1]⟩

private theorem posDef_of_row_bound {S : Matrix T T ℝ} (hs : S.IsHermitian)
    (hrow : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖S k j‖ < S k k) : S.PosDef := by
  apply hs.posDef_iff_eigenvalues_pos.mpr
  intro i
  obtain ⟨k,hk⟩ := eigenvalue_lower_row hs i
  linarith [hrow k]

private theorem posSemidef_of_row_bound {S : Matrix T T ℝ} (hs : S.IsHermitian)
    (hrow : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖S k j‖ ≤ S k k) : S.PosSemidef := by
  apply hs.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hs.eigenvalues i
  obtain ⟨k,hk⟩ := eigenvalue_lower_row hs i
  linarith [hrow k]

end RowBounds

/-- Precision of a finite massive symmetric walk, multiplicities included. -/
def walkPrecision (m : ℝ) (A : Matrix (Sites V W) (Sites V W) ℝ) :
    Matrix (Sites V W) (Sites V W) ℝ := Matrix.diagonal (fun _ => m) - A

/-- A strict mass gap for a symmetric nonnegative finite walk makes its
precision positive definite. Self-loops are permitted. -/
theorem walkPrecision_posDef {A : Matrix (Sites V W) (Sites V W) ℝ} {m : ℝ}
    (hsym : A.IsHermitian) (hnon : ∀ i j, 0 ≤ A i j) (hmass : ∀ i, ∑ j, A i j < m) :
    (walkPrecision m A).PosDef := by
  apply posDef_of_row_bound ((Matrix.isHermitian_diagonal (fun _ => m)).sub hsym)
  intro i
  change (∑ j ∈ Finset.univ.erase i, ‖walkPrecision m A i j‖) < walkPrecision m A i i
  have hsum : ∑ j ∈ Finset.univ.erase i, ‖walkPrecision m A i j‖ = ∑ j ∈ Finset.univ.erase i, A i j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij := (Finset.ne_of_mem_erase hj).symm
    simp [walkPrecision, hij, Real.norm_eq_abs, abs_of_nonneg (hnon i j)]
  rw [hsum]
  have he := Finset.sum_erase_add _ (fun j => A i j) (Finset.mem_univ i)
  change _ < (Matrix.diagonal (fun _ : Sites V W => m) i i - A i i)
  rw [Matrix.diagonal_apply_eq]
  linarith [hmass i]

/-- Sufficient conditions directly on the finite walk weights. The mass exceeds every
full row sum. On each open-half seam, the direct reflected weight dominates all the
other reflected weights in its row. Rows away from the seam may vanish identically. -/
theorem massive_walk_closedReflected_posSemidef {A : Matrix (Sites V W) (Sites V W) ℝ}
    {m : ℝ} (hsym : A.IsHermitian) (hnon : ∀ i j, 0 ≤ A i j)
    (hinv : ∀ i j, A (mirror i) (mirror j) = A i j)
    (hmass : ∀ i, ∑ j, A i j < m)
    (hseam : ∀ i : V, ∑ j ∈ Finset.univ.erase i, A (.inl i) (.inr (.inl j))
        ≤ A (.inl i) (.inr (.inl i))) :
    (closedReflected (walkPrecision m A)⁻¹).PosSemidef := by
  let Q := walkPrecision m A
  let K : Matrix V V ℝ := fun i j => A (.inl i) (.inr (.inl j))
  have hentry : negativeCross Q = K := by
    ext i j
    simp [negativeCross, Q, walkPrecision, K]
  have hQp : Q.PosDef := walkPrecision_posDef hsym hnon hmass
  apply inverse_closedReflected_posSemidef hQp
  · intro i j
    have hiff : mirror i = mirror j ↔ i = j := mirrorEquiv.injective.eq_iff
    simp [Q, walkPrecision, Matrix.diagonal_apply, hiff, hinv]
  · rw [hentry]
    apply posSemidef_of_row_bound
    · apply Matrix.IsHermitian.ext
      intro i j
      change star (A (.inl j) (.inr (.inl i))) = A (.inl i) (.inr (.inl j))
      rw [hsym.apply]
      exact hinv (.inl i) (.inr (.inl j))
    · intro i
      simpa [K, Real.norm_eq_abs, abs_of_nonneg (hnon _ _)] using hseam i

#print axioms massive_walk_closedReflected_posSemidef

section SeamBlocks

variable {T D : Type*} [Fintype T] [DecidableEq T] [Fintype D]

private def pairEntry (e : T ≃ T) (i j : T) : ℝ :=
  (if j = e i then 1 else 0) + (if i = e j then 1 else 0)

private def weightedPairs (shift : D → T ≃ T) (w : D → ℝ) : Matrix T T ℝ :=
  fun i j => ∑ d, w d * pairEntry (shift d) i j

/-- A tangential lump with its two reverse orientations on the actual finite
permutation orbits. Coincident destinations are counted with multiplicity. -/
def seamBlock (a : ℝ) (shift : D → T ≃ T) (w : D → ℝ) : Matrix T T ℝ :=
  Matrix.diagonal (fun _ => a) + weightedPairs shift w

private theorem pair_row (e : T ≃ T) (i : T) : ∑ j, pairEntry e i j = 2 := by
  have he (j : T) : i = e j ↔ j = e.symm i := by
    constructor
    · intro h
      rw [h, e.symm_apply_apply]
    · rintro rfl
      exact (e.apply_symm_apply _).symm
  simp [pairEntry, Finset.sum_add_distrib, he]
  norm_num

/-- Each weighted forward/backward permutation contributes exactly twice its
coefficient to the row sum, including shifts that coincide on short tori. -/
theorem weighted_seam_posSemidef (a : ℝ) (shift : D → T ≃ T) (w : D → ℝ)
    (hw : ∀ d, 0 ≤ w d) (ha : 2 * ∑ d, w d ≤ a) : (seamBlock a shift w).PosSemidef := by
  let A := weightedPairs shift w
  have hn (i j : T) : 0 ≤ A i j := by
    apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg (hw d)
    unfold pairEntry
    split_ifs <;> norm_num
  have hs : A.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (∑ d, w d * pairEntry (shift d) j i) = ∑ d, w d * pairEntry (shift d) i j
    rw [star_trivial]
    exact Finset.sum_congr rfl fun d _ => congrArg (w d * ·) (add_comm _ _)
  have hrow (i : T) : ∑ j, A i j = 2 * ∑ d, w d := by
    change (∑ j, ∑ d, w d * pairEntry (shift d) i j) = _
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, pair_row, mul_comm]
  apply posSemidef_of_row_bound ((Matrix.isHermitian_diagonal (fun _ => a)).add hs)
  intro i
  change (∑ j ∈ Finset.univ.erase i, ‖seamBlock a shift w i j‖) ≤ seamBlock a shift w i i
  have hoff : (∑ j ∈ Finset.univ.erase i, ‖seamBlock a shift w i j‖)
      = ∑ j ∈ Finset.univ.erase i, A i j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij := (Finset.ne_of_mem_erase hj).symm
    simp [seamBlock, A, hij, Real.norm_eq_abs, abs_of_nonneg (hn i j)]
  rw [hoff]
  have he := Finset.sum_erase_add _ (fun j => A i j) (Finset.mem_univ i)
  rw [hrow] at he
  change _ ≤ Matrix.diagonal (fun _ : T => a) i i + A i i
  rw [Matrix.diagonal_apply_eq]
  linarith [hn i i]

/-- The coordinate-bond seam (VM-2) with two tangential translations, the two
mixed translations, and all four of their reverses. -/
theorem coordinate_bond_seam_posSemidef (e₁ e₂ : T ≃ T) {a b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : 4*b+4*c ≤ a) :
    (seamBlock a ![e₁, e₂, e₁.trans e₂, e₁.trans e₂.symm] ![b,b,c,c]).PosSemidef := by
  apply weighted_seam_posSemidef
  · intro d
    fin_cases d <;> first | exact hb | exact hc
  · simp [Fin.sum_univ_succ]
    linarith

/-- The oblique site seam (VM-3) with two opposite third-coordinate steps
on each admissible tangential line. -/
theorem oblique_site_seam_posSemidef (e₃ : T ≃ T) {b c : ℝ}
    (hc : 0 ≤ c) (hb : 2*c ≤ b) :
    (seamBlock b (fun _ : Unit => e₃) (fun _ => c)).PosSemidef := by
  apply weighted_seam_posSemidef
  · exact fun _ => hc
  · simpa using hb

end SeamBlocks

#print axioms coordinate_bond_seam_posSemidef
#print axioms oblique_site_seam_posSemidef

end IsingScaling.Rotor.PrecisionReflection

