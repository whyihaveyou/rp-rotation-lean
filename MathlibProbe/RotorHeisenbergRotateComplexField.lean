import MathlibProbe.RotorHeisenbergComplexPartition

/-!
# Common spin basis for the finite Heisenberg complex field

An orthogonal map has physical basis vectors as its columns. Expressing a
complex field in this basis applies the transpose of that real matrix. Changing
all spin variables in the original product-sphere integral preserves the
finite-volume partition function and transports arbitrary continuous marks.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace
namespace IsingScaling.Rotor.HeisenbergField.ComplexPartition
open PressureSelection

abbrev SpinSpace := EuclideanSpace ℝ (Fin 3)
abbrev SpinBasis := SpinSpace ≃ₗᵢ[ℝ] SpinSpace

variable {V : Type*}

/-- The transpose of the real spin basis acts complex-linearly on the field.
The physical basis vectors are the columns of the orthogonal map. -/
def rotateField (O : SpinBasis) (H : Field V) : Field V :=
  fun x i => ∑ j : Fin 3, H x j * ((O (EuclideanSpace.single i 1) j : ℝ) : ℂ)

private theorem coord_transpose (O : SpinBasis) (v : SpinSpace) (j : Fin 3) :
    O v j = ⟪O.symm (EuclideanSpace.single j 1), v⟫_ℝ := by
  simpa only [O.apply_symm_apply,EuclideanSpace.inner_single_left,map_one,one_mul] using
    O.inner_map_map (O.symm (EuclideanSpace.single j 1)) v

private theorem matrix_coord (O : SpinBasis) (v : SpinSpace) (j : Fin 3) :
    O v j = ∑ i : Fin 3, O (EuclideanSpace.single i 1) j * v i := by
  have col (i : Fin 3) : O (EuclideanSpace.single i 1) j = O.symm (EuclideanSpace.single j 1) i := by
    simpa [EuclideanSpace.inner_single_right] using coord_transpose O (EuclideanSpace.single i 1) j
  rw [coord_transpose]
  simp only [PiLp.inner_apply,Real.inner_apply,col]

private theorem transpose_coord (O : SpinBasis) (v : SpinSpace) (i : Fin 3) :
    ∑ j : Fin 3, v j * O (EuclideanSpace.single i 1) j = O.symm v i := by
  calc
    _ = ⟪v, O (EuclideanSpace.single i 1)⟫_ℝ := by simp only [PiLp.inner_apply,Real.inner_apply]
    _ = ⟪O.symm v, EuclideanSpace.single i 1⟫_ℝ := by
      simpa only [O.apply_symm_apply] using O.inner_map_map (O.symm v) (EuclideanSpace.single i 1)
    _ = _ := by simp [EuclideanSpace.inner_single_right]

theorem fieldEvaluation_rotateField [Fintype V] (O : SpinBasis) (H : Field V) (s : Config V) :
    fieldEvaluation (rotateField O H) s = fieldEvaluation H (InternalOrthogonal.rotate O s) := by
  change (∑ x : V, ∑ i : Fin 3, (rotateField O H) x i * ((s x).val i : ℂ)) =
    ∑ x : V, ∑ j : Fin 3, H x j * ((O (s x).val j : ℝ) : ℂ)
  apply Finset.sum_congr rfl
  intro x _
  simp only [rotateField,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrix_coord O (s x).val j]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem weight_rotateField [Fintype V] (J : V → V → ℝ) (O : SpinBasis) (H : Field V) (s : Config V) :
    weight J (rotateField O H) s = weight J H (InternalOrthogonal.rotate O s) := by
  change Complex.exp ((PressureSelection.energy J s : ℝ) + fieldEvaluation (rotateField O H) s) =
    Complex.exp ((PressureSelection.energy J (InternalOrthogonal.rotate O s) : ℝ) +
      fieldEvaluation H (InternalOrthogonal.rotate O s))
  rw [InternalOrthogonal.energy_rotate,fieldEvaluation_rotateField]

private theorem surfaceProduct_rotate [Fintype V] (O : SpinBasis) :
    MeasurePreserving (InternalOrthogonal.rotate (V := V) O) (surfaceProduct V) (surfaceProduct V) :=
  measurePreserving_pi (fun _ : V => SiteReflection.surfacePrior 3)
    (fun _ : V => SiteReflection.surfacePrior 3)
    (f := fun _ s => SiteReflection.SphereSign.sphereMap O s)
    (fun _ => SiteReflection.SphereSign.sphereMap_preserving O)

theorem partition_rotateField [Fintype V] (J : V → V → ℝ) (O : SpinBasis) (H : Field V) :
    partition J (rotateField O H) = partition J H := by
  unfold partition
  simp_rw [weight_rotateField]
  exact (surfaceProduct_rotate O).hasLaw.integral_comp (weight J H).continuous.aestronglyMeasurable

theorem marked_rotateField [Fintype V] (J : V → V → ℝ) (O : SpinBasis) (H : Field V)
    (F : C(Config V,ℂ)) :
    marked J (rotateField O H) (F.comp (InternalOrthogonal.rotate O)) = marked J H F := by
  unfold marked
  simp_rw [weight_rotateField,ContinuousMap.comp_apply]
  exact (surfaceProduct_rotate O).hasLaw.integral_comp
    ((weight J H).continuous.mul F.continuous).aestronglyMeasurable

/-- A physical one-site perturbation has coordinates in the rotated basis
given by the inverse real rotation of its unit spin direction. -/
theorem rotateField_addAt (O : SpinBasis) (H : Field V) (x : V) (u : Spin 3) (w : ℂ) :
    rotateField O (addAt H x u w) =
      addAt (rotateField O H) x (SiteReflection.SphereSign.sphereMap O.symm u) w := by
  classical
  funext y i
  by_cases h : y = x
  · subst y
    change (∑ j : Fin 3, (H x j + (if x = x then w * (u.val j : ℂ) else 0)) *
      ((O (EuclideanSpace.single i 1) j : ℝ) : ℂ)) =
      (∑ j : Fin 3, H x j * ((O (EuclideanSpace.single i 1) j : ℝ) : ℂ)) +
      (if x = x then w * ((O.symm u.val i : ℝ) : ℂ) else 0)
    simp only [ite_true,add_mul,Finset.sum_add_distrib]
    congr 1
    rw [← transpose_coord O u.val i]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]
  · simp [rotateField,addAt,h]

theorem rotateField_addAt_rotatedDirection (O : SpinBasis) (H : Field V) (x : V) (u : Spin 3)
    (w : ℂ) : rotateField O (addAt H x (SiteReflection.SphereSign.sphereMap O u) w) =
      addAt (rotateField O H) x u w := by
  rw [rotateField_addAt]
  have hu : SiteReflection.SphereSign.sphereMap O.symm (SiteReflection.SphereSign.sphereMap O u) =
      u := Subtype.ext (O.symm_apply_apply u.val)
  rw [hu]

end IsingScaling.Rotor.HeisenbergField.ComplexPartition
