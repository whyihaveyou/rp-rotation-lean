import MathlibProbe.RotorPeriodicGibbsReflection
import MathlibProbe.RotorPeriodicCouplingMixture

/-! # Lifting a finite lattice half-space test at every periodic root

The adapted torus has normal coordinate x₁+x₂ modulo 2L. Translate the
chosen root to the chart origin by its negative lattice representative.
In this chart every displacement z has precisely the coordinates of z;
the lattice map (x₁,x₂,x₃) ↦ (−x₂,−x₁,x₃) acts by the physical chart
mirror, including its tangential shear. If the test has 0 ≤ x₁+x₂ < L,
positive normals are in the open half and zero normals are fixed site by
site. Conjugating back gives one mirror for the whole test family and
retains every boundary insertion. On the ordinary torus the same
argument uses the normal x₁ and the physical site or bond mirror.
Only the largest normal of the finite test enters the side cutoff.
-/

noncomputable section

namespace IsingScaling.Rotor.PressureSelection.PeriodicMirrorLift

open IsingScaling
open PhysicalSplit

/-- Lattice site mirror with normal (1,1,0), in the physical adapted chart. -/
def diagonal (z : Site) : Site := ![-z 1,-z 0,z 2]

/-- Lattice site mirror in the coordinate plane through the origin. -/
def axis (z : Site) : Site := ![-z 0,z 1,z 2]

/-- Lattice bond mirror between the coordinate planes at zero and one. -/
def bond (z : Site) : Site := ![1-z 0,z 1,z 2]

private theorem diagChart_neg (L : ℕ) (z : Site) :
    DiagonalSeam.coords L (-z) = -DiagonalSeam.coords L z := by
  apply Prod.ext
  · change ((-z 0 + -z 1 : ℤ) : ZMod (2*L)) = -((z 0 + z 1 : ℤ) : ZMod (2*L))
    push_cast
    abel
  · apply Prod.ext <;> simp [DiagonalSeam.coords]

/-- In the translated frame each actual displacement has its lattice chart. -/
private theorem diagCentered {L : ℕ} [NeZero L] (o : Seam.Site L) (z : Site) :
    DiagonalSeam.siteCoords
      (Seam.adaptedDestination (-Seam.representative o) (Seam.adaptedDestination z o)) =
      DiagonalSeam.coords L z := by
  rw [DiagonalSeam.coords_adaptedDestination,DiagonalSeam.coords_adaptedDestination,diagChart_neg]
  change DiagonalSeam.coords L (Seam.representative o) + _ + -_ = _
  abel

private theorem val_int_nonneg {L : ℕ} [NeZero L] {n : ℤ} (h₀ : 0 ≤ n) (hL : n < (L : ℤ)) :
    ((n : ZMod L).val : ℤ) = n := by
  lift n to ℕ using h₀
  rw [Int.cast_natCast, ZMod.val_natCast_of_lt (by exact_mod_cast hL)]

theorem diagonal_at_root {L : ℕ} [NeZero L] (o : Seam.Site L) (z : Site) :
    (shiftedAdaptedHalf L (-Seam.representative o)).refl (Seam.adaptedDestination z o) =
      Seam.adaptedDestination (diagonal z) o := by
  let d := -Seam.representative o
  let u := Seam.adaptedDestination z o
  let v := Seam.adaptedDestination (diagonal z) o
  have hc : DiagonalSeam.adaptedMirror L (Seam.adaptedDestination d u) = Seam.adaptedDestination d v := by
    apply (DiagonalSeam.siteCoords_bijective L).injective
    rw [DiagonalSeam.coords_adaptedMirror,diagCentered o z,diagCentered o (diagonal z)]
    exact (DiagonalSeam.coords_geometric_mirror L z).symm
  change Seam.adaptedDestination (-d) (DiagonalSeam.adaptedMirror L (Seam.adaptedDestination d u)) = v
  rw [hc, ← PeriodizedWalk.adapted_add L, add_neg_cancel, PeriodizedWalk.adapted_zero]

theorem diagonal_closed_at_root {L : ℕ} [NeZero L] (o : Seam.Site L) (z : Site)
    (h₀ : 0 ≤ z 0+z 1) (hL : z 0+z 1 < (L : ℤ)) :
    (shiftedAdaptedHalf L (-Seam.representative o)).closed (Seam.adaptedDestination z o) := by
  rcases h₀.eq_or_lt with hz | hz
  · right
    rw [diagonal_at_root]
    suffices he : diagonal z = z by rw [he]
    funext i
    fin_cases i <;> simp [diagonal] <;> omega
  · left
    change 0 < (DiagonalSeam.siteCoords
      (Seam.adaptedDestination (-Seam.representative o) (Seam.adaptedDestination z o))).1.val ∧
      (DiagonalSeam.siteCoords (Seam.adaptedDestination (-Seam.representative o)
        (Seam.adaptedDestination z o))).1.val < L
    rw [diagCentered]
    have hh := val_int_nonneg (L:=2*L) (n:=z 0+z 1) h₀ (by push_cast; omega)
    change 0 < ((z 0 + z 1 : ℤ) : ZMod (2*L)).val ∧ ((z 0 + z 1 : ℤ) : ZMod (2*L)).val < L
    omega

private def cubeRep {L : ℕ} (o : Seam.Cell L) : Site :=
  ![(o.1.val : ℤ),(o.2.1.val : ℤ),(o.2.2.val : ℤ)]

private theorem cubeCentered {L : ℕ} [NeZero L] (o : Seam.Cell L) (z : Site) :
    CubicSeam.cubeCoords (Seam.baseMove (-cubeRep o) (Seam.baseMove z o)) = CubicSeam.coords L z := by
  rw [CubicSeam.cubeCoords_baseMove,CubicSeam.cubeCoords_baseMove]
  ext <;> simp [CubicSeam.cubeCoords,CubicSeam.coords,cubeRep]

private theorem cubeCoords_siteMirror {L : ℕ} [NeZero L] (x : Seam.Cell L) :
    CubicSeam.cubeCoords (CubicSeam.siteMirror L x) =
      (-(CubicSeam.cubeCoords x).1,(CubicSeam.cubeCoords x).2) :=
  (CubicSeam.cubeEquiv L).apply_symm_apply _

theorem cubic_site_at_root {L : ℕ} [NeZero L] (o : Seam.Cell (2*L)) (z : Site) :
    shiftedCubicSiteMirror (-cubeRep o) (Seam.baseMove z o) = Seam.baseMove (axis z) o := by
  let d := -cubeRep o
  let u := Seam.baseMove z o
  let v := Seam.baseMove (axis z) o
  have hc : CubicSeam.siteMirror (2*L) (Seam.baseMove d u) = Seam.baseMove d v := by
    apply (CubicSeam.cubeCoords_bijective (2*L)).injective
    rw [cubeCoords_siteMirror,cubeCentered o z,cubeCentered o (axis z)]
    simp [CubicSeam.coords,axis]
  change Seam.baseMove (-d) (CubicSeam.siteMirror (2*L) (Seam.baseMove d u)) = v
  rw [hc, ← PeriodizedWalk.ordinary_add (2*L), add_neg_cancel, PeriodizedWalk.ordinary_zero]

theorem cubic_site_closed_at_root {L : ℕ} [NeZero L] (o : Seam.Cell (2*L)) (z : Site)
    (h₀ : 0 ≤ z 0) (hL : z 0 < (L : ℤ)) :
    CubicSeam.SiteOpen (Seam.baseMove (-cubeRep o) (Seam.baseMove z o)) ∨
      shiftedCubicSiteMirror (-cubeRep o) (Seam.baseMove z o) = Seam.baseMove z o := by
  rcases h₀.eq_or_lt with hz | hz
  · right
    rw [cubic_site_at_root]
    suffices he : axis z=z by rw [he]
    funext i
    fin_cases i <;> simp [axis]
    omega
  · left
    unfold CubicSeam.SiteOpen
    rw [cubeCentered]
    have hh := val_int_nonneg (L:=2*L) (n:=z 0) h₀ (by push_cast; omega)
    change 0 < ((z 0 : ℤ) : ZMod (2*L)).val ∧ ((z 0 : ℤ) : ZMod (2*L)).val < L
    omega

theorem cubic_bond_at_root {L : ℕ} [NeZero L] (o : Seam.Cell (2*L)) (z : Site) :
    (shiftedCubicBondHalf L (-cubeRep o)).refl (Seam.baseMove z o) = Seam.baseMove (bond z) o := by
  let d := -cubeRep o
  let u := Seam.baseMove z o
  let v := Seam.baseMove (bond z) o
  have hc : CubicSeam.bondMirror (2*L) (Seam.baseMove d u) = Seam.baseMove d v := by
    apply (CubicSeam.cubeCoords_bijective (2*L)).injective
    rw [CubicSeam.cubeCoords_bondMirror,cubeCentered o z,cubeCentered o (bond z)]
    simp [CubicSeam.coordMirror,CubicSeam.coords,bond]
  change Seam.baseMove (-d) (CubicSeam.bondMirror (2*L) (Seam.baseMove d u)) = v
  rw [hc, ← PeriodizedWalk.ordinary_add (2*L), add_neg_cancel, PeriodizedWalk.ordinary_zero]

theorem cubic_bond_closed_at_root {L : ℕ} [NeZero L] (o : Seam.Cell (2*L)) (z : Site)
    (h₁ : 1 ≤ z 0) (hL : z 0 ≤ (L : ℤ)) :
    (shiftedCubicBondHalf L (-cubeRep o)).closed (Seam.baseMove z o) := by
  left
  change CubicSeam.OpenSide (Seam.baseMove (-cubeRep o) (Seam.baseMove z o))
  unfold CubicSeam.OpenSide
  rw [cubeCentered]
  have hpos := NeZero.pos L
  have hh := val_int_nonneg (L:=2*L) (n:=z 0) (by omega) (by push_cast; omega)
  change 1 ≤ ((z 0 : ℤ) : ZMod (2*L)).val ∧ ((z 0 : ℤ) : ZMod (2*L)).val ≤ L
  omega

open PeriodicCouplingMixture PeriodicGibbsReflection Filter LatticeWalk
open scoped Topology
open MeasureTheory

/-- One physical Gibbs mirror serves every test at each chosen root.
The side bound applies only to the normal coordinates of the test. -/
theorem diagonal_root_mirrors {I : Type*} {L : ℕ} [NeZero L]
    (x : I → Site) (h₀ : ∀ i, 0 ≤ x i 0+x i 1) (hL : ∀ i, x i 0+x i 1 < (L : ℤ))
    {J : Profile} (hJ : AllGibbsHalves J) :
    HasRootMirrors (Seam.adaptedDestination (L:=L)) (Seam.adaptedSeries L J) diagonal x := by
  intro o
  let d := -Seam.representative o
  have h := hJ.diagonal L d
  exact ⟨shiftedAdaptedHalf L d,h.symmetric,h.reflected,h.cross,
    fun i => diagonal_closed_at_root o (x i) (h₀ i) (hL i),fun i => diagonal_at_root o (x i)⟩

theorem cubic_site_root_mirrors {I : Type*} {L : ℕ} [NeZero L]
    (x : I → Site) (h₀ : ∀ i, 0 ≤ x i 0) (hL : ∀ i, x i 0 < (L : ℤ))
    {J : Profile} (hJ : AllGibbsHalves J) :
    HasRootMirrors (Seam.baseMove (L:=2*L)) (Seam.ordinarySeries (2*L) J) axis x := by
  intro o
  let d := -cubeRep o
  have h := hJ.shiftedSite L d
  exact ⟨cubicShiftedSite L d,h.symmetric,h.reflected,h.cross,
    fun i => cubic_site_closed_at_root o (x i) (h₀ i) (hL i),fun i => cubic_site_at_root o (x i)⟩

theorem cubic_bond_root_mirrors {I : Type*} {L : ℕ} [NeZero L]
    (x : I → Site) (h₁ : ∀ i, 1 ≤ x i 0) (hL : ∀ i, x i 0 ≤ (L : ℤ))
    {J : Profile} (hJ : AllGibbsHalves J) :
    HasRootMirrors (Seam.baseMove (L:=2*L)) (Seam.ordinarySeries (2*L) J) bond x := by
  intro o
  let d := -cubeRep o
  have h := hJ.bond L d
  exact ⟨shiftedCubicBondHalf L d,h.symmetric,h.reflected,h.cross,
    fun i => cubic_bond_closed_at_root o (x i) (h₁ i) (hL i),fun i => cubic_bond_at_root o (x i)⟩

private theorem eventual_normals {I : Type*} [Finite I] {sides : ℕ → ℕ}
    (hsides : Tendsto sides atTop atTop) (normals : I → ℤ) :
    ∀ᶠ j in atTop, ∀ i, normals i < (sides j : ℤ) := by
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [hsides.eventually_gt_atTop (normals i).toNat] with j hj
  omega

/-- Every divergent sequence of adapted sides works for each finite closed-half test.
The cutoff is uniform over the coupling in the physical Gibbs class. -/
theorem eventually_diagonal_root_mirrors {I : Type*} [Finite I] {sides : ℕ → ℕ}
    [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop) (x : I → Site)
    (h₀ : ∀ i, 0 ≤ x i 0+x i 1) :
    ∀ᶠ j in atTop, ∀ {J : Profile}, AllGibbsHalves J →
      HasRootMirrors (Seam.adaptedDestination (L:=sides j)) (Seam.adaptedSeries (sides j) J) diagonal x := by
  filter_upwards [eventual_normals hsides (fun i => x i 0+x i 1)] with j hj J hJ
  exact diagonal_root_mirrors x h₀ hj hJ

theorem eventually_cubic_site_root_mirrors {I : Type*} [Finite I] {sides : ℕ → ℕ}
    [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop) (x : I → Site)
    (h₀ : ∀ i, 0 ≤ x i 0) :
    ∀ᶠ j in atTop, ∀ {J : Profile}, AllGibbsHalves J →
      HasRootMirrors (Seam.baseMove (L:=2*sides j)) (Seam.ordinarySeries (2*sides j) J) axis x := by
  filter_upwards [eventual_normals hsides (fun i => x i 0)] with j hj J hJ
  exact cubic_site_root_mirrors x h₀ hj hJ

theorem eventually_cubic_bond_root_mirrors {I : Type*} [Finite I] {sides : ℕ → ℕ}
    [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop) (x : I → Site)
    (h₁ : ∀ i, 1 ≤ x i 0) :
    ∀ᶠ j in atTop, ∀ {J : Profile}, AllGibbsHalves J →
      HasRootMirrors (Seam.baseMove (L:=2*sides j)) (Seam.ordinarySeries (2*sides j) J) bond x := by
  filter_upwards [eventual_normals hsides (fun i => x i 0)] with j hj J hJ
  exact cubic_bond_root_mirrors x h₁ (fun i => (hj i).le) hJ

/-- Reflected positivity of the same weak spin-field limit even when the inner
subsequence in the adapted variation depends on the perturbation index. -/
theorem diagonal_variation_reflected (N : ℕ) [NeZero N] {sides : ℕ → ℕ}
    [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop)
    (K : ℕ → Profile) (Q : ProbabilityMeasure (SpinField N))
    (hQ : AdaptedVariationLimit N sides K Q) (hK : ∀ᶠ n in atTop, AllGibbsHalves (K n))
    {I : Type*} [Fintype I] (x : I → Site) (h₀ : ∀ i, 0 ≤ x i 0+x i 1) (c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair Q (x i-diagonal (x j)) := by
  apply adapted_variation_reflected N K Q hQ diagonal x c
  filter_upwards [hK] with n hn
  filter_upwards [eventually_diagonal_root_mirrors hsides x h₀] with j hj
  exact hj hn

/-- Rooted ordinary-torus spin-field limits retain the axial site form. -/
theorem cubic_site_limit_reflected (N : ℕ) [NeZero N] {sides : ℕ → ℕ}
    [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop)
    (K : ℕ → Profile) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (2*sides n) (K n)))
      atTop (𝓝 P)) (hK : ∀ᶠ n in atTop, AllGibbsHalves (K n)) {I : Type*} [Fintype I]
    (x : I → Site) (h₀ : ∀ i, 0 ≤ x i 0) (c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair P (x i-axis (x j)) := by
  apply cubic_limit_reflected N (fun j => 2*sides j) K P hP axis x c
  filter_upwards [eventually_cubic_site_root_mirrors hsides x h₀,hK] with j hj hKj
  exact hj hKj

/-- Rooted ordinary-torus spin-field limits retain the axial bond form. -/
theorem cubic_bond_limit_reflected (N : ℕ) [NeZero N] {sides : ℕ → ℕ}
    [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop)
    (K : ℕ → Profile) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (2*sides n) (K n)))
      atTop (𝓝 P)) (hK : ∀ᶠ n in atTop, AllGibbsHalves (K n)) {I : Type*} [Fintype I]
    (x : I → Site) (h₁ : ∀ i, 1 ≤ x i 0) (c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair P (x i-bond (x j)) := by
  apply cubic_limit_reflected N (fun j => 2*sides j) K P hP bond x c
  filter_upwards [eventually_cubic_bond_root_mirrors hsides x h₁,hK] with j hj hKj
  exact hj hKj

#print axioms diagonal_root_mirrors
#print axioms cubic_site_root_mirrors
#print axioms cubic_bond_root_mirrors
#print axioms diagonal_variation_reflected
#print axioms cubic_site_limit_reflected
#print axioms cubic_bond_limit_reflected

end IsingScaling.Rotor.PressureSelection.PeriodicMirrorLift
