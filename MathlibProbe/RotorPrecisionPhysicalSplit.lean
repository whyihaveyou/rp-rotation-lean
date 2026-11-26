import MathlibProbe.RotorPrecisionSevenSeams

/-! # Inverse reflection on the physical halved period lattice

Let θ be a site involution. Its strictly positive side and its reflected
copy are disjoint, and all remaining points are fixed. Enumerate the
actual finite set by its positive sites, their reflected partners, and
its individual fixed sites. Simultaneously reindexing rows and columns
commutes with inversion. In this enumeration the previously proved
closed-half inverse inequality tests precisely Q⁻¹(x, θy). A list of
positive or wall sites is a pullback of that matrix, even with repeated
entries. For Q = m I - A, the negative precision cross-block equals the
physical A cross-block because strict opposite sites are distinct. Row
sums, the mass gap and the reflection symmetry transfer under the same
bijection. Hence the estimates apply to the actual finite coupling.
-/

noncomputable section
open scoped Classical
open Matrix Finset
namespace IsingScaling.Rotor.PressureSelection.PhysicalSplit
open IsingScaling.Rotor.PrecisionReflection
open PeriodizedWalk LatticeWalk

structure Half (T : Type*) where
  refl : T → T
  positive : T → Prop
  invol : Function.Involutive refl
  opposite : ∀ x, positive x → ¬ positive (refl x)
  cover : ∀ x, positive x ∨ positive (refl x) ∨ refl x=x

namespace Half
variable {T : Type*} (H : Half T)

@[simp] theorem refl_refl (x : T) : H.refl (H.refl x)=x := H.invol x

abbrev Plus := {x : T // H.positive x}
abbrev Wall := {x : T // H.refl x=x}
def closed (x : T) : Prop := H.positive x ∨ H.refl x=x

private def decode : Sites H.Plus H.Wall → T
  | .inl v => v.val
  | .inr (.inl v) => H.refl v.val
  | .inr (.inr w) => w.val

private def encode (x : T) : Sites H.Plus H.Wall :=
  if hp : H.positive x then .inl ⟨x,hp⟩ else
  if hn : H.positive (H.refl x) then .inr (.inl ⟨H.refl x,hn⟩) else
    .inr (.inr ⟨x,((H.cover x).resolve_left hp).resolve_left hn⟩)

def equiv : Sites H.Plus H.Wall ≃ T where
  toFun := H.decode
  invFun := H.encode
  left_inv := by
    rintro (v | (v | w))
    · simp [decode,encode,v.property]
    · simp [decode,encode,H.opposite _ v.property,v.property]
    · have hn : ¬ H.positive w.val := by
        intro hp
        exact H.opposite _ hp (w.property.symm ▸ hp)
      simp [decode,encode,hn,w.property]
  right_inv := by
    intro x
    by_cases hp : H.positive x
    · simp [encode,decode,hp]
    · by_cases hn : H.positive (H.refl x) <;> simp [encode,decode,hp,hn]

theorem map_mirror (i : Sites H.Plus H.Wall) : H.equiv (mirror i) = H.refl (H.equiv i) := by
  rcases i with v | (v | w)
  · rfl
  · exact (H.invol v.val).symm
  · exact w.property.symm

private def closedIndex (x : T) (hx : H.closed x) : H.Plus ⊕ H.Wall :=
  if hp : H.positive x then .inl ⟨x,hp⟩ else .inr ⟨x,hx.resolve_left hp⟩

private theorem map_closedIndex (x : T) (hx : H.closed x) :
    H.equiv (closedSite (H.closedIndex x hx)) = x := by
  by_cases hp : H.positive x <;> simp [closedIndex,hp,equiv,decode,closedSite]

variable [Fintype T] [DecidableEq T]

/-- Pull the inverse theorem back to any physical closed-half list. -/
theorem inverse_on_closed {Q : Matrix T T ℝ} (hQ : Q.PosDef)
    (hinv : ∀ x y, Q (H.refl x) (H.refl y)=Q x y)
    (hc : (Matrix.of fun x y : H.Plus => -Q x.val (H.refl y.val)).PosSemidef)
    {ι : Type*} [Fintype ι] (p : ι → T) (hp : ∀ i, H.closed (p i)) :
    (Matrix.of fun i j => Q⁻¹ (p i) (H.refl (p j))).PosSemidef := by
  let e := H.equiv
  let q := Q.submatrix e e
  have hq : q.PosDef := hQ.submatrix e.injective
  have hi (i j : Sites H.Plus H.Wall) : q (mirror i) (mirror j)=q i j := by
    change Q (H.equiv (mirror i)) (H.equiv (mirror j))=Q (H.equiv i) (H.equiv j)
    rw [H.map_mirror,H.map_mirror,hinv]
  have h := inverse_closedReflected_posSemidef hq hi hc
  let k (i : ι) := H.closedIndex (p i) (hp i)
  have hsub := h.submatrix k
  have heq : (closedReflected q⁻¹).submatrix k k =
      Matrix.of (fun i j => Q⁻¹ (p i) (H.refl (p j))) := by
    ext i j
    change (Q.submatrix e e)⁻¹ (closedSite (k i)) (mirror (closedSite (k j))) = _
    rw [Matrix.inv_submatrix_equiv]
    change Q⁻¹ (H.equiv (closedSite (k i))) (H.equiv (mirror (closedSite (k j)))) = _
    rw [H.map_mirror,H.map_closedIndex,H.map_closedIndex]
    rfl
  exact heq ▸ hsub

def precision (m : ℝ) (A : Matrix T T ℝ) : Matrix T T ℝ := Matrix.diagonal (fun _ => m)-A

/-- A nonnegative symmetric finite walk with mass gap and positive physical
seam has a positive reflected inverse on the actual closed half. -/
theorem walk_on_closed {A : Matrix T T ℝ} {m : ℝ}
    (hsym : A.IsHermitian) (hnon : ∀ x y, 0 ≤ A x y)
    (hrow : ∀ x, ∑ y, A x y < m)
    (hinv : ∀ x y, A (H.refl x) (H.refl y)=A x y)
    (hc : (Matrix.of fun x y : H.Plus => A x.val (H.refl y.val)).PosSemidef)
    {ι : Type*} [Fintype ι] (p : ι → T) (hp : ∀ i, H.closed (p i)) :
    (Matrix.of fun i j => (precision m A)⁻¹ (p i) (H.refl (p j))).PosSemidef := by
  let e := H.equiv
  let Q : Matrix T T ℝ := Matrix.diagonal (fun _ => m)-A
  have hq : (walkPrecision m (A.submatrix e e)).PosDef := by
    apply walkPrecision_posDef (hsym.submatrix e) (fun i j => hnon (e i) (e j))
    intro i
    change ∑ j, A (e i) (e j) < m
    rw [Equiv.sum_comp e]
    exact hrow (e i)
  have hsub : Q.submatrix e e = walkPrecision m (A.submatrix e e) := by
    change (Matrix.diagonal (fun _ : T => m)).submatrix e e - A.submatrix e e =
      walkPrecision m (A.submatrix e e)
    rw [Matrix.submatrix_diagonal_equiv]
    rfl
  rw [←hsub] at hq
  have hQ : Q.PosDef := by
    simpa only [Matrix.submatrix_submatrix,Equiv.self_comp_symm,Matrix.submatrix_id_id] using
      hq.submatrix e.symm.injective
  apply H.inverse_on_closed (Q := Q) hQ _ _ p hp
  · intro x y
    simp [Q,Matrix.diagonal_apply,H.invol.injective.eq_iff,hinv]
  · convert hc using 1
    ext x y
    have hxy : x.val ≠ H.refl y.val := by
      intro he
      exact H.opposite _ y.property (he ▸ x.property)
    simp [Q,Matrix.diagonal_apply,hxy]

/-- Pull a physical half and its *individual* fixed sites along a bijection. -/
def pull {U : Type*} (e : U ≃ T) : Half U where
  refl x := e.symm (H.refl (e x))
  positive x := H.positive (e x)
  invol x := by simp
  opposite x hp := by simpa using H.opposite (e x) hp
  cover x := by
    rcases H.cover (e x) with hp | hn | hf
    · exact Or.inl hp
    · exact Or.inr (Or.inl (by simpa using hn))
    · exact Or.inr (Or.inr (by simpa [hf]))

end Half

private theorem nonzero_val {m : ℕ} [NeZero m] (p : ZMod (2*m)) (h : p ≠ 0) : 0 < p.val :=
  Nat.pos_of_ne_zero fun hv => h ((ZMod.val_eq_zero p).mp hv)

private theorem fixed_normal {m : ℕ} [NeZero m] {p : ZMod (2*m)}
    (h : p=0 ∨ p.val=m) : -p=p := by
  rcases h with rfl | hp
  · simp
  · have hn : p ≠ 0 := by
      rintro rfl
      have : 0=m := by simpa using hp
      exact (NeZero.ne m) this.symm
    apply ZMod.val_injective (2*m)
    rw [ZMod.neg_val,if_neg hn]
    omega

private def site_half {T : Type*} (m : ℕ) [NeZero m] (r : T → T) (hr : Function.Involutive r)
    (normal : T → ZMod (2*m)) (hn : ∀ x, normal (r x) = -normal x)
    (hfix : ∀ x, (normal x=0 ∨ (normal x).val=m) → r x=x) : Half T where
  refl := r
  positive x := 0 < (normal x).val ∧ (normal x).val<m
  invol := hr
  opposite := by
    intro x hx hy
    have hz : normal x ≠ 0 := by intro h; simp [h] at hx
    rw [hn,ZMod.neg_val,if_neg hz] at hy
    omega
  cover := by
    intro x
    by_cases hx : normal x=0
    · exact Or.inr (Or.inr (hfix x (Or.inl hx)))
    have hv := nonzero_val (normal x) hx
    have hl := ZMod.val_lt (normal x)
    by_cases hm : (normal x).val=m
    · exact Or.inr (Or.inr (hfix x (Or.inr hm)))
    rw [hn,ZMod.neg_val,if_neg hx]
    omega

private theorem oblique_chart_fixed {L : ℕ} [NeZero L] (p : DiagonalSeam.Chart L)
    (h : p.1=0 ∨ p.1.val=L) : DiagonalSeam.chartMirror p=p := by
  apply Prod.ext (fixed_normal h)
  apply Prod.ext
  swap
  · rfl
  change p.2.1 - (ZMod.castHom (dvd_mul_left L 2) (ZMod L)) p.1 = p.2.1
  rcases h with h | h
  · simp [h]
  · have ht : p.1=(L:ZMod (2*L)) := by rw [←ZMod.natCast_zmod_val p.1,h]
    simp [ht]

/-- Both adapted fixed layers are fixed site by site, even though the
second chart coordinate undergoes a shear away from those layers. -/
def adaptedHalf (L : ℕ) [NeZero L] : Half (Seam.Site L) :=
  site_half L (DiagonalSeam.adaptedMirror L) (DiagonalSeam.adaptedMirror_involutive L)
    (fun x => (DiagonalSeam.siteCoords x).1)
    (fun x => by simp [DiagonalSeam.chartMirror])
    (fun x hx => (DiagonalSeam.siteCoords_bijective L).injective
      ((DiagonalSeam.coords_adaptedMirror L x).trans (oblique_chart_fixed _ hx)))

private theorem site_coords {L : ℕ} [NeZero L] (x : Seam.Cell L) :
    CubicSeam.cubeCoords (CubicSeam.siteMirror L x) =
      (-(CubicSeam.cubeCoords x).1,(CubicSeam.cubeCoords x).2) :=
  (CubicSeam.cubeEquiv L).apply_symm_apply _

def cubicSiteHalf (m : ℕ) [NeZero m] : Half (Seam.Cell (2*m)) :=
  site_half m (CubicSeam.siteMirror (2*m)) (by
    intro x
    apply (CubicSeam.cubeCoords_bijective (2*m)).injective
    simp [site_coords]) (fun x => (CubicSeam.cubeCoords x).1)
    (fun x => by simp [site_coords])
    (fun x hx => (CubicSeam.cubeCoords_bijective (2*m)).injective
      ((site_coords x).trans (Prod.ext (fixed_normal hx) rfl)))

private theorem bond_flip {m : ℕ} [NeZero m] (p : ZMod (2*m)) :
    (1 ≤ (1-p).val ∧ (1-p).val ≤ m) ↔ ¬(1 ≤ p.val ∧ p.val ≤ m) := by
  have hm := NeZero.pos m
  have ho : (1:ZMod (2*m)).val=1 := ZMod.val_one'' (by omega)
  by_cases hz : p=0
  · subst p
    simp [ho]
    omega
  by_cases h1 : p=1
  · subst p
    simp [ho]
    omega
  have hv := nonzero_val p hz
  have h₁ : p.val≠1 := fun he => h1 (ZMod.val_injective _ (he.trans ho.symm))
  have hsub := ZMod.val_sub (a:=p) (b:=1) (by omega)
  have hn : p-1≠0 := sub_ne_zero.mpr h1
  have hl := ZMod.val_lt p
  rw [show 1-p= -(p-1) by abel,ZMod.neg_val,if_neg hn]
  omega

def cubicBondHalf (m : ℕ) [NeZero m] : Half (Seam.Cell (2*m)) where
  refl := CubicSeam.bondMirror (2*m)
  positive := CubicSeam.OpenSide
  invol x := by
    apply (CubicSeam.cubeCoords_bijective (2*m)).injective
    simp [CubicSeam.coordMirror]
  opposite x hx := by
    change ¬(1 ≤ (CubicSeam.cubeCoords (CubicSeam.bondMirror (2*m) x)).1.val ∧ _)
    simp only [CubicSeam.cubeCoords_bondMirror,CubicSeam.coordMirror]
    exact fun hyp => (bond_flip _).mp hyp hx
  cover x := by
    by_cases hx : CubicSeam.OpenSide x
    · exact Or.inl hx
    · right; left
      simpa only [CubicSeam.OpenSide,CubicSeam.cubeCoords_bondMirror,CubicSeam.coordMirror] using
        (bond_flip (CubicSeam.cubeCoords x).1).mpr hx

private def moveEquiv {T : Type*} (D : IsingScaling.Site → T → T) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x)) (d : IsingScaling.Site) : T ≃ T where
  toFun := D d
  invFun := D (-d)
  left_inv x := by rw [←hadd,add_neg_cancel,hzero]
  right_inv x := by rw [←hadd,neg_add_cancel,hzero]

def shiftedAdaptedHalf (L : ℕ) [NeZero L] (d : IsingScaling.Site) : Half (Seam.Site L) :=
  (adaptedHalf L).pull (moveEquiv _ (adapted_zero L) (adapted_add L) d)

def shiftedCubicBondHalf (m : ℕ) [NeZero m] (d : IsingScaling.Site) : Half (Seam.Cell (2*m)) :=
  (cubicBondHalf m).pull (moveEquiv _ (ordinary_zero (2*m)) (ordinary_add (2*m)) d)

/-- On the genuine pressure torus transform the ℓ¹ lattice coupling itself.
The test index can repeat physical sites and can meet either fixed layer. -/
theorem actual_curve_on_closed {T : Type*} [Fintype T] [DecidableEq T] (H : Half T)
    (D : IsingScaling.Site → T → T) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z s x, D (z+s) x = D s (D z x)) (a b c m t : ℝ) (d : Fin 7 → ℝ)
    (w : Fin 7 → ℝ) (hw : w=fun j => weight a b c j+t*d j)
    (hn : ∀ j, 0≤w j) (hrow : ∑ j, w j*(2:ℝ)^(directions j).length < 1-t*m)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator)+hopping d)‖ < 1)
    (hi : ∀ x y, walkMatrix D w (H.refl x) (H.refl y)=walkMatrix D w x y)
    (hc : (Matrix.of fun x y : H.Plus => walkMatrix D w x.val (H.refl y.val)).PosSemidef)
    {ι : Type*} [Fintype ι] (p : ι → T) (hp : ∀ i, H.closed (p i)) :
    (Matrix.of fun i j => Seam.periodizeSeries D
      (operatorCurve a b c (m • (1:Operator)+hopping d) t) (p i) (H.refl (p j))).PosSemidef := by
  have h := H.walk_on_closed (walkMatrix_isHermitian D hzero hadd w) (walkMatrix_nonneg D w hn)
    (m:=1-t*m) (fun x => (walkMatrix_row_sum D w x).trans_lt hrow) hi hc p hp
  have he : Matrix.of (Seam.periodizeSeries D (operatorCurve a b c (m • (1:Operator)+hopping d) t)) =
      (Half.precision (1-t*m) (walkMatrix D w))⁻¹ := by
    rw [hw]
    exact periodize_operatorCurve_eq_inverse D hzero hadd a b c m t d ht
  simpa only [←he,Matrix.of_apply] using h

/-- The two diagonal fixed layers, all their interior translates, and all
closed positive test sites, for the actual perturbed periodic coupling. -/
theorem shifted_adapted_curve {L : ℕ} [NeZero L] (s : IsingScaling.Site)
    (a b c m t : ℝ) (d w : Fin 7 → ℝ) (hw : w=fun j => weight a b c j+t*d j)
    (hn : ∀ j, 0≤w j) (hrow : ∑ j, w j*(2:ℝ)^(directions j).length < 1-t*m)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator)+hopping d)‖ < 1)
    (hv₀ : w 0=w 1) (hv₄ : w 4=w 5) (hv₃ : 2*w 6≤w 3)
    {ι : Type*} [Fintype ι] (p : ι → Seam.Site L)
    (hp : ∀ i, DiagonalSeam.OpenSide (Seam.adaptedDestination s (p i)) ∨
        DiagonalSeam.shiftedMirror s (p i)=p i) :
    (Matrix.of fun i j => Seam.adaptedSeries L (operatorCurve a b c (m • (1:Operator)+hopping d) t)
      (p i) (DiagonalSeam.shiftedMirror s (p j))).PosSemidef := by
  apply actual_curve_on_closed (shiftedAdaptedHalf L s) _ (adapted_zero L) (adapted_add L)
    a b c m t d w hw hn hrow ht (SevenSeams.shifted_oblique_walk_invariant w hv₀ hv₄ s) _ p hp
  exact SevenSeams.shifted_oblique_cross_posSemidef w (hn 6) hv₃ s
    (fun x : (shiftedAdaptedHalf L s).Plus => x.val) (fun x => x.property)

theorem shifted_bond_curve {L : ℕ} [NeZero L] (s : IsingScaling.Site)
    (a b c m t : ℝ) (d w : Fin 7 → ℝ) (hw : w=fun j => weight a b c j+t*d j)
    (hn : ∀ j, 0≤w j) (hrow : ∑ j, w j*(2:ℝ)^(directions j).length < 1-t*m)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator)+hopping d)‖ < 1)
    (h₀ : 2*w 3+2*w 4+4*w 6 ≤ w 0)
    {ι : Type*} [Fintype ι] (p : ι → Seam.Cell (2*L))
    (hp : ∀ i, CubicSeam.OpenSide (Seam.baseMove s (p i))) :
    (Matrix.of fun i j => Seam.ordinarySeries (2*L) (operatorCurve a b c (m • (1:Operator)+hopping d) t)
      (p i) (CubicSeam.shiftedBond s (p j))).PosSemidef := by
  apply actual_curve_on_closed (shiftedCubicBondHalf L s) _ (ordinary_zero (2*L)) (ordinary_add (2*L))
    a b c m t d w hw hn hrow ht (SevenSeams.shifted_axial_walk_invariant w s) _ p
    (fun i => Or.inl (hp i))
  exact SevenSeams.shifted_axial_cross_posSemidef w (hn 3) (hn 4) (hn 6) h₀ s
    (fun x : (shiftedCubicBondHalf L s).Plus => x.val) (fun x => x.property)

theorem coordinate_site_curve {L : ℕ} [NeZero L] (a b c m t : ℝ)
    (d w : Fin 7 → ℝ) (hw : w=fun j => weight a b c j+t*d j)
    (hn : ∀ j, 0≤w j) (hrow : ∑ j, w j*(2:ℝ)^(directions j).length < 1-t*m)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator)+hopping d)‖ < 1)
    {ι : Type*} [Fintype ι] (p : ι → Seam.Cell (2*L))
    (hp : ∀ i, CubicSeam.SiteOpen (p i) ∨ CubicSeam.siteMirror (2*L) (p i)=p i) :
    (Matrix.of fun i j => Seam.ordinarySeries (2*L) (operatorCurve a b c (m • (1:Operator)+hopping d) t)
      (p i) (CubicSeam.siteMirror (2*L) (p j))).PosSemidef := by
  apply actual_curve_on_closed (cubicSiteHalf L) _ (ordinary_zero (2*L)) (ordinary_add (2*L))
    a b c m t d w hw hn hrow ht (SevenSeams.coordinate_site_walk_invariant w) _ p hp
  have he : (Matrix.of fun x y : (cubicSiteHalf L).Plus =>
      walkMatrix Seam.baseMove w x.val (CubicSeam.siteMirror (2*L) y.val)) = 0 := by
    ext x y
    exact SevenSeams.coordinate_site_cross_zero w x.val y.val x.property y.property
  rw [show (cubicSiteHalf L).refl=CubicSeam.siteMirror (2*L) by rfl,he]
  exact Matrix.PosSemidef.zero

#print axioms shifted_adapted_curve
#print axioms shifted_bond_curve
#print axioms coordinate_site_curve

open Filter
open scoped Topology
universe u

/-- All three physical finite covariance readouts, keeping the same lattice
coupling at every size. The test type, periods, shifts and lists are
quantified *after* selection of the perturbation parameter. -/
structure PeriodicCovarianceForms (J : Profile) : Prop where
  diagonal : ∀ {L : ℕ} [NeZero L] (s : IsingScaling.Site) {ι : Type u} [Fintype ι]
    (p : ι → Seam.Site L), (∀ i, DiagonalSeam.OpenSide (Seam.adaptedDestination s (p i)) ∨
        DiagonalSeam.shiftedMirror s (p i)=p i) →
    (Matrix.of fun i j => Seam.adaptedSeries L J (p i) (DiagonalSeam.shiftedMirror s (p j))).PosSemidef
  bond : ∀ {L : ℕ} [NeZero L] (s : IsingScaling.Site) {ι : Type u} [Fintype ι]
    (p : ι → Seam.Cell (2*L)), (∀ i, CubicSeam.OpenSide (Seam.baseMove s (p i))) →
    (Matrix.of fun i j => Seam.ordinarySeries (2*L) J (p i) (CubicSeam.shiftedBond s (p j))).PosSemidef
  site : ∀ {L : ℕ} [NeZero L] {ι : Type u} [Fintype ι] (p : ι → Seam.Cell (2*L)),
    (∀ i, CubicSeam.SiteOpen (p i) ∨ CubicSeam.siteMirror (2*L) (p i)=p i) →
    (Matrix.of fun i j => Seam.ordinarySeries (2*L) J (p i) (CubicSeam.siteMirror (2*L) (p j))).PosSemidef

private theorem periodize_translate {T : Type*} [DecidableEq T] (D : IsingScaling.Site → T → T)
    (hzero : ∀ x, D 0 x=x) (hadd : ∀ z s x, D (z+s) x = D s (D z x))
    (J : Profile) (d : IsingScaling.Site) (x y : T) :
    Seam.periodizeSeries D J (D d x) (D d y)=Seam.periodizeSeries D J x y := by
  have hinj : Function.Injective (D d) := (moveEquiv D hzero hadd d).injective
  unfold Seam.periodizeSeries
  apply tsum_congr
  intro z
  have h : D z (D d x)=D d (D z x) := by rw [←hadd,add_comm d z,hadd]
  by_cases he : D z x=y
  · simp [h,he]
  · simp [h,hinj.eq_iff,he]

def shiftedCubicSiteMirror {L : ℕ} [NeZero L] (s : IsingScaling.Site)
    (x : Seam.Cell (2*L)) : Seam.Cell (2*L) :=
  Seam.baseMove (-s) (CubicSeam.siteMirror (2*L) (Seam.baseMove s x))

/-- Translation invariance of the *same* periodic coupling moves the
ordinary site result to every parallel mirror, with its entire fixed walls. -/
theorem PeriodicCovarianceForms.shiftedSite {J : Profile} (F : PeriodicCovarianceForms.{u} J)
    {L : ℕ} [NeZero L] (s : IsingScaling.Site) {ι : Type u} [Fintype ι]
    (p : ι → Seam.Cell (2*L))
    (hp : ∀ i, CubicSeam.SiteOpen (Seam.baseMove s (p i)) ∨ shiftedCubicSiteMirror s (p i)=p i) :
    (Matrix.of fun i j => Seam.ordinarySeries (2*L) J (p i) (shiftedCubicSiteMirror s (p j))).PosSemidef := by
  have hθ (x : Seam.Cell (2*L)) : Seam.baseMove s (shiftedCubicSiteMirror s x) =
      CubicSeam.siteMirror (2*L) (Seam.baseMove s x) := by
    unfold shiftedCubicSiteMirror
    rw [←ordinary_add (2*L),neg_add_cancel,ordinary_zero]
  have H := F.site (fun i => Seam.baseMove s (p i)) (fun i => (hp i).imp_right (fun e =>
    (hθ (p i)).symm.trans (congrArg (Seam.baseMove s) e)))
  convert H using 1
  ext i j
  change Seam.periodizeSeries Seam.baseMove J (p i) (shiftedCubicSiteMirror s (p j)) = _
  rw [←periodize_translate Seam.baseMove (ordinary_zero (2*L)) (ordinary_add (2*L)) J s,hθ]
  rfl

/-- Every sufficiently small positive or negative physical perturbation
preserving the two oblique weight symmetries has all three reflected
covariance inequalities, simultaneously for all volumes and tests. -/
theorem eventually_periodic_covariance_forms {a b c : ℝ} (hc : 0<c) (hb : 2*c<b)
    (ha : 4*b+4*c<a) (hgap : 6*a+12*b+8*c<1) (m : ℝ) (d : Fin 7 → ℝ)
    (hd₀ : d 0=d 1) (hd₄ : d 4=d 5) :
    ∀ᶠ t in 𝓝 (0:ℝ), PeriodicCovarianceForms.{u}
      (operatorCurve a b c (m • (1:Operator)+hopping d) t) := by
  let w (t : ℝ) (j : Fin 7) := weight a b c j+t*d j
  have hb' : 0<b := by linarith
  have ha' : 0<a := by linarith
  have hdiag : ∀ᶠ t in 𝓝 (0:ℝ), 2*w t 6 < w t 3 :=
    (isOpen_lt (show Continuous (fun t => 2*w t 6) by dsimp [w]; fun_prop)
      (show Continuous (fun t => w t 3) by dsimp [w]; fun_prop)).mem_nhds (by
        simpa [w,weight] using hb)
  have hax : ∀ᶠ t in 𝓝 (0:ℝ), 2*w t 3+2*w t 4+4*w t 6 < w t 0 :=
    (isOpen_lt (show Continuous (fun t => 2*w t 3+2*w t 4+4*w t 6) by dsimp [w]; fun_prop)
      (show Continuous (fun t => w t 0) by dsimp [w]; fun_prop)).mem_nhds (by
        simp [w,weight]
        linarith)
  filter_upwards [eventually_admissible_weights ha' hb' hc hgap m d,hdiag,hax] with t H h₃ h₀
  have h₁ : w t 0=w t 1 := by simp [w,weight,hd₀]
  have h₅ : w t 4=w t 5 := by simp [w,weight,hd₄]
  constructor
  · intro L _ s ι _ p hp
    exact shifted_adapted_curve s a b c m t d (w t) rfl H.1 H.2.1 H.2.2 h₁ h₅ h₃.le p hp
  · intro L _ s ι _ p hp
    exact shifted_bond_curve s a b c m t d (w t) rfl H.1 H.2.1 H.2.2 h₀.le p hp
  · intro L _ ι _ p hp
    exact coordinate_site_curve a b c m t d (w t) rfl H.1 H.2.1 H.2.2 p hp

#print axioms eventually_periodic_covariance_forms
#print axioms PeriodicCovarianceForms.shiftedSite

end IsingScaling.Rotor.PressureSelection.PhysicalSplit
