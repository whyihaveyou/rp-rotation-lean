import MathlibProbe.RotorPrecisionAxialSeam
import MathlibProbe.RotorPeriodizedWalkResolvent

/-!
# Open-half cross matrices for the seven independently varied hopping weights

The entries use the same finite walk matrix as the periodized resolvent.
At the adapted site wall only orbit 3 (the first-two-coordinate diagonal)
and orbit 6 (the body diagonal) reach the reflected open half. At the
coordinate bond, the retained orbits are 0,3,4,6. Their independent
coefficients lead to a direct weight and two different transverse
nearest-neighbour weights. Summing the two boundary-layer congruences
gives matrix positivity for arbitrary lists of actual original sites.
-/

noncomputable section
namespace IsingScaling.Rotor.PressureSelection.SevenSeams

open LatticeWalk
open PeriodizedWalk (walkMatrix)
open DiagonalSeam (bit bit_and mask_posSemidef)
open IsingScaling.Rotor.PrecisionReflection
open Matrix

theorem oblique_entry {L : ℕ} [NeZero L] (v : Fin 7 → ℝ) (p q : Seam.Site L)
    (hp : DiagonalSeam.OpenSide p) (hq : DiagonalSeam.OpenSide q) :
    walkMatrix Seam.adaptedDestination v p (DiagonalSeam.adaptedMirror L q) =
      DiagonalSeam.physicalWalk L 0 (v 3) (v 6) p (DiagonalSeam.adaptedMirror L q) := by
  let f (z : Site) := bit (Seam.adaptedDestination z p=DiagonalSeam.adaptedMirror L q)
  have hzero (z : Site) (hx : -1≤z 0 ∧ z 0≤1) (hy : -1≤z 1 ∧ z 1≤1)
      (h : z 0=0 ∨ z 1=0) : f z=0 := by
    have hm := DiagonalSeam.adapted_cross_iff p q hp hq z hx hy
    classical
    have hn : ¬(Seam.adaptedDestination z p=DiagonalSeam.adaptedMirror L q) := by
      intro he
      rcases (hm.mp he).1 with ⟨_,_,h₀,h₁⟩ | ⟨_,_,h₀,h₁⟩ <;> omega
    simp [f,bit,hn]
  change (∑ j, v j*orbit (directions j) f 0) = step 0 (v 3) (v 6) f 0
  simp (disch:=decide) [step,directions,weight,Fin.sum_univ_succ,orbit,both,hzero]

theorem oblique_cross_posSemidef {L : ℕ} [NeZero L] (v : Fin 7 → ℝ)
    (h₆ : 0 ≤ v 6) (h₃ : 2*v 6 ≤ v 3) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Seam.Site L) (hp : ∀ i, DiagonalSeam.OpenSide (p i)) :
    (Matrix.of fun i j => walkMatrix Seam.adaptedDestination v (p i) (DiagonalSeam.adaptedMirror L (p j))).PosSemidef := by
  have h := DiagonalSeam.physical_oblique_cross_posSemidef 0 h₆ h₃ p hp
  convert h using 1
  ext i j
  exact oblique_entry v (p i) (p j) (hp i) (hp j)

private theorem axial_stencil (w : Fin 7 → ℝ) (l u : ℝ) (f : Profile) (v : ℤ → ℤ → ℝ)
    (hf : ∀ d : Site, (-1 ≤ d 0 ∧ d 0 ≤ 1) →
      f d = (l*bit (d 0= -1)+u*bit (d 0=1))*v (d 1) (d 2)) :
    (∑ j, w j*orbit (directions j) f 0) =
    (l+u)*CubicSeam.anisotropicNine (w 0) (w 3) (w 4) (w 6) v := by
  classical
  simp (disch:=decide) [directions,Fin.sum_univ_succ,orbit,both,hf,unit,bit,CubicSeam.anisotropicNine]
  ring

theorem axial_entry {m : ℕ} [NeZero m] (w : Fin 7 → ℝ) (x y : Seam.Cell (2*m))
    (hx : CubicSeam.OpenSide x) (hy : CubicSeam.OpenSide y) :
    walkMatrix Seam.baseMove w x (CubicSeam.bondMirror (2*m) y)=
    (bit ((CubicSeam.cubeCoords x).1.val=1 ∧ (CubicSeam.cubeCoords y).1.val=1)+
     bit ((CubicSeam.cubeCoords x).1.val=m ∧ (CubicSeam.cubeCoords y).1.val=m))*
    CubicSeam.anisotropicNine (w 0) (w 3) (w 4) (w 6) (CubicSeam.tangentRead x y) :=
  axial_stencil _ _ _ _ _ (CubicSeam.bond_step_bit x y hx hy)

theorem axial_cross_posSemidef {m : ℕ} [NeZero m] (w : Fin 7 → ℝ)
    (h₃ : 0 ≤ w 3) (h₄ : 0 ≤ w 4) (h₆ : 0 ≤ w 6) (h₀ : 2*w 3+2*w 4+4*w 6 ≤ w 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Seam.Cell (2*m))
    (hp : ∀ i, CubicSeam.OpenSide (p i)) :
    (Matrix.of fun i j => walkMatrix Seam.baseMove w (p i) (CubicSeam.bondMirror (2*m) (p j))).PosSemidef := by
  let e (i : ι) := (CubicSeam.cubeCoords (p i)).2
  let u := CubicSeam.shift (2*m) 1 0
  let v := CubicSeam.shift (2*m) 0 1
  let P := seamBlock (w 0) ![u,v,u.trans v,u.trans v.symm] ![w 3,w 4,w 6,w 6]
  have hP : P.PosSemidef := by
    apply weighted_seam_posSemidef
    · intro j
      fin_cases j <;> first | exact h₃ | exact h₄ | exact h₆
    · simp [Fin.sum_univ_succ]
      linarith
  let S := P.submatrix e e
  have hs : S.PosSemidef := hP.submatrix e
  let d i := bit ((CubicSeam.cubeCoords (p i)).1.val=1)
  let t i := bit ((CubicSeam.cubeCoords (p i)).1.val=m)
  have h := (mask_posSemidef hs d).add (mask_posSemidef hs t)
  convert h using 1
  ext i j
  change walkMatrix Seam.baseMove w (p i) (CubicSeam.bondMirror (2*m) (p j)) =
    d i*S i j*d j+t i*S i j*t j
  rw [axial_entry w (p i) (p j) (hp i) (hp j)]
  have hh : S i j=CubicSeam.anisotropicNine (w 0) (w 3) (w 4) (w 6)
      (CubicSeam.tangentRead (p i) (p j)) :=
    CubicSeam.tangential_anisotropic_entry (w 0) (w 3) (w 4) (w 6) (e i) (e j)
  rw [hh,bit_and,bit_and]
  dsimp [d,t]
  ring

theorem coordinate_site_cross_zero {m : ℕ} [NeZero m] (v : Fin 7 → ℝ)
    (x y : Seam.Cell (2*m)) (hx : CubicSeam.SiteOpen x) (hy : CubicSeam.SiteOpen y) :
    walkMatrix Seam.baseMove v x (CubicSeam.siteMirror (2*m) y)=0 := by
  let f (z : Site) := bit (Seam.baseMove z x=CubicSeam.siteMirror (2*m) y)
  let o (j : Fin 7) := orbit (directions j) f 0
  have ho (j : Fin 7) : 0 ≤ o j := by
    apply orbit_nonneg
    intro z
    classical
    by_cases h : Seam.baseMove z x=CubicSeam.siteMirror (2*m) y <;> simp [f,bit,h]
  have hz := CubicSeam.physical_site_cross_zero 1 1 1 x y hx hy
  have hw (j : Fin 7) : weight 1 1 1 j=1 := by fin_cases j <;> rfl
  change ∑ j, weight 1 1 1 j * o j = 0 at hz
  simp only [hw,one_mul] at hz
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ho j)).mp hz
  change ∑ j, v j*o j=0
  exact Finset.sum_eq_zero fun j hj => by rw [hzero j hj,mul_zero]

#print axioms oblique_cross_posSemidef
#print axioms axial_cross_posSemidef
#print axioms coordinate_site_cross_zero

private theorem move_cancel {V : Type*} (D : Site → V → V) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x=D t (D z x)) (d : Site) (x : V) : D d (D (-d) x)=x := by
  rw [← hadd,neg_add_cancel,hzero]

private theorem walk_translate {V : Type*} [Fintype V] [DecidableEq V] (D : Site → V → V)
    (hzero : ∀ x, D 0 x=x) (hadd : ∀ z t x, D (z+t) x=D t (D z x))
    (v : Fin 7 → ℝ) (d : Site) (x y : V) :
    walkMatrix D v (D d x) (D d y)=walkMatrix D v x y := by
  have hrev : Function.LeftInverse (D (-d)) (D d) := by
    intro z
    rw [← hadd,add_neg_cancel,hzero]
  have hf : (fun z => bit (D z (D d x)=D d y))=(fun z => bit (D z x=y)) := by
    funext z
    have hcomm : D z (D d x)=D d (D z x) := by rw [← hadd,add_comm d z,hadd]
    rw [hcomm,hrev.injective.eq_iff]
  simp only [walkMatrix,hf]

theorem shifted_oblique_cross_posSemidef {L : ℕ} [NeZero L] (v : Fin 7 → ℝ)
    (h₆ : 0 ≤ v 6) (h₃ : 2*v 6 ≤ v 3) (d : Site) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Seam.Site L) (hp : ∀ i, DiagonalSeam.OpenSide (Seam.adaptedDestination d (p i))) :
    (Matrix.of fun i j => walkMatrix Seam.adaptedDestination v (p i) (DiagonalSeam.shiftedMirror d (p j))).PosSemidef := by
  have h := oblique_cross_posSemidef v h₆ h₃ (fun i => Seam.adaptedDestination d (p i)) hp
  convert h using 1
  ext i j
  change walkMatrix Seam.adaptedDestination v (p i) (DiagonalSeam.shiftedMirror d (p j)) = _
  rw [← walk_translate _ (PeriodizedWalk.adapted_zero L) (PeriodizedWalk.adapted_add L) v d]
  simp [DiagonalSeam.shiftedMirror,move_cancel _ (PeriodizedWalk.adapted_zero L) (PeriodizedWalk.adapted_add L)]

theorem shifted_axial_cross_posSemidef {m : ℕ} [NeZero m] (w : Fin 7 → ℝ)
    (h₃ : 0 ≤ w 3) (h₄ : 0 ≤ w 4) (h₆ : 0 ≤ w 6) (h₀ : 2*w 3+2*w 4+4*w 6 ≤ w 0)
    (d : Site) {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Seam.Cell (2*m))
    (hp : ∀ i, CubicSeam.OpenSide (Seam.baseMove d (p i))) :
    (Matrix.of fun i j => walkMatrix Seam.baseMove w (p i) (CubicSeam.shiftedBond d (p j))).PosSemidef := by
  have h := axial_cross_posSemidef w h₃ h₄ h₆ h₀ (fun i => Seam.baseMove d (p i)) hp
  convert h using 1
  ext i j
  change walkMatrix Seam.baseMove w (p i) (CubicSeam.shiftedBond d (p j)) = _
  rw [← walk_translate _ (PeriodizedWalk.ordinary_zero (2*m)) (PeriodizedWalk.ordinary_add (2*m)) w d]
  simp [CubicSeam.shiftedBond,move_cancel _ (PeriodizedWalk.ordinary_zero (2*m)) (PeriodizedWalk.ordinary_add (2*m))]

#print axioms shifted_oblique_cross_posSemidef
#print axioms shifted_axial_cross_posSemidef

private def diagonalStep (z : Site) : Site := ![-z 1,-z 0,z 2]
private def axialStep (z : Site) : Site := ![-z 0,z 1,z 2]

private theorem values (f : Profile) (z : Site) : f z=f ![z 0,z 1,z 2] := by
  apply congrArg f
  funext i
  fin_cases i <;> rfl

private theorem oblique_orbits (w : Fin 7 → ℝ) (h₀ : w 0=w 1) (h₄ : w 4=w 5)
    (f : Profile) :
    (∑ j, w j*orbit (directions j) (fun z => f (diagonalStep z)) 0) =
      ∑ j, w j*orbit (directions j) f 0 := by
  let g (a b c : ℤ) := f ![a,b,c]
  have hf : f=(fun z => g (z 0) (z 1) (z 2)) := funext (values f)
  have hr : (fun z => f (diagonalStep z))=(fun z => g (-(z 1)) (-(z 0)) (z 2)) := rfl
  rw [hr]
  conv_rhs => rw [hf]
  simp (disch:=decide) [directions, Fin.sum_univ_succ,orbit,both,unit,h₀,h₄]
  ring

private theorem axial_orbits (w : Fin 7 → ℝ) (f : Profile) :
    (∑ j, w j*orbit (directions j) (fun z => f (axialStep z)) 0) =
      ∑ j, w j*orbit (directions j) f 0 := by
  let g (a b c : ℤ) := f ![a,b,c]
  have hf : f=(fun z => g (z 0) (z 1) (z 2)) := funext (values f)
  have hr : (fun z => f (axialStep z))=(fun z => g (-(z 0)) (z 1) (z 2)) := rfl
  rw [hr]
  conv_rhs => rw [hf]
  simp (disch:=decide) [directions,Fin.sum_univ_succ,orbit,both,unit]
  ring

/-- Reflection invariance of the full hopping matrix is a separate statement
from positivity of its cross block. For the oblique mirror, the two exchanged
pairs of orbit weights must agree. -/
theorem oblique_walk_invariant {L : ℕ} [NeZero L] (w : Fin 7 → ℝ)
    (h₀ : w 0=w 1) (h₄ : w 4=w 5) (x y : Seam.Site L) :
    walkMatrix Seam.adaptedDestination w (DiagonalSeam.adaptedMirror L x)
        (DiagonalSeam.adaptedMirror L y)=walkMatrix Seam.adaptedDestination w x y := by
  let r := DiagonalSeam.adaptedMirror L
  have him (p q : DiagonalSeam.Chart L) :
      DiagonalSeam.chartMirror (p+q)=DiagonalSeam.chartMirror p+DiagonalSeam.chartMirror q := by
    ext <;> simp [DiagonalSeam.chartMirror] <;> abel
  have hi (p : DiagonalSeam.Chart L) : DiagonalSeam.chartMirror (DiagonalSeam.chartMirror p)=p := by
    ext <;> simp [DiagonalSeam.chartMirror]
  have hd (z : Site) : Seam.adaptedDestination z (r x)=r (Seam.adaptedDestination (diagonalStep z) x) := by
    apply (DiagonalSeam.siteCoords_bijective L).injective
    simp only [r,DiagonalSeam.coords_adaptedDestination,DiagonalSeam.coords_adaptedMirror,him,
      diagonalStep,DiagonalSeam.coords_geometric_mirror,hi]
  let f (z : Site) := bit (Seam.adaptedDestination z x=y)
  have he : (fun z => bit (Seam.adaptedDestination z (r x)=r y))=(fun z => f (diagonalStep z)) := by
    funext z
    rw [hd,(DiagonalSeam.adaptedMirror_involutive L).injective.eq_iff]
  change (∑ j, w j*orbit (directions j) (fun z => bit (Seam.adaptedDestination z (r x)=r y)) 0)=_
  rw [he]
  exact oblique_orbits w h₀ h₄ f

theorem axial_walk_invariant {L : ℕ} [NeZero L] (w : Fin 7 → ℝ) (x y : Seam.Cell L) :
    walkMatrix Seam.baseMove w (CubicSeam.bondMirror L x) (CubicSeam.bondMirror L y)=
      walkMatrix Seam.baseMove w x y := by
  let r := CubicSeam.bondMirror L
  have hinj : Function.Injective r := by
    intro p q h
    apply (CubicSeam.cubeCoords_bijective L).injective
    have h' := congrArg CubicSeam.cubeCoords h
    simp only [r,CubicSeam.cubeCoords_bondMirror,CubicSeam.coordMirror,Prod.mk.injEq,sub_right_inj] at h'
    exact Prod.ext h'.1 h'.2
  have hd (z : Site) : Seam.baseMove z (r x)=r (Seam.baseMove (axialStep z) x) := by
    apply (CubicSeam.cubeCoords_bijective L).injective
    simp only [r,CubicSeam.cubeCoords_baseMove,CubicSeam.cubeCoords_bondMirror,CubicSeam.coordMirror,CubicSeam.coords]
    ext <;> simp [axialStep]
    ring
  let f (z : Site) := bit (Seam.baseMove z x=y)
  have he : (fun z => bit (Seam.baseMove z (r x)=r y))=(fun z => f (axialStep z)) := by
    funext z
    rw [hd,hinj.eq_iff]
  change (∑ j, w j*orbit (directions j) (fun z => bit (Seam.baseMove z (r x)=r y)) 0)=_
  rw [he]
  exact axial_orbits w f

#print axioms oblique_walk_invariant
#print axioms axial_walk_invariant

theorem coordinate_site_walk_invariant {L : ℕ} [NeZero L] (w : Fin 7 → ℝ) (x y : Seam.Cell L) :
    walkMatrix Seam.baseMove w (CubicSeam.siteMirror L x) (CubicSeam.siteMirror L y)=
      walkMatrix Seam.baseMove w x y := by
  let r := CubicSeam.siteMirror L
  have hr (p : Seam.Cell L) : CubicSeam.cubeCoords (r p)=
      (-(CubicSeam.cubeCoords p).1,(CubicSeam.cubeCoords p).2) :=
    (CubicSeam.cubeEquiv L).apply_symm_apply _
  have hinj : Function.Injective r := by
    intro p q h
    apply (CubicSeam.cubeCoords_bijective L).injective
    have h' := congrArg CubicSeam.cubeCoords h
    simp only [hr,Prod.mk.injEq,neg_inj] at h'
    exact Prod.ext h'.1 h'.2
  have hd (z : Site) : Seam.baseMove z (r x)=r (Seam.baseMove (axialStep z) x) := by
    apply (CubicSeam.cubeCoords_bijective L).injective
    simp only [CubicSeam.cubeCoords_baseMove,hr,CubicSeam.coords]
    ext <;> simp [axialStep] <;> ring
  let f (z : Site) := bit (Seam.baseMove z x=y)
  have he : (fun z => bit (Seam.baseMove z (r x)=r y))=(fun z => f (axialStep z)) := by
    funext z
    rw [hd,hinj.eq_iff]
  change (∑ j, w j*orbit (directions j) (fun z => bit (Seam.baseMove z (r x)=r y)) 0)=_
  rw [he]
  exact axial_orbits w f

theorem shifted_oblique_walk_invariant {L : ℕ} [NeZero L] (w : Fin 7 → ℝ)
    (h₀ : w 0=w 1) (h₄ : w 4=w 5) (d : Site) (x y : Seam.Site L) :
    walkMatrix Seam.adaptedDestination w (DiagonalSeam.shiftedMirror d x) (DiagonalSeam.shiftedMirror d y)=
      walkMatrix Seam.adaptedDestination w x y := by
  unfold DiagonalSeam.shiftedMirror
  rw [walk_translate _ (PeriodizedWalk.adapted_zero L) (PeriodizedWalk.adapted_add L) w (-d),
    oblique_walk_invariant w h₀ h₄,
    walk_translate _ (PeriodizedWalk.adapted_zero L) (PeriodizedWalk.adapted_add L) w d]

theorem shifted_axial_walk_invariant {L : ℕ} [NeZero L] (w : Fin 7 → ℝ) (d : Site) (x y : Seam.Cell L) :
    walkMatrix Seam.baseMove w (CubicSeam.shiftedBond d x) (CubicSeam.shiftedBond d y)=
      walkMatrix Seam.baseMove w x y := by
  unfold CubicSeam.shiftedBond
  rw [walk_translate _ (PeriodizedWalk.ordinary_zero L) (PeriodizedWalk.ordinary_add L) w (-d),
    axial_walk_invariant w,
    walk_translate _ (PeriodizedWalk.ordinary_zero L) (PeriodizedWalk.ordinary_add L) w d]

#print axioms coordinate_site_walk_invariant
#print axioms shifted_oblique_walk_invariant
#print axioms shifted_axial_walk_invariant

open Filter
open scoped Topology

/-- One neighbourhood of zero in the perturbation parameter works on all
periods and all finite open-half test lists; no volume-dependent tolerance
enters the two seam bounds. -/
theorem eventually_all_cross_matrices {a b c : ℝ} (hc : 0<c) (hb : 2*c<b)
    (ha : 4*b+4*c<a) (d : Fin 7 → ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ᶠ t in 𝓝 (0:ℝ), let w := fun j => weight a b c j+t*d j
      (∀ (L : ℕ) [NeZero L] (p : ι → Seam.Site L), (∀ i, DiagonalSeam.OpenSide (p i)) →
        (Matrix.of fun i j => walkMatrix Seam.adaptedDestination w (p i) (DiagonalSeam.adaptedMirror L (p j))).PosSemidef) ∧
      (∀ (m : ℕ) [NeZero m] (p : ι → Seam.Cell (2*m)), (∀ i, CubicSeam.OpenSide (p i)) →
        (Matrix.of fun i j => walkMatrix Seam.baseMove w (p i) (CubicSeam.bondMirror (2*m) (p j))).PosSemidef) := by
  let w (t : ℝ) (j : Fin 7) := weight a b c j+t*d j
  have hpos (j : Fin 7) : 0<weight a b c j := by
    have hbb : 0<b := by linarith
    have haa : 0<a := by linarith
    fin_cases j <;> first | exact haa | exact hbb | exact hc
  have hnon : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, 0<w t j := by
    rw [Filter.eventually_all]
    intro j
    exact (isOpen_lt continuous_const (show Continuous (fun t => w t j) by dsimp [w]; fun_prop)).mem_nhds
      (by simpa [w] using hpos j)
  have hdiag : ∀ᶠ t in 𝓝 (0:ℝ), 2*w t 6<w t 3 :=
    (isOpen_lt (show Continuous (fun t => 2*w t 6) by dsimp [w]; fun_prop)
      (show Continuous (fun t => w t 3) by dsimp [w]; fun_prop)).mem_nhds (by
        simpa [w,weight] using hb)
  have hax : ∀ᶠ t in 𝓝 (0:ℝ), 2*w t 3+2*w t 4+4*w t 6<w t 0 :=
    (isOpen_lt (show Continuous (fun t => 2*w t 3+2*w t 4+4*w t 6) by dsimp [w]; fun_prop)
      (show Continuous (fun t => w t 0) by dsimp [w]; fun_prop)).mem_nhds (by
        simp [w,weight]
        linarith)
  filter_upwards [hnon,hdiag,hax] with t hn hd he
  exact ⟨fun L _ p hp => oblique_cross_posSemidef (w t) (hn 6).le hd.le p hp,
    fun m _ p hp => axial_cross_posSemidef (w t) (hn 3).le (hn 4).le (hn 6).le he.le p hp⟩

#print axioms eventually_all_cross_matrices

end IsingScaling.Rotor.PressureSelection.SevenSeams

