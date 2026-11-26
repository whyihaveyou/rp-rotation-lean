import MathlibProbe.RotorPrecisionPhysicalSplit
import MathlibProbe.RotorLocalGibbsLimit
import MathlibProbe.RotorPhysicalAdmissibleVariations

/-! # Positive sums of the actual periodized rotor couplings

At fixed period and fixed pair of physical sites, periodization is the
sum over one displacement fibre. This functional on lattice ℓ¹ has norm
at most one. The reflected matrix therefore depends continuously and
linearly on the physical lattice coupling. The cone of positive
semidefinite finite matrices is closed and contains the nonnegative
finite sums of the reflected resolvents, so it contains their positive
summable series, without changing the order of the volume and index
quantifiers.

The nearest-neighbour coupling has a positive cross matrix on the
strict half. Its periodization is exactly the six-step matrix, counting
every displacement separately. At a site reflection, the tests at 0
and its normal neighbour have bare nearest-neighbour reflected matrix
[[0, β], [β, 0]] on a torus of period at least four. The fixed wall is
integrated with the common half energy. The strictly opposite crossing
term enters the Gibbs factorization.
-/

noncomputable section
open scoped Classical Topology
open Finset Filter Matrix
namespace IsingScaling.Rotor.PressureSelection.PeriodicCouplingMixture
open LatticeWalk PeriodizedWalk PhysicalSplit
universe u

private theorem restricted_summable {T : Type*} [DecidableEq T] (D : Site → T → T)
    (f : LatticeL1) (x y : T) :
    Summable (fun z => if D z x=y then f z else 0) :=
  f.2.summable_of_one.norm.of_norm_bounded fun z => by by_cases h : D z x=y <;> simp [h]

/-- One physical matrix entry is a bounded linear functional on lattice ℓ¹. -/
def entry {T : Type*} [DecidableEq T] (D : Site → T → T) (x y : T) : LatticeL1 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    ({ toFun := fun f : LatticeL1 => Seam.periodizeSeries D f x y
       map_add' := by
         intro f g
         unfold Seam.periodizeSeries
         rw [←(restricted_summable D f x y).tsum_add (restricted_summable D g x y)]
         exact tsum_congr fun z => by by_cases h : D z x=y <;> simp [h]
       map_smul' := by
         intro r f
         change Seam.periodizeSeries D (r • f : LatticeL1) x y = r * Seam.periodizeSeries D f x y
         unfold Seam.periodizeSeries
         rw [←tsum_mul_left]
         exact tsum_congr fun z => by by_cases h : D z x=y <;> simp [h] } : LatticeL1 →ₗ[ℝ] ℝ)
    1 (by
      intro f
      change ‖Seam.periodizeSeries D f x y‖ ≤ 1*‖f‖
      rw [one_mul]
      calc
        ‖Seam.periodizeSeries D f x y‖ ≤ ∑' z, ‖if D z x=y then f z else 0‖ :=
          norm_tsum_le_tsum_norm (restricted_summable D f x y).norm
        _ ≤ ∑' z, ‖f z‖ := (restricted_summable D f x y).norm.tsum_le_tsum
          (fun z => by by_cases h : D z x=y <;> simp [h]) f.2.summable_of_one.norm
        _ = ‖f‖ := by simp [lp.norm_eq_tsum_rpow (by norm_num : 0<(1:ENNReal).toReal)])

private def folded {T ι : Type*} [DecidableEq T] (D : Site → T → T) (p q : ι → T) :
    LatticeL1 →L[ℝ] Matrix ι ι ℝ where
  toFun f := Matrix.of fun i j => entry D (p i) (q j) f
  map_add' f g := by ext i j; exact (entry D (p i) (q j)).map_add f g
  map_smul' r f := by ext i j; exact (entry D (p i) (q j)).map_smul r f
  cont := continuous_pi fun i => continuous_pi fun j => (entry D (p i) (q j)).continuous

private theorem folded_series {T ι κ : Type*} [DecidableEq T] [Fintype ι] (D : Site → T → T)
    (p q : ι → T) (α : κ → ℝ) (ha : ∀ j, 0 ≤ α j) (K : κ → LatticeL1)
    (hs : Summable (fun j => α j • K j))
    (hK : ∀ j, (Matrix.of fun i l => Seam.periodizeSeries D (K j) (p i) (q l)).PosSemidef) :
    (Matrix.of fun i l => Seam.periodizeSeries D (∑' j, α j • K j : LatticeL1) (p i) (q l)).PosSemidef := by
  let M := folded D p q
  apply Matrix.posSemidef_is_closed.mem_of_tendsto (b:=atTop)
    (f:=fun s : Finset κ => M (∑ j ∈ s, α j • K j)) (M.continuous.continuousAt.tendsto.comp hs.hasSum)
  apply Eventually.of_forall
  intro s
  rw [map_sum]
  exact Matrix.posSemidef_sum s fun j _ => by
    rw [map_smul]
    exact (hK j).smul (ha j)

/-- A summable positive series of the same lattice kernels retains
every complete fixed-wall test, simultaneously for all periods. -/
theorem positiveSeries {κ : Type*} (α : κ → ℝ) (ha : ∀ j, 0≤α j) (K : κ → LatticeL1)
    (hs : Summable (fun j => α j • K j)) (hK : ∀ j, PeriodicCovarianceForms.{u} (K j)) :
    PeriodicCovarianceForms.{u} (∑' j, α j • K j : LatticeL1) := by
  constructor
  · intro L _ s ι _ p hp
    exact folded_series Seam.adaptedDestination p (fun i => DiagonalSeam.shiftedMirror s (p i))
      α ha K hs fun j => (hK j).diagonal s p hp
  · intro L _ s ι _ p hp
    exact folded_series Seam.baseMove p (fun i => CubicSeam.shiftedBond s (p i))
      α ha K hs fun j => (hK j).bond s p hp
  · intro L _ ι _ p hp
    exact folded_series Seam.baseMove p (fun i => CubicSeam.siteMirror (2*L) (p i))
      α ha K hs fun j => (hK j).site p hp

/-- The exact hypotheses on the interaction in the finite Gibbs
factorization. Fixed-wall interactions are included in the half energies. -/
structure GibbsHalf {T : Type*} [DecidableEq T] (H : Half T) (D : Site → T → T)
    (J : Profile) : Prop where
  symmetric : ∀ x y, Seam.periodizeSeries D J x y=Seam.periodizeSeries D J y x
  reflected : ∀ x y, Seam.periodizeSeries D J (H.refl x) (H.refl y)=Seam.periodizeSeries D J x y
  cross : (Matrix.of fun x y : H.Plus => Seam.periodizeSeries D J x.val (H.refl y.val)).PosSemidef

private theorem entry_sum {T κ : Type*} [DecidableEq T] (D : Site → T → T) (x y : T)
    (α : κ → ℝ) (K : κ → LatticeL1) (hs : Summable (fun j => α j • K j)) :
    Seam.periodizeSeries D (∑' j, α j • K j : LatticeL1) x y =
        ∑' j, α j*Seam.periodizeSeries D (K j) x y := by
  change (entry D x y) (∑' j, α j • K j) = _
  rw [(entry D x y).map_tsum hs]
  exact tsum_congr fun j => (entry D x y).map_smul (α j) (K j)

theorem GibbsHalf.positiveSeries {T κ : Type*} [DecidableEq T] [Fintype T]
    {H : Half T} {D : Site → T → T} (α : κ → ℝ) (ha : ∀ j, 0≤α j)
    (K : κ → LatticeL1) (hs : Summable (fun j => α j • K j))
    (hK : ∀ j, GibbsHalf H D (K j)) : GibbsHalf H D (∑' j, α j • K j : LatticeL1) where
  symmetric x y := by
    rw [entry_sum D x y α K hs,entry_sum D y x α K hs]
    exact tsum_congr fun j => congrArg (α j * ·) ((hK j).symmetric x y)
  reflected x y := by
    rw [entry_sum D _ _ α K hs,entry_sum D x y α K hs]
    exact tsum_congr fun j => congrArg (α j * ·) ((hK j).reflected x y)
  cross := folded_series D Subtype.val (fun j : H.Plus => H.refl j.val) α ha K hs
    (fun j => (hK j).cross)

theorem GibbsHalf.add_nonneg_smul {T : Type*} [DecidableEq T] [Fintype T]
    {H : Half T} {D : Site → T → T} {f g : LatticeL1} (hf : GibbsHalf H D f)
    (hg : GibbsHalf H D g) {r : ℝ} (hr : 0≤r) : GibbsHalf H D (f+r • g : LatticeL1) := by
  have he (x y : T) : Seam.periodizeSeries D (f+r • g : LatticeL1) x y =
      Seam.periodizeSeries D f x y+r*Seam.periodizeSeries D g x y := by
    change (entry D x y) (f+r • g) = _
    rw [map_add,map_smul]
    rfl
  constructor
  · intro x y
    rw [he,he,hf.symmetric x y,hg.symmetric x y]
  · intro x y
    rw [he,he,hf.reflected x y,hg.reflected x y]
  · let M := folded D Subtype.val (fun j : H.Plus => H.refl j.val)
    change (M (f+r • g)).PosSemidef
    rw [map_add,map_smul]
    exact hf.cross.add (hg.cross.smul hr)

private def signedStep (u : Fin 3 × Bool) : Site := Pi.single u.1 (if u.2 then 1 else -1)

private theorem signedStep_injective : Function.Injective signedStep := by
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  have h := congrFun eq i
  have hij : i=j := by
    by_contra hn
    cases b <;> simp [signedStep,Pi.single_eq_of_ne hn] at h
  subst j
  cases b <;> cases c <;> simp [signedStep] at h ⊢

/-- The physical periodized NN coupling counts the six oriented steps of
the original lattice even when several land on the same finite site. -/
theorem nearest_eq_walk {T : Type*} [DecidableEq T] (D : Site → T → T)
    (β : ℝ) (x y : T) :
    Seam.periodizeSeries D (LocalGibbs.nearestCoupling β) x y =
      walkMatrix D (weight β 0 0) x y := by
  let E := LocalGibbs.nearestSteps
  let a (z : Site) : ℝ := β * DiagonalSeam.bit (D z x=y)
  have hs : ∑' z, (if D z x=y then LocalGibbs.nearestCoupling β z else 0) = ∑ z ∈ E, a z := by
    rw [tsum_eq_sum (s:=E) (fun z hz => by
      have hn : z ∉ LocalGibbs.nearestSteps := hz
      simp [LocalGibbs.nearestCoupling,hn])]
    apply Finset.sum_congr rfl
    intro z hz
    have hm : z ∈ LocalGibbs.nearestSteps := hz
    by_cases hd : D z x=y <;> simp [a,LocalGibbs.nearestCoupling,DiagonalSeam.bit,hd,hm]
  have hminus (i : Fin 3) : signedStep (i,false) = -unit i := by
    ext j
    by_cases h : j=i <;> simp [signedStep,unit,h,Pi.single_eq_of_ne]
  change _ = walkMatrix D _ x y
  change ∑' z, (if D z x=y then LocalGibbs.nearestCoupling β z else 0) = _
  rw [hs,show E=Finset.univ.image signedStep by rfl,Finset.sum_image signedStep_injective.injOn,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,hminus,show ∀ i, signedStep (i,true)=unit i from fun _ => rfl]
  simp [walkMatrix,a,weight,directions,Fin.sum_univ_succ,orbit,both,mul_add]

structure AllGibbsHalves (J : Profile) : Prop where
  diagonal : ∀ (L : ℕ) [NeZero L] (s : Site), GibbsHalf (shiftedAdaptedHalf L s) Seam.adaptedDestination J
  bond : ∀ (L : ℕ) [NeZero L] (s : Site), GibbsHalf (shiftedCubicBondHalf L s) Seam.baseMove J
  site : ∀ (L : ℕ) [NeZero L], GibbsHalf (cubicSiteHalf L) Seam.baseMove J

private def cubicTranslation (L : ℕ) [NeZero L] (s : Site) : Seam.Cell L ≃ Seam.Cell L where
  toFun := Seam.baseMove s
  invFun := Seam.baseMove (-s)
  left_inv x := by rw [←ordinary_add L,add_neg_cancel,ordinary_zero]
  right_inv x := by rw [←ordinary_add L,neg_add_cancel,ordinary_zero]

def cubicShiftedSite (L : ℕ) [NeZero L] (s : Site) : Half (Seam.Cell (2*L)) :=
  (cubicSiteHalf L).pull (cubicTranslation (2*L) s)

theorem AllGibbsHalves.shiftedSite {J : Profile} (h : AllGibbsHalves J)
    (L : ℕ) [NeZero L] (s : Site) : GibbsHalf (cubicShiftedSite L s) Seam.baseMove J := by
  let e := cubicTranslation (2*L) s
  let H := cubicSiteHalf L
  let S := cubicShiftedSite L s
  have he (x : Seam.Cell (2*L)) : e (S.refl x)=H.refl (e x) := e.apply_symm_apply _
  let A := Seam.ordinarySeries (2*L) J
  have ha (x y : Seam.Cell (2*L)) : A (e x) (e y)=A x y := by
    unfold A Seam.ordinarySeries Seam.periodizeSeries
    apply tsum_congr
    intro z
    have hcomm : Seam.baseMove z (e x)=e (Seam.baseMove z x) := by
      change Seam.baseMove z (Seam.baseMove s x) = Seam.baseMove s (Seam.baseMove z x)
      rw [←ordinary_add (2*L),add_comm s z,ordinary_add]
    by_cases hy : Seam.baseMove z x=y
    · simp [hcomm,hy]
    · simp [hcomm,e.injective.eq_iff,hy]
  have hs := h.site L
  constructor
  · exact hs.symmetric
  · intro x y
    change A (S.refl x) (S.refl y)=A x y
    rw [←ha (S.refl x) (S.refl y),he,he,←ha x y]
    exact hs.reflected (e x) (e y)
  · let k (x : S.Plus) : H.Plus := ⟨e x.val,x.property⟩
    have hk := hs.cross.submatrix k
    convert hk using 1
    ext x y
    change A x.val (S.refl y.val)=A (e x.val) (H.refl (e y.val))
    rw [←ha x.val (S.refl y.val),he]

theorem AllGibbsHalves.positiveSeries {κ : Type*} (α : κ → ℝ) (ha : ∀ j, 0≤α j)
    (K : κ → LatticeL1) (hs : Summable (fun j => α j • K j))
    (hf : ∀ j, AllGibbsHalves (K j)) : AllGibbsHalves (∑' j, α j • K j : LatticeL1) where
  diagonal L _ s := GibbsHalf.positiveSeries α ha K hs fun j => (hf j).diagonal L s
  bond L _ s := GibbsHalf.positiveSeries α ha K hs fun j => (hf j).bond L s
  site L _ := GibbsHalf.positiveSeries α ha K hs fun j => (hf j).site L

theorem AllGibbsHalves.add_nonneg_smul {f g : LatticeL1} (hf : AllGibbsHalves f)
    (hg : AllGibbsHalves g) {δ : ℝ} (hd : 0≤δ) : AllGibbsHalves (f+δ • g : LatticeL1) where
  diagonal L _ s := ((hf.diagonal L s).add_nonneg_smul (hg.diagonal L s) hd)
  bond L _ s := (hf.bond L s).add_nonneg_smul (hg.bond L s) hd
  site L _ := (hf.site L).add_nonneg_smul (hg.site L) hd

private theorem of_walk_matrix {T : Type*} [DecidableEq T] [Fintype T] (H : Half T)
    (D : Site → T → T) (hzero : ∀ x, D 0 x=x) (hadd : ∀ z s x, D (z+s) x=D s (D z x))
    (w : Fin 7 → ℝ) (J : Profile) (he : ∀ x y, Seam.periodizeSeries D J x y=walkMatrix D w x y)
    (hi : ∀ x y, walkMatrix D w (H.refl x) (H.refl y)=walkMatrix D w x y)
    (hc : (Matrix.of fun x y : H.Plus => walkMatrix D w x.val (H.refl y.val)).PosSemidef) :
    GibbsHalf H D J where
  symmetric x y := by
    rw [he,he]
    exact (walkMatrix_isHermitian D hzero hadd w).apply y x
  reflected x y := by rw [he,he,hi]
  cross := by simpa only [he] using hc

/-- The nearest-neighbour coupling has the three Gibbs reflection forms
including the full cross-block of the physical periodic energy. -/
theorem nearest_all {β : ℝ} (hβ : 0≤β) : AllGibbsHalves (LocalGibbs.nearestCoupling β) := by
  let w := weight β 0 0
  have hw₃ : 0≤w 3 := le_rfl
  have hw₄ : 0≤w 4 := le_rfl
  have hw₆ : 0≤w 6 := le_rfl
  have hd : 2*w 6 ≤ w 3 := by change 2*(0:ℝ) ≤ 0; norm_num
  have hax : 2*w 3+2*w 4+4*w 6 ≤ w 0 := by
    change 2*0+2*0+4*0≤β
    simpa using hβ
  constructor
  · intro L _ s
    apply of_walk_matrix (shiftedAdaptedHalf L s) _ (adapted_zero L) (adapted_add L) w _
      (nearest_eq_walk _ β) (SevenSeams.shifted_oblique_walk_invariant w rfl rfl s)
    exact SevenSeams.shifted_oblique_cross_posSemidef w hw₆ hd s
      (fun x : (shiftedAdaptedHalf L s).Plus => x.val) (fun x => x.property)
  · intro L _ s
    apply of_walk_matrix (shiftedCubicBondHalf L s) _ (ordinary_zero (2*L)) (ordinary_add (2*L)) w _
      (nearest_eq_walk _ β) (SevenSeams.shifted_axial_walk_invariant w s)
    exact SevenSeams.shifted_axial_cross_posSemidef w hw₃ hw₄ hw₆ hax s
      (fun x : (shiftedCubicBondHalf L s).Plus => x.val) (fun x => x.property)
  · intro L _
    apply of_walk_matrix (cubicSiteHalf L) _ (ordinary_zero (2*L)) (ordinary_add (2*L)) w _
      (nearest_eq_walk _ β) (SevenSeams.coordinate_site_walk_invariant w)
    have he : (Matrix.of fun x y : (cubicSiteHalf L).Plus =>
        walkMatrix Seam.baseMove w x.val (CubicSeam.siteMirror (2*L) y.val)) = 0 := by
      ext x y
      exact SevenSeams.coordinate_site_cross_zero w x.val y.val x.property y.property
    rw [show (cubicSiteHalf L).refl=CubicSeam.siteMirror (2*L) by rfl,he]
    exact Matrix.PosSemidef.zero

private theorem of_walk_inverse {T : Type*} [Fintype T] [DecidableEq T] (H : Half T)
    (D : Site → T → T) (hzero : ∀ x, D 0 x=x) (hadd : ∀ z s x, D (z+s) x=D s (D z x))
    (w : Fin 7 → ℝ) (m : ℝ) (J : Profile)
    (he : Matrix.of (Seam.periodizeSeries D J)=(Half.precision m (walkMatrix D w))⁻¹)
    (hi : ∀ x y, walkMatrix D w (H.refl x) (H.refl y)=walkMatrix D w x y)
    (hc : (Matrix.of fun x y : H.Plus => Seam.periodizeSeries D J x.val (H.refl y.val)).PosSemidef) :
    GibbsHalf H D J := by
  let Q := Half.precision m (walkMatrix D w)
  let e : T ≃ T := ⟨H.refl,H.refl,H.invol,H.invol⟩
  have hh : Q.IsHermitian := (Matrix.isHermitian_diagonal _).sub (walkMatrix_isHermitian D hzero hadd w)
  have hsub : Q.submatrix e e=Q := by
    ext x y
    change Half.precision m (walkMatrix D w) (H.refl x) (H.refl y)=Half.precision m (walkMatrix D w) x y
    simp [Half.precision,Matrix.diagonal_apply,H.invol.injective.eq_iff,hi]
  have h := Matrix.inv_submatrix_equiv Q e e
  rw [hsub] at h
  have hv (x y : T) : Seam.periodizeSeries D J x y=Q⁻¹ x y :=
    congrFun (congrFun he x) y
  constructor
  · intro x y
    rw [hv,hv]
    exact hh.inv.apply y x
  · intro x y
    rw [hv,hv]
    exact congrFun (congrFun h.symm x) y
  · exact hc

/-- Real-space lattice perturbation with admissible seven orbital
weights yields every full-matrix symmetry and each open cross-PSD
requirement of the physical finite-volume sphere spin Gibbs law. -/
theorem curve_all (a b c m t : ℝ) (d w : Fin 7 → ℝ) (hw : w=fun j => weight a b c j+t*d j)
    (hn : ∀ j, 0≤w j) (hrow : ∑ j, w j*(2:ℝ)^(directions j).length < 1-t*m)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator)+hopping d)‖ < 1)
    (hv₀ : w 0=w 1) (hv₄ : w 4=w 5) (hv₃ : 2*w 6≤w 3) (hax : 2*w 3+2*w 4+4*w 6 ≤ w 0) :
    AllGibbsHalves (operatorCurve a b c (m • (1:Operator)+hopping d) t) := by
  constructor
  · intro L _ s
    refine of_walk_inverse (shiftedAdaptedHalf L s) _ (adapted_zero L) (adapted_add L) w (1-t*m) _ ?_
      (SevenSeams.shifted_oblique_walk_invariant w hv₀ hv₄ s) ?_
    · rw [hw]
      exact adaptedCurve_eq_inverse L a b c m t d ht
    · exact shifted_adapted_curve s a b c m t d w hw hn hrow ht hv₀ hv₄ hv₃
        (fun x : (shiftedAdaptedHalf L s).Plus => x.val) (fun x => Or.inl x.property)
  · intro L _ s
    refine of_walk_inverse (shiftedCubicBondHalf L s) _ (ordinary_zero (2*L)) (ordinary_add (2*L))
      w (1-t*m) _ ?_ (SevenSeams.shifted_axial_walk_invariant w s) ?_
    · rw [hw]
      exact ordinaryCurve_eq_inverse (2*L) a b c m t d ht
    · exact shifted_bond_curve s a b c m t d w hw hn hrow ht hax
        (fun x : (shiftedCubicBondHalf L s).Plus => x.val) (fun x => x.property)
  · intro L _
    refine of_walk_inverse (cubicSiteHalf L) _ (ordinary_zero (2*L)) (ordinary_add (2*L))
      w (1-t*m) _ ?_ (SevenSeams.coordinate_site_walk_invariant w) ?_
    · rw [hw]
      exact ordinaryCurve_eq_inverse (2*L) a b c m t d ht
    · exact coordinate_site_curve a b c m t d w hw hn hrow ht
        (fun x : (cubicSiteHalf L).Plus => x.val) (fun x => Or.inl x.property)

/-- Each slot is the lattice operator curve of the dense physical family. -/
theorem component_all {j : PhysicalVariations.Index} {s : ℝ} (h : PhysicalVariations.Allowed j s) :
    AllGibbsHalves (PhysicalVariations.component j s) := by
  obtain ⟨hn,hrow,ht,hdiag,hax,h01,h45,_⟩ := h
  unfold PhysicalVariations.component
  rw [PhysicalVariations.slot_operator]
  exact curve_all _ _ _ _ _ _ (PhysicalVariations.slotWeights j s) rfl hn hrow ht h01 h45 hdiag.le hax.le

/-- The resolvent part alone permits an even stronger test: arbitrary
finite lists on the closed positive side, with all fixed-wall sites. -/
theorem component_closed {j : PhysicalVariations.Index} {s : ℝ} (h : PhysicalVariations.Allowed j s) :
    PeriodicCovarianceForms.{u} (PhysicalVariations.component j s) := by
  obtain ⟨hn,hrow,ht,hdiag,hax,h01,h45,_⟩ := h
  unfold PhysicalVariations.component
  rw [PhysicalVariations.slot_operator]
  constructor
  · intro L _ z ι _ p hp
    exact shifted_adapted_curve z _ _ _ _ _ _ _ rfl hn hrow ht h01 h45 hdiag.le p hp
  · intro L _ z ι _ p hp
    exact shifted_bond_curve z _ _ _ _ _ _ _ rfl hn hrow ht hax.le p hp
  · intro L _ ι _ p hp
    exact coordinate_site_curve _ _ _ _ _ _ _ rfl hn hrow ht p hp

theorem mixture_closed_of_allowed (δ : ℝ) (d : PhysicalVariations.Index →₀ ℝ) (t : ℝ)
    (ht : ∀ j, PhysicalVariations.Allowed j (PhysicalVariations.speed δ d j*t)) :
    PeriodicCovarianceForms.{u} (∑' j, PhysicalVariations.alpha j •
      PhysicalVariations.component j (PhysicalVariations.speed δ d j*t) : LatticeL1) :=
  positiveSeries _ (fun j => (PhysicalVariations.alpha_pos j).le) _ (PhysicalVariations.summable_components δ d t)
    (fun j => component_closed (ht j))

theorem perturbed_all_of_allowed {β δ : ℝ} (hβ : 0≤β) (hδ : 0≤δ)
    (d : PhysicalVariations.Index →₀ ℝ) (t : ℝ)
    (ht : ∀ j, PhysicalVariations.Allowed j (PhysicalVariations.speed δ d j*t)) :
    AllGibbsHalves (PhysicalVariations.perturbed β δ d t) := by
  rw [PhysicalVariations.perturbed_eq_tsum]
  have hNN : AllGibbsHalves (PhysicalVariations.nearest β) := nearest_all hβ
  exact hNN.add_nonneg_smul (AllGibbsHalves.positiveSeries PhysicalVariations.alpha
    (fun j => (PhysicalVariations.alpha_pos j).le) _ (PhysicalVariations.summable_components δ d t)
    (fun j => component_all (ht j))) hδ

/-- On one two-sided neighbourhood before choosing a period or cut, the
actual perturbed NN plus dense-mixture coupling satisfies the full
finite-Gibbs interaction hypotheses on every physical half-torus. -/
theorem perturbed_all_eventually {β δ : ℝ} (hβ : 0≤β) (hδ : 0≤δ)
    (d : PhysicalVariations.Index →₀ ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), AllGibbsHalves (PhysicalVariations.perturbed β δ d t) := by
  filter_upwards [PhysicalVariations.all_components_allowed δ d] with t ht
  exact perturbed_all_of_allowed hβ hδ d t ht

theorem baseline_all {β δ : ℝ} (hβ : 0≤β) (hδ : 0≤δ) :
    AllGibbsHalves (PhysicalVariations.J β δ) := by
  have ht := Filter.Eventually.self_of_nhds (perturbed_all_eventually hβ hδ 0)
  simpa only [PhysicalVariations.perturbed_zero] using ht

#print axioms positiveSeries
#print axioms AllGibbsHalves.positiveSeries
#print axioms nearest_all
#print axioms curve_all
#print axioms AllGibbsHalves.shiftedSite
#print axioms mixture_closed_of_allowed
#print axioms perturbed_all_eventually
#print axioms baseline_all

end IsingScaling.Rotor.PressureSelection.PeriodicCouplingMixture
