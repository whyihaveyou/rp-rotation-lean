import MathlibProbe.RotorPrecisionLatticeSeam

/-!
# Coordinate bond reflections on the ordinary periodic cubic walk

On the even cube of side 2m reflect the first coordinate n to 1−n.
The strict positive representatives have heights 1,...,m. At two
positive sites, a step landing at the other's reflection has
height sum plus normal displacement minus one divisible by 2m.
This integer lies in [0,2m]. At zero the two heights are 1 and
the step is −1. At 2m the heights are m and the step is +1.
All original tangential displacements and their multiplicities survive.
-/

noncomputable section
namespace IsingScaling.Rotor.PressureSelection.CubicSeam

open IsingScaling.Rotor.PressureSelection.Seam
open IsingScaling.Rotor.PressureSelection.LatticeWalk
open DiagonalSeam (bit bit_and bit_or mask_posSemidef)
open Matrix IsingScaling.Rotor.PrecisionReflection

abbrev Chart (L : ℕ) := ZMod L × ZMod L × ZMod L

def cubeCoords {L : ℕ} (x : Cell L) : Chart L :=
  (↑x.1.val,↑x.2.1.val,↑x.2.2.val)

def coords (L : ℕ) (z : IsingScaling.Site) : Chart L := (↑(z 0),↑(z 1),↑(z 2))

theorem cubeCoords_bijective (L : ℕ) [NeZero L] : Function.Bijective (@cubeCoords L) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · have h (i j : Fin L) (e : (i.val:ZMod L)=(j.val:ZMod L)) : i=j := by
      apply Fin.ext
      simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using congrArg ZMod.val e
    rintro ⟨x,y,z⟩ ⟨u,v,w⟩ he
    change ((x.val:ZMod L),(y.val:ZMod L),(z.val:ZMod L))=(↑u.val,↑v.val,↑w.val) at he
    rcases Prod.mk.inj he with ⟨h₁,he⟩
    rcases Prod.mk.inj he with ⟨h₂,h₃⟩
    obtain rfl := h x u h₁
    obtain rfl := h y v h₂
    obtain rfl := h z w h₃
    rfl
  · simp [Cell, Chart, Fintype.card_prod]

def cubeEquiv (L : ℕ) [NeZero L] : Cell L ≃ Chart L :=
  Equiv.ofBijective cubeCoords (cubeCoords_bijective L)

theorem cubeCoords_baseMove (L : ℕ) [NeZero L] (z : IsingScaling.Site) (x : Cell L) :
    cubeCoords (baseMove z x) = cubeCoords x + coords L z := by
  have hr (i : Fin L) (d : ℤ) :
      (((((i.val:ℤ)+d)%L).toNat:ℕ):ZMod L) = (i.val:ZMod L)+(d:ZMod L) := by
    have hp : 0 ≤ ((i.val:ℤ)+d)%L := Int.emod_nonneg _ (by exact_mod_cast NeZero.ne L)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hp, ZMod.intCast_mod, Int.cast_add, Int.cast_natCast]
  exact Prod.ext (hr x.1 _) (Prod.ext (hr x.2.1 _) (hr x.2.2 _))

def coordMirror (L : ℕ) (x : Chart L) : Chart L := (1-x.1,x.2)

def bondMirror (L : ℕ) [NeZero L] (x : Cell L) : Cell L :=
  (cubeEquiv L).symm (coordMirror L (cubeCoords x))

@[simp] theorem cubeCoords_bondMirror (L : ℕ) [NeZero L] (x : Cell L) :
    cubeCoords (bondMirror L x) = coordMirror L (cubeCoords x) :=
  (cubeEquiv L).apply_symm_apply _

def OpenSide {m : ℕ} (x : Cell (2*m)) := 1 ≤ (cubeCoords x).1.val ∧ (cubeCoords x).1.val ≤ m

theorem bond_step_iff {m : ℕ} [NeZero m] (x y : Cell (2*m))
    (hx : OpenSide x) (hy : OpenSide y) (d : IsingScaling.Site) (hd : -1 ≤ d 0 ∧ d 0 ≤ 1) :
    baseMove d x = bondMirror (2*m) y ↔
     (((cubeCoords x).1.val=1 ∧ (cubeCoords y).1.val=1 ∧ d 0= -1) ∨
      ((cubeCoords x).1.val=m ∧ (cubeCoords y).1.val=m ∧ d 0=1)) ∧
     (cubeCoords x).2.1+(d 1:ZMod (2*m)) = (cubeCoords y).2.1 ∧
     (cubeCoords x).2.2+(d 2:ZMod (2*m)) = (cubeCoords y).2.2 := by
  let p := (cubeCoords x).1
  let q := (cubeCoords y).1
  let s : ℤ := (p.val:ℤ)+q.val+d 0-1
  change 1 ≤ p.val ∧ p.val ≤ m at hx
  change 1 ≤ q.val ∧ q.val ≤ m at hy
  have hc : p+(d 0:ZMod (2*m))=1-q ↔ (s:ZMod (2*m))=0 := by
    simp only [s,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one,ZMod.natCast_zmod_val]
    constructor <;> intro he <;> linear_combination he
  have hnorm : p+(d 0:ZMod (2*m))=1-q ↔
      (p.val=1 ∧ q.val=1 ∧ d 0= -1) ∨ (p.val=m ∧ q.val=m ∧ d 0=1) := by
    rw [hc,ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hlo : 0≤s := by unfold s; omega
    constructor
    · intro he
      by_cases hz : s=0
      · left; unfold s at hz; omega
      · have ht := Int.le_of_dvd (by omega : 0<s) he
        right; unfold s at ht; omega
    · rintro (⟨h,h',h''⟩|⟨h,h',h''⟩)
      · exact ⟨0, by unfold s; omega⟩
      · exact ⟨1, by unfold s; omega⟩
  rw [← (cubeCoords_bijective (2*m)).injective.eq_iff,cubeCoords_baseMove,cubeCoords_bondMirror]
  change (p+(d 0:ZMod (2*m)),(cubeCoords x).2.1+(d 1:ZMod (2*m)),(cubeCoords x).2.2+(d 2:ZMod (2*m))) =
     (1-q,(cubeCoords y).2.1,(cubeCoords y).2.2) ↔ _
  rw [Prod.mk.injEq,Prod.mk.injEq,hnorm]

def physicalWalk (L : ℕ) [NeZero L] (a b c : ℝ) (x y : Cell L) : ℝ :=
  step a b c (fun d => bit (baseMove d x = y)) 0

def tangentRead {L : ℕ} (x y : Cell L) (i j : ℤ) : ℝ :=
  bit ((cubeCoords x).2.1+(i:ZMod L)=(cubeCoords y).2.1 ∧
       (cubeCoords x).2.2+(j:ZMod L)=(cubeCoords y).2.2)

def nineTerms (a b c : ℝ) (v : ℤ → ℤ → ℝ) : ℝ :=
  a*v 0 0+b*(v (-1) 0+v 1 0+v 0 (-1)+v 0 1)+
    c*(v (-1) (-1)+v 1 1+v (-1) 1+v 1 (-1))

private theorem restricted_step (a b c lo hi : ℝ) (f : Profile) (v : ℤ → ℤ → ℝ)
    (hf : ∀ d : IsingScaling.Site, (-1 ≤ d 0 ∧ d 0 ≤ 1) →
      f d = (lo*bit (d 0= -1)+hi*bit (d 0=1))*v (d 1) (d 2)) :
    step a b c f 0 = (lo+hi)*nineTerms a b c v := by
  classical
  simp (disch := decide)
    [step, directions, weight, Fin.sum_univ_succ, orbit, both, hf, unit,bit, nineTerms]
  ring

theorem bond_step_bit {m : ℕ} [NeZero m] (x y : Cell (2*m)) (hx : OpenSide x) (hy : OpenSide y)
    (d : IsingScaling.Site) (hd : -1 ≤ d 0 ∧ d 0 ≤ 1) :
    bit (baseMove d x=bondMirror (2*m) y) =
      (bit ((cubeCoords x).1.val=1 ∧ (cubeCoords y).1.val=1)*bit (d 0= -1)+
       bit ((cubeCoords x).1.val=m ∧ (cubeCoords y).1.val=m)*bit (d 0=1))*tangentRead x y (d 1) (d 2) := by
  let lo := (cubeCoords x).1.val=1 ∧ (cubeCoords y).1.val=1
  let hi := (cubeCoords x).1.val=m ∧ (cubeCoords y).1.val=m
  let v := (cubeCoords x).2.1+(d 1:ZMod (2*m))=(cubeCoords y).2.1 ∧
    (cubeCoords x).2.2+(d 2:ZMod (2*m))=(cubeCoords y).2.2
  have he : (baseMove d x=bondMirror (2*m) y) ↔ ((lo ∧ d 0= -1) ∨ (hi ∧ d 0=1)) ∧ v := by
    rw [bond_step_iff x y hx hy d hd]
    dsimp [lo,hi,v]
    tauto
  have hdis : ¬((lo ∧ d 0= -1) ∧ (hi ∧ d 0=1)) := by omega
  change bit (baseMove d x=bondMirror (2*m) y) =
    (bit lo*bit (d 0= -1)+bit hi*bit (d 0=1))*bit v
  rw [propext he,bit_and _ v,bit_or hdis,bit_and lo _,bit_and hi _]

theorem physical_bond_cross_entry {m : ℕ} [NeZero m] (a b c : ℝ) (x y : Cell (2*m))
    (hx : OpenSide x) (hy : OpenSide y) :
    physicalWalk (2*m) a b c x (bondMirror (2*m) y) =
    (bit ((cubeCoords x).1.val=1 ∧ (cubeCoords y).1.val=1) +
     bit ((cubeCoords x).1.val=m ∧ (cubeCoords y).1.val=m))*nineTerms a b c (tangentRead x y) :=
  restricted_step _ _ _ _ _ _ _ (bond_step_bit x y hx hy)

#print axioms physical_bond_cross_entry

abbrev Tangent (L : ℕ) := ZMod L × ZMod L

def shift (L : ℕ) (i j : ℤ) : Tangent L ≃ Tangent L :=
  Equiv.addRight ((i:ZMod L),(j:ZMod L))

def readAt {L : ℕ} (p q : Tangent L) (i j : ℤ) : ℝ :=
  bit (p.1+(i:ZMod L)=q.1 ∧ p.2+(j:ZMod L)=q.2)

private def pairAt {L : ℕ} [NeZero L] (p q : Tangent L) (e : Tangent L ≃ Tangent L) : ℝ :=
  (if q=e p then 1 else 0)+(if p=e q then 1 else 0)

private theorem pairAt_eq {L : ℕ} [NeZero L] (p q : Tangent L) (s t : ℤ)
    (e : Tangent L ≃ Tangent L) (he : ∀ x, e x=x+((s:ZMod L),(t:ZMod L))) :
    pairAt p q e = readAt p q s t + readAt p q (-s) (-t) := by
  classical
  have hp : q=e p ↔ p.1+(s:ZMod L)=q.1 ∧ p.2+(t:ZMod L)=q.2 := by
    rw [eq_comm,he,Prod.ext_iff]
    rfl
  have hm : p=e q ↔ p.1+(-s:ℤ)=q.1 ∧ p.2+(-t:ℤ)=q.2 := by
    rw [he,Prod.ext_iff]
    change (p.1=q.1+(s:ZMod L) ∧ p.2=q.2+(t:ZMod L)) ↔ _
    push_cast
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor
    · linear_combination h₁
    · linear_combination h₂
    · linear_combination h₁
    · linear_combination h₂
  simp only [pairAt,readAt,bit,hp,hm]
  split_ifs <;> rfl

def anisotropicNine (a b₁ b₂ c : ℝ) (v : ℤ → ℤ → ℝ) : ℝ :=
  a*v 0 0+b₁*(v (-1) 0+v 1 0)+b₂*(v 0 (-1)+v 0 1)+
    c*(v (-1) (-1)+v 1 1+v (-1) 1+v 1 (-1))

theorem tangential_anisotropic_entry {L : ℕ} [NeZero L] (a b₁ b₂ c : ℝ) (p q : Tangent L) :
    seamBlock a ![shift L 1 0,shift L 0 1,(shift L 1 0).trans (shift L 0 1),
      (shift L 1 0).trans (shift L 0 1).symm] ![b₁,b₂,c,c] p q =
      anisotropicNine a b₁ b₂ c (readAt p q) := by
  classical
  let u := shift L 1 0
  let v := shift L 0 1
  have hu := pairAt_eq p q 1 0 u (fun _ => rfl)
  have hv := pairAt_eq p q 0 1 v (fun _ => rfl)
  have hplus := pairAt_eq p q 1 1 (u.trans v) (by
    intro x
    ext <;> simp [u,v,shift])
  have hminus := pairAt_eq p q 1 (-1) (u.trans v.symm) (by
    intro x
    ext <;> simp [u,v,shift])
  have hdiag : (if p=q then a else 0)=a*readAt p q 0 0 := by
    have h : p=q ↔ p.1=q.1 ∧ p.2=q.2 := Prod.ext_iff
    by_cases he : p=q
    · simp [he,readAt,bit]
    · simp [he,readAt,bit,mt h.mpr he]
  change (if p=q then a else 0)+(∑ d : Fin 4, ![b₁,b₂,c,c] d *
    pairAt p q (![u,v,u.trans v,u.trans v.symm] d)) = _
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,hdiag,hu,hv,hplus,hminus]
  norm_num [anisotropicNine]
  ring

private theorem tangential_entry {L : ℕ} [NeZero L] (a b c : ℝ) (p q : Tangent L) :
    seamBlock a ![shift L 1 0,shift L 0 1,(shift L 1 0).trans (shift L 0 1),
      (shift L 1 0).trans (shift L 0 1).symm] ![b,b,c,c] p q = nineTerms a b c (readAt p q) := by
  rw [tangential_anisotropic_entry]
  simp only [anisotropicNine,nineTerms]
  ring

/-- Both coordinate-bond interfaces of the original cubic torus, for the full
26-step walk. No parameters occur except the physical walk weights. -/
theorem physical_bond_cross_posSemidef {m : ℕ} [NeZero m] {a b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : 4*b+4*c ≤ a) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Cell (2*m)) (hp : ∀ i, OpenSide (p i)) :
    (Matrix.of fun i j => physicalWalk (2*m) a b c (p i) (bondMirror (2*m) (p j))).PosSemidef := by
  let e (i : ι) := (cubeCoords (p i)).2
  let u := shift (2*m) 1 0
  let v := shift (2*m) 0 1
  let S := (seamBlock a ![u,v,u.trans v,u.trans v.symm] ![b,b,c,c]).submatrix e e
  have hs : S.PosSemidef := (coordinate_bond_seam_posSemidef u v hb hc ha).submatrix e
  let d i := bit ((cubeCoords (p i)).1.val=1)
  let t i := bit ((cubeCoords (p i)).1.val=m)
  have h := (mask_posSemidef hs d).add (mask_posSemidef hs t)
  convert h using 1
  ext i j
  change physicalWalk (2*m) a b c (p i) (bondMirror (2*m) (p j))=d i*S i j*d j+t i*S i j*t j
  rw [physical_bond_cross_entry a b c (p i) (p j) (hp i) (hp j)]
  have hh : S i j=nineTerms a b c (tangentRead (p i) (p j)) := tangential_entry a b c (e i) (e j)
  rw [hh,bit_and,bit_and]
  dsimp [d,t]
  ring

#print axioms physical_bond_cross_posSemidef

theorem physicalWalk_translate {L : ℕ} [NeZero L] (a b c : ℝ) (d : IsingScaling.Site)
    (x y : Cell L) :
    physicalWalk L a b c (baseMove d x) (baseMove d y)=physicalWalk L a b c x y := by
  unfold physicalWalk
  apply congrArg (fun f => step a b c f 0)
  funext z
  apply congrArg bit
  apply propext
  have hj := (cubeCoords_bijective L).injective
  conv_lhs => rw [← hj.eq_iff]
  conv_rhs => rw [← hj.eq_iff]
  simp only [cubeCoords_baseMove]
  constructor <;> intro he <;> linear_combination he

private theorem translate_cancel {L : ℕ} [NeZero L] (d : IsingScaling.Site) (x : Cell L) :
    baseMove d (baseMove (-d) x) = x := by
  apply (cubeCoords_bijective L).injective
  have hn : coords L (-d) = -coords L d := by ext <;> simp [coords]
  rw [cubeCoords_baseMove,cubeCoords_baseMove,hn]
  abel

def shiftedBond {L : ℕ} [NeZero L] (d : IsingScaling.Site) (x : Cell L) : Cell L :=
  baseMove (-d) (bondMirror L (baseMove d x))

theorem shifted_physical_bond_cross_posSemidef {m : ℕ} [NeZero m] {a b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : 4*b+4*c ≤ a)
    (d : IsingScaling.Site) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Cell (2*m)) (hp : ∀ i, OpenSide (baseMove d (p i))) :
    (Matrix.of fun i j => physicalWalk (2*m) a b c (p i) (shiftedBond d (p j))).PosSemidef := by
  have h := physical_bond_cross_posSemidef hb hc ha (fun i => baseMove d (p i)) hp
  convert h using 1
  ext i j
  change physicalWalk (2*m) a b c (p i) (shiftedBond d (p j)) = _
  rw [← physicalWalk_translate a b c d (p i) (shiftedBond d (p j))]
  simp [shiftedBond,translate_cancel]

def siteMirror (L : ℕ) [NeZero L] (x : Cell L) : Cell L :=
  (cubeEquiv L).symm (-(cubeCoords x).1,(cubeCoords x).2)

def SiteOpen {m : ℕ} (x : Cell (2*m)) := 0<(cubeCoords x).1.val ∧ (cubeCoords x).1.val<m

/-- The ordinary coordinate site mirror has no open-half crossing in the
26-step walk. The whole untruncated site set on the fixed layers remains. -/
theorem physical_site_cross_zero {m : ℕ} [NeZero m] (a b c : ℝ) (p q : Cell (2*m))
    (hp : SiteOpen p) (hq : SiteOpen q) :
    physicalWalk (2*m) a b c p (siteMirror (2*m) q)=0 := by
  let x := (cubeCoords p).1
  let y := (cubeCoords q).1
  change 0<x.val ∧ x.val<m at hp
  change 0<y.val ∧ y.val<m at hq
  have hz (d : IsingScaling.Site) (hd : -1≤d 0 ∧ d 0≤1) :
      bit (baseMove d p=siteMirror (2*m) q)=0 := by
    classical
    apply if_neg
    intro h
    have h₀ := congrArg (fun u : Cell (2*m) => (cubeCoords u).1) h
    have hsite : cubeCoords (siteMirror (2*m) q) = (-y,(cubeCoords q).2) :=
      (cubeEquiv (2*m)).apply_symm_apply _
    simp only [cubeCoords_baseMove,hsite] at h₀
    change x+(d 0:ZMod (2*m))= -y at h₀
    let s : ℤ := (x.val:ℤ)+y.val+d 0
    have hs : (s:ZMod (2*m))=0 := by
      simp only [s,Int.cast_add,Int.cast_natCast,ZMod.natCast_zmod_val]
      linear_combination h₀
    have he := Int.le_of_dvd (by unfold s; omega : 0<s) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hs)
    unfold s at he
    omega
  unfold physicalWalk
  simp (disch:=decide) [step,directions,weight,Fin.sum_univ_succ,orbit,both,hz]

#print axioms shifted_physical_bond_cross_posSemidef
#print axioms physical_site_cross_zero

end IsingScaling.Rotor.PressureSelection.CubicSeam

