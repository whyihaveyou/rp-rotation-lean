import MathlibProbe.RotorPrecisionReflection
import MathlibProbe.RotorPeriodicSeam
import MathlibProbe.RotorLatticeWalkResolvent
import Mathlib.Data.ZMod.Basic

/-!
# Original-lattice crossings of an adapted diagonal site mirror

Use normal height x₁+x₂ modulo 2L, together with x₂ and x₃ modulo L.
Their joint kernel is precisely the three period vectors in the pressure
torus. In these coordinates the geometric diagonal mirror sends (h,v,w) to
(−h,v−h,w). Between two strictly positive representatives, a step from the
first to the reflection of the second has normal height sum 0 or 2L after
the step. Thus both heights equal 1 and both planar step components are −1,
or both heights equal L−1 and both step components are +1. Reflection then
restores the second coordinate, while the third coordinate keeps its step.
-/

noncomputable section
namespace IsingScaling.Rotor.PressureSelection.DiagonalSeam

open IsingScaling.Rotor.PressureSelection.Seam
open IsingScaling.Rotor.PressureSelection.LatticeWalk

abbrev Chart (L : ℕ) := ZMod (2*L) × ZMod L × ZMod L

def coords (L : ℕ) (p : IsingScaling.Site) : Chart L :=
  (↑(p 0+p 1), ↑(p 1), ↑(p 2))

private theorem int_cast_eq {n : ℕ} {x y : ℤ} :
    (x : ZMod n) = (y : ZMod n) ↔ ∃ d : ℤ, x-y = (n : ℤ)*d := by
  rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
  rfl

theorem samePeriod_iff_coords (L : ℕ) (p q : IsingScaling.Site) :
    SamePeriodClass L p q ↔ coords L p = coords L q := by
  simp only [coords, Prod.mk.injEq, int_cast_eq]
  constructor
  · rintro ⟨i,j,k,hx,hy,hz⟩
    refine ⟨⟨i+j,?_⟩,⟨j,hy⟩,⟨k,hz⟩⟩
    push_cast
    linear_combination hx + hy
  · rintro ⟨⟨q₁,h₁⟩,⟨q₂,h₂⟩,⟨q₃,h₃⟩⟩
    refine ⟨q₁-q₂,q₂,q₃,?_,h₂,h₃⟩
    push_cast at h₁
    linear_combination h₁ - h₂

/-- Actual representatives from the bounded-volume pressure construction. -/
def siteCoords {L : ℕ} (p : Seam.Site L) : Chart L := coords L (representative p)

theorem siteCoords_bijective (L : ℕ) [NeZero L] : Function.Bijective (@siteCoords L) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j hij
    apply representative_injective L
    apply representative_eq_of_same_period i j
    exact (samePeriod_iff_coords L _ _).mpr hij
  · simp [Chart, Seam.Site, Cell, Fintype.card_sum, Fintype.card_prod]
    ring

def siteEquiv (L : ℕ) [NeZero L] : Seam.Site L ≃ Chart L :=
  Equiv.ofBijective siteCoords (siteCoords_bijective L)

theorem coords_add (L : ℕ) (p q : IsingScaling.Site) :
    coords L (p+q) = coords L p + coords L q := by
  ext <;> simp [coords]
  abel

theorem coords_adaptedDestination (L : ℕ) [NeZero L] (z : IsingScaling.Site) (x : Seam.Site L) :
    siteCoords (adaptedDestination z x) = siteCoords x + coords L z := by
  have h := (samePeriod_iff_coords L _ _).mp (adapted_step_same_period L z x)
  exact h.symm.trans (coords_add L _ _)

private def small {L : ℕ} : ZMod (2*L) →+* ZMod L := ZMod.castHom (dvd_mul_left _ _) _

def chartMirror {L : ℕ} (p : Chart L) : Chart L := (-p.1,p.2.1-small p.1,p.2.2)

theorem coords_geometric_mirror (L : ℕ) (x : IsingScaling.Site) :
    coords L ![-x 1,-x 0,x 2] = chartMirror (coords L x) := by
  ext <;> simp [coords, chartMirror, small, add_comm]

def adaptedMirror (L : ℕ) [NeZero L] (p : Seam.Site L) : Seam.Site L :=
  (siteEquiv L).symm (chartMirror (siteCoords p))

@[simp] theorem coords_adaptedMirror (L : ℕ) [NeZero L] (p : Seam.Site L) :
    siteCoords (adaptedMirror L p) = chartMirror (siteCoords p) :=
  (siteEquiv L).apply_symm_apply _

theorem adaptedMirror_involutive (L : ℕ) [NeZero L] : Function.Involutive (adaptedMirror L) := by
  intro x
  apply (siteCoords_bijective L).injective
  simp [chartMirror]

def OpenSide {L : ℕ} (x : Seam.Site L) := 0 < (siteCoords x).1.val ∧ (siteCoords x).1.val < L

private theorem normal_cross {L : ℕ} [NeZero L] {p q : ZMod (2*L)}
    (hp : 0 < p.val ∧ p.val < L) (hq : 0 < q.val ∧ q.val < L) {u v : ℤ}
    (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1) :
    p + ((u+v : ℤ) : ZMod (2*L)) = -q ↔
      (p.val=1 ∧ q.val=1 ∧ u= -1 ∧ v= -1) ∨
      (p.val+1=L ∧ q.val+1=L ∧ u=1 ∧ v=1) := by
  let s : ℤ := (p.val:ℤ) + q.val + u + v
  have hcast : p + ((u+v : ℤ) : ZMod (2*L)) = -q ↔ (s : ZMod (2*L))=0 := by
    simp only [s, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    constructor <;> intro he <;> linear_combination he
  rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hlo : 0 ≤ s := by unfold s; omega
  have hhi : s ≤ ((2*L:ℕ):ℤ) := by unfold s; omega
  constructor
  · intro hd
    by_cases hs : s=0
    · left; unfold s at hs; omega
    · have ht := Int.le_of_dvd (show 0 < s by omega) hd
      right; unfold s at ht; omega
  · rintro (⟨he,hf,hg,hh⟩ | ⟨he,hf,hg,hh⟩)
    · exact ⟨0, by unfold s; omega⟩
    · exact ⟨1, by unfold s; omega⟩

private theorem small_val {L : ℕ} [NeZero L] (p : ZMod (2*L)) :
    small p = (p.val : ZMod L) := by
  calc
    small p = small (p.val : ZMod (2*L)) := congrArg small (ZMod.natCast_zmod_val p).symm
    _ = _ := map_natCast _ _

/-- Exact individual physical step event on the original adapted torus. -/
theorem adapted_cross_iff {L : ℕ} [NeZero L] (x y : Seam.Site L)
    (hx : OpenSide x) (hy : OpenSide y) (z : IsingScaling.Site)
    (h₁ : -1 ≤ z 0 ∧ z 0 ≤ 1) (h₂ : -1 ≤ z 1 ∧ z 1 ≤ 1) :
    adaptedDestination z x = adaptedMirror L y ↔
      (((siteCoords x).1.val=1 ∧ (siteCoords y).1.val=1 ∧ z 0= -1 ∧ z 1= -1) ∨
       ((siteCoords x).1.val+1=L ∧ (siteCoords y).1.val+1=L ∧ z 0=1 ∧ z 1=1)) ∧
      (siteCoords x).2.1=(siteCoords y).2.1 ∧
      (siteCoords x).2.2+(z 2 : ZMod L)=(siteCoords y).2.2 := by
  let p := siteCoords x
  let q := siteCoords y
  have hc := normal_cross (p:=p.1) (q:=q.1) hx hy h₁ h₂
  have hshift (h : (p.1.val=1 ∧ q.1.val=1 ∧ z 0= -1 ∧ z 1= -1) ∨
          (p.1.val+1=L ∧ q.1.val+1=L ∧ z 0=1 ∧ z 1=1)) :
      (z 1 : ZMod L) = -small q.1 := by
    rw [small_val]
    rcases h with ⟨_,hq,_,he⟩ | ⟨_,hq,_,he⟩
    · simp [hq,he]
    · have hz : (q.1.val : ZMod L)+1=0 := by
        rw [← Nat.cast_add_one, hq, ZMod.natCast_self]
      rw [he,Int.cast_one]
      linear_combination hz
  rw [← (siteCoords_bijective L).injective.eq_iff, coords_adaptedDestination, coords_adaptedMirror]
  change (p.1+((z 0+z 1:ℤ):ZMod (2*L)), p.2.1+(z 1:ZMod L),p.2.2+(z 2:ZMod L)) =
    (-q.1,q.2.1-small q.1,q.2.2) ↔ _
  rw [Prod.mk.injEq,Prod.mk.injEq,hc]
  constructor
  · rintro ⟨h,hv,hw⟩
    refine ⟨h,?_,hw⟩
    rw [hshift h] at hv
    change p.2.1=q.2.1
    linear_combination hv
  · rintro ⟨h,hv,hw⟩
    refine ⟨h,?_,hw⟩
    change p.2.1=q.2.1 at hv
    rw [hshift h,hv]
    abel

#print axioms adapted_cross_iff

noncomputable def bit (p : Prop) : ℝ := by classical exact if p then 1 else 0

theorem bit_and (p q : Prop) : bit (p ∧ q) = bit p * bit q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit,hp,hq]

theorem bit_or {p q : Prop} (h : ¬(p ∧ q)) : bit (p ∨ q) = bit p + bit q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp_all [bit]

/-- Exactly one original step of the three-dimensional walk evaluated at a
target on the actual pressure torus. -/
def physicalWalk (L : ℕ) [NeZero L] (a b c : ℝ) (x y : Seam.Site L) : ℝ :=
  step a b c (fun z => bit (adaptedDestination z x = y)) 0

def lowerPair {L : ℕ} (x y : Seam.Site L) : Prop :=
  (siteCoords x).1.val=1 ∧ (siteCoords y).1.val=1 ∧ (siteCoords x).2.1=(siteCoords y).2.1

def upperPair {L : ℕ} (x y : Seam.Site L) : Prop :=
  (siteCoords x).1.val+1=L ∧ (siteCoords y).1.val+1=L ∧ (siteCoords x).2.1=(siteCoords y).2.1

def verticalRead {L : ℕ} (x y : Seam.Site L) (k : ℤ) : ℝ :=
  bit ((siteCoords x).2.2+(k:ZMod L)=(siteCoords y).2.2)

private theorem restricted_step (a b c lo hi : ℝ) (f : Profile) (v : ℤ → ℝ)
    (hf : ∀ z : IsingScaling.Site, (-1 ≤ z 0 ∧ z 0 ≤ 1) → (-1 ≤ z 1 ∧ z 1 ≤ 1) →
      f z = (lo*bit (z 0= -1 ∧ z 1= -1)+hi*bit (z 0=1 ∧ z 1=1))*v (z 2)) :
    step a b c f 0 = (lo+hi)*(b*v 0+c*(v (-1)+v 1)) := by
  classical
  simp (disch := decide)
    [step, directions, weight, Fin.sum_univ_succ, orbit, both, hf, unit,bit]
  ring

/-- The two disjoint boundary layers retain exactly one face-diagonal step
and its two body-diagonal companions on each tangential line. The formula
also counts both layers if the period is so short that they coincide. -/
theorem physical_cross_entry {L : ℕ} [NeZero L] (a b c : ℝ) (x y : Seam.Site L)
    (hx : OpenSide x) (hy : OpenSide y) :
    physicalWalk L a b c x (adaptedMirror L y) =
      (bit (lowerPair x y)+bit (upperPair x y))*
      (b*verticalRead x y 0+c*(verticalRead x y (-1)+verticalRead x y 1)) := by
  apply restricted_step
  intro z h₁ h₂
  let lo := z 0= -1 ∧ z 1= -1
  let hi := z 0=1 ∧ z 1=1
  let v := (siteCoords x).2.2+(z 2:ZMod L)=(siteCoords y).2.2
  have h : (adaptedDestination z x=adaptedMirror L y) ↔
      ((lowerPair x y ∧ lo) ∨ (upperPair x y ∧ hi)) ∧ v := by
    rw [adapted_cross_iff x y hx hy z h₁ h₂]
    unfold lowerPair upperPair
    dsimp [lo,hi,v]
    tauto
  have disjoint : ¬((lowerPair x y ∧ lo) ∧ (upperPair x y ∧ hi)) := by
    rintro ⟨⟨_,hl⟩,⟨_,hh⟩⟩
    have hL : z 0= -1 := hl.1
    have hH : z 0=1 := hh.1
    omega
  change bit (adaptedDestination z x=adaptedMirror L y) =
      (bit (lowerPair x y)*bit lo+bit (upperPair x y)*bit hi)*bit v
  rw [propext h, bit_and _ v, bit_or disjoint, bit_and (lowerPair x y) lo, bit_and (upperPair x y) hi]

#print axioms physical_cross_entry

open Matrix IsingScaling.Rotor.PrecisionReflection

private def thirdShift (L : ℕ) : ZMod L × ZMod L ≃ ZMod L × ZMod L :=
  (Equiv.refl (ZMod L)).prodCongr (Equiv.addRight 1)

private theorem tangential_entry (L : ℕ) [NeZero L] (b c : ℝ) (p q : ZMod L × ZMod L) :
    seamBlock b (fun _ : Unit => thirdShift L) (fun _ => c) p q =
      bit (p.1=q.1)*(b*bit (p.2=q.2)+c*(bit (p.2-1=q.2)+bit (p.2+1=q.2))) := by
  classical
  change (if p=q then b else 0) +
    (∑ _ : Unit, c*((if q=thirdShift L p then 1 else 0)+(if p=thirdShift L q then 1 else 0))) = _
  have he : q=thirdShift L p ↔ p.1=q.1 ∧ p.2+1=q.2 := by
    rw [eq_comm, Prod.ext_iff]
    rfl
  have hf : p=thirdShift L q ↔ p.1=q.1 ∧ p.2-1=q.2 := by
    rw [Prod.ext_iff]
    change (p.1=q.1 ∧ p.2=q.2+1) ↔ _
    apply and_congr_right
    intro _
    constructor <;> intro h <;> linear_combination h
  have heq : p=q ↔ p.1=q.1 ∧ p.2=q.2 := Prod.ext_iff
  simp only [Fintype.sum_unique, he, hf, heq]
  by_cases h : p.1=q.1
  · by_cases hzero : p.2=q.2 <;> by_cases hup : p.2+1=q.2 <;> by_cases hdown : p.2-1=q.2 <;>
      simp [h,hzero,hup,hdown,bit] <;> ring
  · simp [h,bit]

theorem mask_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hs : S.PosSemidef) (d : ι → ℝ) :
    (Matrix.of fun i j => d i * S i j * d j).PosSemidef := by
  let D := Matrix.diagonal d
  have hd : D.conjTranspose = D := (Matrix.isHermitian_diagonal d).eq
  have h := hs.conjTranspose_mul_mul_same D
  convert h using 1
  ext i j
  rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- The folded cross matrix of the actual 26-step adapted torus is positive
semidefinite for every finite list of open-half sites. No Fourier-matrix
hypothesis, submatrix identification, or assumption on the row sums occurs
in this statement. -/
theorem physical_oblique_cross_posSemidef {L : ℕ} [NeZero L] {b c : ℝ} (a : ℝ)
    (hc : 0 ≤ c) (hb : 2*c ≤ b) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Seam.Site L) (hp : ∀ i, OpenSide (p i)) :
    (Matrix.of fun i j => physicalWalk L a b c (p i) (adaptedMirror L (p j))).PosSemidef := by
  let e (i : ι) := (siteCoords (p i)).2
  let S := (seamBlock b (fun _ : Unit => thirdShift L) (fun _ => c)).submatrix e e
  have hs : S.PosSemidef := (oblique_site_seam_posSemidef (thirdShift L) hc hb).submatrix e
  let d (i : ι) := bit ((siteCoords (p i)).1.val=1)
  let t (i : ι) := bit ((siteCoords (p i)).1.val+1=L)
  have h := (mask_posSemidef hs d).add (mask_posSemidef hs t)
  convert h using 1
  ext i j
  change physicalWalk L a b c (p i) (adaptedMirror L (p j)) =
    d i*S i j*d j+t i*S i j*t j
  rw [physical_cross_entry a b c (p i) (p j) (hp i) (hp j)]
  have hS := tangential_entry L b c (e i) (e j)
  change S i j = _ at hS
  rw [hS]
  simp only [e,d,t,lowerPair,upperPair,bit_and,verticalRead,Int.cast_zero,Int.cast_neg,
    Int.cast_one,add_zero,sub_eq_add_neg]
  ring

#print axioms physical_oblique_cross_posSemidef

theorem physicalWalk_translate {L : ℕ} [NeZero L] (a b c : ℝ) (d : IsingScaling.Site)
    (x y : Seam.Site L) :
    physicalWalk L a b c (adaptedDestination d x) (adaptedDestination d y) =
      physicalWalk L a b c x y := by
  unfold physicalWalk
  apply congrArg (fun f => step a b c f 0)
  funext z
  apply congrArg bit
  apply propext
  have hj := (siteCoords_bijective L).injective
  conv_lhs => rw [← hj.eq_iff]
  conv_rhs => rw [← hj.eq_iff]
  simp only [coords_adaptedDestination]
  constructor <;> intro he <;> linear_combination he

private theorem adapted_translate_cancel {L : ℕ} [NeZero L] (d : IsingScaling.Site)
    (x : Seam.Site L) : adaptedDestination d (adaptedDestination (-d) x) = x := by
  apply (siteCoords_bijective L).injective
  have hneg : coords L (-d) = -coords L d := by
    ext <;> simp [coords]
    abel
  rw [coords_adaptedDestination,coords_adaptedDestination,hneg]
  abel

/-- Conjugation by an original lattice displacement; a unit step in either
of the first two coordinates gives the adjacent shifted diagonal site plane. -/
def shiftedMirror {L : ℕ} [NeZero L] (d : IsingScaling.Site) (x : Seam.Site L) : Seam.Site L :=
  adaptedDestination (-d) (adaptedMirror L (adaptedDestination d x))

theorem shifted_physical_oblique_cross_posSemidef {L : ℕ} [NeZero L] {b c : ℝ} (a : ℝ)
    (hc : 0 ≤ c) (hb : 2*c ≤ b) (d : IsingScaling.Site) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Seam.Site L) (hp : ∀ i, OpenSide (adaptedDestination d (p i))) :
    (Matrix.of fun i j => physicalWalk L a b c (p i) (shiftedMirror d (p j))).PosSemidef := by
  have h := physical_oblique_cross_posSemidef a hc hb (fun i => adaptedDestination d (p i)) hp
  convert h using 1
  ext i j
  change physicalWalk L a b c (p i) (shiftedMirror d (p j)) = _
  rw [← physicalWalk_translate a b c d (p i) (shiftedMirror d (p j))]
  simp [shiftedMirror,adapted_translate_cancel]

#print axioms shifted_physical_oblique_cross_posSemidef

end IsingScaling.Rotor.PressureSelection.DiagonalSeam

