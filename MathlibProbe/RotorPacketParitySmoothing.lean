import MathlibProbe.ReflectedLatticePacket
import MathlibProbe.IsingOffOriginPackets
import MathlibProbe.SpatialEnvelopeDoubling

/-! # A physical finite stencil for the even-layer spectrum

Average each lattice mark with the product tent supported on the 27 adjacent
sites. The covariance of the new marks is the double convolution below. For
either mirror one unit of inward translation puts every constituent in the
closed half lattice. Reindexing the second tent by that mirror gives the
original positive-time packet of the smoothed covariance with delay one.
The one-dimensional tent also converts a one-step increment to two
two-step increments. The measure-level proof and the normalization for the
unsmoothed susceptibility are given in SM-1--5 of the packet manuscript.
-/

noncomputable section
open Finset MeasureTheory
namespace IsingScaling.Packet.ParitySmoothing

abbrev Offset := Fin 3 × Fin 3 × Fin 3

def value (a : Fin 3) : ℤ := (a.val : ℤ) - 1
def weight (a : Fin 3) : ℝ := if a = 1 then 1/2 else 1/4
def place (a : Offset) : Site := ![value a.1, value a.2.1, value a.2.2]
def mass (a : Offset) : ℝ := weight a.1 * weight a.2.1 * weight a.2.2

theorem mass_nonneg (a : Offset) : 0 ≤ mass a := by
  have hw (i : Fin 3) : 0 ≤ weight i := by unfold weight; split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)

theorem sum_mass : ∑ a : Offset, mass a = 1 := by
  simp only [Fintype.sum_prod_type, mass, Fin.sum_univ_three]
  norm_num [show weight 0 = 1/4 by rfl, show weight 1 = 1/2 by rfl,
    show weight 2 = 1/4 by rfl]

/-- The actual same-stencil two-site function after replacing each mark by
the finite weighted sum. -/
def smooth (g : Site → ℝ) (z : Site) : ℝ :=
  ∑ a : Offset, ∑ b : Offset, mass a * mass b * g (z + place a - place b)

theorem smooth_nonneg {g : Site → ℝ} (h : ∀ x, 0 ≤ g x) (z : Site) :
    0 ≤ smooth g z :=
  sum_nonneg fun a _ => sum_nonneg fun b _ =>
    mul_nonneg (mul_nonneg (mass_nonneg a) (mass_nonneg b)) (h _)

def tip : Bool → Site → ℤ
  | false, z => z 0
  | true, z => z 0 - z 1

def reflection : Bool → Site → Site
  | false, z => signedPerm (Equiv.refl _) (fun k => decide (k = 0)) z
  | true, z => signedPerm (Equiv.swap 0 1) (fun _ => false) z

def layered : Bool → ℤ → ℤ → ℤ → Site
  | false, m, x, y => ![m,x,y]
  | true, m, x, y => ![x+m,x-m,y]

private def offsetMirror : Bool → Equiv.Perm Offset
  | false => Equiv.prodCongr (Equiv.swap 0 2) (Equiv.refl _)
  | true => { toFun := fun p => (p.2.1,p.1,p.2.2),
              invFun := fun p => (p.2.1,p.1,p.2.2),
              left_inv := fun _ => rfl, right_inv := fun _ => rfl }

private theorem mass_mirror (d : Bool) (a : Offset) : mass (offsetMirror d a) = mass a := by
  rcases a with ⟨i,j,k⟩
  cases d
  · have hi : weight (Equiv.swap 0 2 i) = weight i := by fin_cases i <;> rfl
    change weight (Equiv.swap 0 2 i) * weight j * weight k = _
    rw [hi]
    rfl
  · change weight j * weight i * weight k = weight i * weight j * weight k
    ring

private theorem place_mirror (d : Bool) (a : Offset) :
    place (offsetMirror d a) = reflection d (place a) := by
  rcases a with ⟨i,j,k⟩
  cases d
  · fin_cases i <;> funext c <;> fin_cases c <;> rfl
  · funext c; fin_cases c <;> rfl

private theorem coord_bound (i : Fin 3) : -1 ≤ value i ∧ value i ≤ 1 := by
  fin_cases i <;> norm_num [value]

theorem place_bound (a : Offset) (i : Fin 3) : -1 ≤ place a i ∧ place a i ≤ 1 := by
  fin_cases i <;> exact coord_bound _

private theorem mark_inside (d : Bool) (p : ℕ) (x y : ℤ) (a : Offset) :
    0 ≤ tip d (layered d ((p:ℤ)+1) x y + place a) := by
  have hp : 0 ≤ (p : ℤ) := Int.natCast_nonneg _
  have h₀ := coord_bound a.1
  have h₁ := coord_bound a.2.1
  cases d
  · change 0 ≤ (p:ℤ)+1+value a.1
    omega
  · change 0 ≤ x+((p:ℤ)+1)+value a.1-(x-((p:ℤ)+1)+value a.2.1)
    omega

private theorem mark_difference (d : Bool) (p q : ℕ) (x y X Y : ℤ) (a b : Offset) :
    (layered d ((p:ℤ)+1) x y + place a) -
      reflection d (layered d ((q:ℤ)+1) X Y + place b) =
    layered d ((p+q:ℕ)+2) (x-X) (y-Y) + place a - place (offsetMirror d b) := by
  rw [place_mirror]
  have h0 (z : Site) : reflection false z = ![-z 0,z 1,z 2] := by funext i; fin_cases i <;> rfl
  have h1 (z : Site) : reflection true z = ![z 1,z 0,z 2] := by funext i; fin_cases i <;> rfl
  funext c
  cases d <;> fin_cases c <;>
    simp [layered,h0,h1,place] <;> ring

private theorem packet_prod_sum {ι : Type} [Fintype ι] (a : ι × Offset → ℝ) :
    ∑ t, a t = ∑ i, ∑ b : Offset, a (i,b) := Fintype.sum_prod_type _

private theorem expand (d : Bool) {ι : Type} [Fintype ι] (g : Site → ℝ) (c : ι → ℝ)
    (x y : ι → ℤ) (n : ℕ) :
    evenPacket (fun t : ι × Offset => c t.1 * mass t.2)
      (fun m i j => g (layered d ((m:ℤ)+2) (x i.1-x j.1) (y i.1-y j.1) +
        place i.2 - place (offsetMirror d j.2))) n =
      Packet.gridPacket d (smooth g) c x y (n+1) := by
  classical
  have hrhs : Packet.gridPacket d (smooth g) c x y (n+1) =
      ∑ i, ∑ j, c i * c j * smooth g
        (layered d (((2*n:ℕ):ℤ)+2) (x i-x j) (y i-y j)) := by
    have hh : ((2*(n+1):ℕ):ℤ) = ((2*n:ℕ):ℤ)+2 := by omega
    cases d <;> simp [Packet.gridPacket, evenPacket, layered, hh]
  rw [hrhs]
  simp only [evenPacket, packet_prod_sum]
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [smooth, Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  let B (b : Offset) := c i * c j * (mass a * mass b *
    g (layered d (((2*n:ℕ):ℤ)+2) (x i-x j) (y i-y j) + place a - place b))
  change _ = ∑ b, B b
  rw [← Equiv.sum_comp (offsetMirror d) B]
  apply sum_congr rfl
  intro b _
  simp only [B,mass_mirror]
  ring

/-- A single delayed positive Hausdorff measure for all times of the
physical smoothed packet. There is no hypothesis on a second parallel mirror. -/
theorem delayed_gridPacket_of_site_form (d : Bool) (g : Site → ℝ)
    (hg : ∀ z, |g z| ≤ 1) (hr : Packet.SiteReflectedPositive g (tip d) (reflection d))
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ ν : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(ν : Measure Packet.UnitInterval)) =
        Packet.gridPacket d (smooth g) c x y (n+1) := by
  let T (p : ℕ) (i : ι × Offset) := layered d ((p:ℤ)+1) (x i.1) (y i.1) + place i.2
  let K (m : ℕ) (i j : ι × Offset) := g
    (layered d ((m:ℤ)+2) (x i.1-x j.1) (y i.1-y j.1) + place i.2 - place (offsetMirror d j.2))
  let w (i : ι × Offset) := c i.1 * mass i.2
  obtain ⟨ν,hν⟩ := Packet.hausdorff_moments (a := evenPacket w K)
    (fun k n => Packet.completeMonotone_of_site_reflection hg (tip d) (reflection d) hr T
      (fun p i => mark_inside d p _ _ i.2) K
      (fun p q i j => congrArg g (mark_difference d p q _ _ _ _ i.2 j.2)) w k n)
  exact ⟨ν, fun n => (hν n).trans (expand d g c x y n)⟩

/-- One-dimensional binomial tent, applied to an arbitrary lattice field. -/
def along (v : Site) (g : Site → ℝ) (x : Site) : ℝ :=
  (g (x-v) + 2*g x + g (x+v)) / 4

/-- Exact conversion of a one-step difference to two even-step differences
on adjacent starting sites. -/
theorem along_step (v : Site) (g : Site → ℝ) (x : Site) :
    along v g (x+v) - along v g x =
    ((g (x+v+v)-g x) + (g (x+v)-g (x-v)))/4 := by
  simp only [along, add_sub_cancel_right]
  ring

private def axis (i : Fin 3) : Site := Pi.single i 1

private def atom (v : Site) (g : Site → ℝ) (x : Site) : ℝ :=
  ∑ i : Fin 3, weight i * g (x + value i • v)

private lemma atom_eq (v : Site) (g : Site → ℝ) : atom v g = along v g := by
  funext x
  rw [atom, Fin.sum_univ_three]
  simp only [show value 0 = -1 by rfl, show value 1 = 0 by rfl, show value 2 = 1 by rfl,
    show weight 0 = 1/4 by rfl, show weight 1 = 1/2 by rfl, show weight 2 = 1/4 by rfl,
    neg_one_zsmul, zero_zsmul,one_zsmul,add_zero,← sub_eq_add_neg,along]
  ring

private theorem atom_comm (u v : Site) (g : Site → ℝ) : atom u (atom v g) = atom v (atom u g) := by
  funext z
  simp only [atom, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [add_right_comm z]
  ring

private theorem place_axes (i j k : Fin 3) :
    place (i,j,k) = value i • axis 0 + value j • axis 1 + value k • axis 2 := by
  funext c
  fin_cases c <;> simp [place,axis]

private def oneSite (g : Site → ℝ) (z : Site) := ∑ a : Offset, mass a * g (z + place a)

private theorem oneSite_eq (g : Site → ℝ) :
    oneSite g = atom (axis 0) (atom (axis 1) (atom (axis 2) g)) := by
  funext z
  simp only [oneSite, atom, Fintype.sum_prod_type, Finset.mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [place_axes]
  simp only [mass, mul_assoc, add_assoc]

/-- Average in the two coordinate directions other than i. -/
def rest (i : Fin 3) (g : Site → ℝ) : Site → ℝ :=
  if i = 0 then atom (axis 1) (atom (axis 2) g)
  else if i = 1 then atom (axis 0) (atom (axis 2) g)
  else atom (axis 0) (atom (axis 1) g)

private theorem oneSite_factor (i : Fin 3) (g : Site → ℝ) :
    oneSite g = along (axis i) (rest i g) := by
  rw [oneSite_eq, ← atom_eq]
  fin_cases i
  · rfl
  · change atom (axis 0) (atom (axis 1) (atom (axis 2) g)) =
      atom (axis 1) (atom (axis 0) (atom (axis 2) g))
    exact atom_comm _ _ _
  · change atom (axis 0) (atom (axis 1) (atom (axis 2) g)) =
      atom (axis 2) (atom (axis 0) (atom (axis 1) g))
    rw [atom_comm (axis 1) (axis 2), atom_comm (axis 0) (axis 2)]

private theorem smooth_oneSite (g : Site → ℝ) (z : Site) :
    smooth g z = ∑ b : Offset, mass b * oneSite g (z - place b) := by
  simp only [smooth,oneSite,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [show z + place j - place i = z - place i + place j by abel]
  ring

/-- In every coordinate the very same covariance used in the delayed
spectral theorem is a binomial average of a positive finite stencil.
Thus its one-step increment is controlled by even-step data. -/
theorem smooth_coordinate_factor (i : Fin 3) (g : Site → ℝ) :
    ∃ h : Site → ℝ, smooth g = along (Pi.single i 1) h ∧
      ∀ z, h z = ∑ b : Offset, mass b * rest i g (z - place b) := by
  let h (z : Site) := ∑ b : Offset, mass b * rest i g (z - place b)
  refine ⟨h, ?_, fun _ => rfl⟩
  funext z
  rw [smooth_oneSite, oneSite_factor i, along]
  change (∑ b : Offset, mass b * along (axis i) (rest i g) (z-place b)) =
    ((∑ b, mass b * rest i g (z-axis i-place b)) + 2*(∑ b, mass b * rest i g (z-place b))
      + ∑ b, mass b * rest i g (z+axis i-place b))/4
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  refine sum_congr rfl fun b _ => ?_
  rw [along, show z-place b-axis i = z-axis i-place b by abel,
    show z-place b+axis i = z+axis i-place b by abel]
  ring

private def digits : Offset ≃ (Fin 3 → Fin 3) where
  toFun a := ![a.1, a.2.1, a.2.2]
  invFun f := (f 0,f 1,f 2)
  left_inv _ := rfl
  right_inv f := by funext j; fin_cases j <;> rfl

private def flip : Bool → Fin 3 → Fin 3
  | true, a => Equiv.swap 0 2 a
  | false, a => a

private theorem flip_twice (s : Bool) (i : Fin 3) : flip s (flip s i) = i := by
  cases s <;> fin_cases i <;> rfl

private def movedDigits (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Equiv.Perm (Fin 3 → Fin 3) where
  toFun f i := flip (s i) (f (p i))
  invFun f i := flip (s (p.symm i)) (f (p.symm i))
  left_inv f := by funext j; simp only [Equiv.apply_symm_apply, flip_twice]
  right_inv f := by funext j; simp only [Equiv.symm_apply_apply, flip_twice]

private def moved (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : Equiv.Perm Offset :=
  digits.trans ((movedDigits p s).trans digits.symm)

private theorem digits_moved (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (a : Offset) (i : Fin 3) : digits (moved p s a) i = flip (s i) (digits a (p i)) := by
  simp only [moved,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

private theorem place_digits (a : Offset) (i : Fin 3) : place a i = value (digits a i) := by
  fin_cases i <;> rfl

private theorem mass_digits (a : Offset) : mass a = ∏ i, weight (digits a i) := by
  rw [Fin.prod_univ_three]
  rfl

private theorem place_moved (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (a : Offset) :
    place (moved p s a) = signedPerm p s (place a) := by
  funext i
  change place (moved p s a) i = (if s i then -place a (p i) else place a (p i))
  rw [place_digits, digits_moved, place_digits]
  generalize digits a (p i) = k
  cases s i <;> fin_cases k <;> rfl

private theorem mass_moved (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (a : Offset) :
    mass (moved p s a) = mass a := by
  have hf (b : Bool) (i : Fin 3) : weight (flip b i) = weight i := by
    cases b <;> fin_cases i <;> rfl
  simp only [mass_digits,digits_moved,hf]
  exact Equiv.prod_comp p (fun i => weight (digits a i))

private theorem double_reindex {T : Type} [Fintype T] (e : Equiv.Perm T) (P : T → T → ℝ) :
    ∑ a, ∑ b, P (e a) (e b) = ∑ a, ∑ b, P a b := by
  simp_rw [Equiv.sum_comp e]
  exact Equiv.sum_comp e (fun a => ∑ b, P a b)

theorem smooth_cubic {g : Site → ℝ} (hc : CubicKernel g) : CubicKernel (smooth g) := by
  intro p s z
  let e := moved p s
  let S := signedPerm p s
  let P (a b : Offset) := mass a * mass b * g (S z + place a - place b)
  change (∑ a, ∑ b, P a b) = _
  rw [← double_reindex e P]
  unfold smooth
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have hd : S z + S (place a) - S (place b) = S (z + place a - place b) := by
    funext i
    change ((if s i then -z (p i) else z (p i)) +
        (if s i then -place a (p i) else place a (p i)) -
        (if s i then -place b (p i) else place b (p i))) =
      (if s i then -(z (p i)+place a (p i)-place b (p i)) else _)
    cases s i <;> simp <;> ring
  simp only [P,e,mass_moved,place_moved]
  change mass a * mass b * g (S z + S (place a) - S (place b)) = _
  rw [hd, hc p s]

theorem smooth_stationary_positive {g : Site → ℝ} (hg : SpatialEnvelope.StationaryPositive g) :
    SpatialEnvelope.StationaryPositive (smooth g) := by
  intro ι _ x c
  have h := hg (fun i : ι × Offset => x i.1 + place i.2) (fun i => c i.1 * mass i.2)
  apply h.trans_eq
  simp only [packet_prod_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simp only [smooth,Finset.mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [show x i + place a - (x j + place b) = (x i - x j) + place a - place b by abel]
  ring

/-- Using the pair of central marks alone bounds the original point by
64 times the positively smoothed covariance. -/
theorem original_le_smooth {g : Site → ℝ} (h : ∀ z, 0 ≤ g z) (z : Site) :
    g z ≤ 64 * smooth g z := by
  let o : Offset := (1,1,1)
  let P (a b : Offset) := mass a * mass b * g (z + place a - place b)
  have hn (a b : Offset) : 0 ≤ P a b := mul_nonneg (mul_nonneg (mass_nonneg a) (mass_nonneg b)) (h _)
  have h₁ : P o o ≤ ∑ b, P o b := single_le_sum (fun b _ => hn o b) (mem_univ o)
  have h₂ : ∑ b, P o b ≤ ∑ a, ∑ b, P a b :=
    single_le_sum (fun a _ => sum_nonneg fun b _ => hn a b) (mem_univ o)
  have hm : mass o = (1/8:ℝ) := by norm_num [mass,o,weight]
  have hh := h₁.trans h₂
  change P o o ≤ smooth g z at hh
  simp only [P,hm,add_sub_cancel_right] at hh
  linarith only [hh]

theorem smooth_le_one {g : Site → ℝ} (h : ∀ z, g z ≤ 1) (z : Site) : smooth g z ≤ 1 := by
  calc
    _ ≤ ∑ a : Offset, ∑ b : Offset, mass a * mass b := by
      apply sum_le_sum; intro a _
      apply sum_le_sum; intro b _
      exact mul_le_of_le_one_right (mul_nonneg (mass_nonneg a) (mass_nonneg b)) (h _)
    _ = 1 := by simp only [← Finset.mul_sum,sum_mass,mul_one]

theorem tail_le_smoothed {g : Site → ℝ} (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1) (r : ℕ) :
    SpatialEnvelope.tail g r ≤ 64 * SpatialEnvelope.tail (smooth g) r := by
  have h0 := SpatialEnvelope.tail_nonneg (smooth_le_one hb) r
  apply SpatialEnvelope.tail_le (by positivity)
  intro x hx
  exact (original_le_smooth hn x).trans (mul_le_mul_of_nonneg_left
    (SpatialEnvelope.le_tail (smooth_le_one hb) hx) (by norm_num))

private def InBox (z : Site) (r : ℤ) (y : Site) : Prop :=
  ∀ j, z j-r ≤ y j ∧ y j ≤ z j+r

private def BoxDiff (g : Site → ℝ) (z : Site) (r : ℤ) (u : Site) (b : ℝ) : Prop :=
  ∀ y, InBox z r y → |g (y+u) - g y| ≤ b

private theorem atomShift_bound (i : Fin 3) (a j : Fin 3) :
    -1 ≤ (value a • axis i) j ∧ (value a • axis i) j ≤ 1 := by
  have h := coord_bound a
  by_cases hj : j = i
  · subst j
    simpa [axis] using h
  · simp [axis, Pi.single_eq_of_ne hj]

private theorem mean_diff {T : Type} [Fintype T] (w : T → ℝ) (hw : ∀ t, 0 ≤ w t)
    (hs : ∑ t, w t = 1) (X Y : T → ℝ) {b : ℝ} (h : ∀ t, |X t-Y t| ≤ b) :
    |(∑ t, w t * X t)-(∑ t, w t * Y t)| ≤ b := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ t, |w t * (X t-Y t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, w t*b := by
      apply sum_le_sum; intro t _
      rw [abs_mul, abs_of_nonneg (hw t)]
      exact mul_le_mul_of_nonneg_left (h t) (hw t)
    _ = b := by rw [← Finset.sum_mul,hs,one_mul]

private theorem atom_boxDiff (i : Fin 3) {g : Site → ℝ} {z u : Site} {r : ℤ} {b : ℝ}
    (h : BoxDiff g z (r+1) u b) : BoxDiff (atom (axis i) g) z r u b := by
  intro y hy
  have hw (a : Fin 3) : 0 ≤ weight a := by unfold weight; split_ifs <;> norm_num
  have hs : ∑ a, weight a = 1 := by
    rw [Fin.sum_univ_three]
    norm_num [show weight 0 = 1/4 by rfl, show weight 1 = 1/2 by rfl, show weight 2 = 1/4 by rfl]
  apply mean_diff weight hw hs
  intro a
  rw [add_right_comm y u]
  apply h
  intro j
  have h₁ := hy j
  have h₂ := atomShift_bound i a j
  change z j - (r+1) ≤ y j + (value a • axis i) j ∧ y j + (value a • axis i) j ≤ z j + (r+1)
  omega

private theorem rest_boxDiff (i : Fin 3) {g : Site → ℝ} {z u : Site} {r : ℤ} {b : ℝ}
    (h : BoxDiff g z (r+2) u b) : BoxDiff (rest i g) z r u b := by
  unfold rest
  have h' : BoxDiff g z (r+1+1) u b := by rw [show r+1+1 = r+2 by omega]; exact h
  split_ifs <;> exact atom_boxDiff _ (atom_boxDiff _ h')

/-- A raw two-step coordinate estimate on the radius-four collar controls
the one-step increment of the concrete 27-site averaged covariance. -/
theorem smooth_step_le {g : Site → ℝ} (x : Site) (i : Fin 3) (b : ℝ)
    (h : ∀ y : Site, (∀ j, x j-4 ≤ y j ∧ y j ≤ x j+4) →
      |g (y + Pi.single i (2:ℤ)) - g y| ≤ b) :
    |smooth g (x + Pi.single i (1:ℤ)) - smooth g x| ≤ b / 2 := by
  let v := axis i
  have hu : v+v = Pi.single i (2:ℤ) := by
    funext j
    by_cases hji : j=i
    · subst j; simp [v,axis]
    · simp [v,axis,Pi.single_eq_of_ne hji]
  obtain ⟨f,hf,hform⟩ := smooth_coordinate_factor i g
  have hraw : BoxDiff g x (2+2) (v+v) b := by rw [hu]; exact h
  have hr := rest_boxDiff i hraw
  have hnear : BoxDiff f x 1 (v+v) b := by
    intro y hy
    rw [hform,hform]
    apply mean_diff mass mass_nonneg sum_mass
    intro a
    rw [show y+(v+v)-place a = (y-place a)+(v+v) by abel]
    apply hr
    intro j
    have h₁ := hy j
    have h₂ := place_bound a j
    change x j-2 ≤ y j-place a j ∧ y j-place a j ≤ x j+2
    omega
  have H₀ := hnear x (fun j => by omega)
  have H₁ := hnear (x-v) (by
    intro j
    have hh : -1 ≤ v j ∧ v j ≤ 1 := by
      by_cases hji : j=i
      · subst j; norm_num [v,axis]
      · simp [v,axis,Pi.single_eq_of_ne hji]
    change x j-1 ≤ x j-v j ∧ x j-v j ≤ x j+1
    omega)
  rw [show x-v+(v+v) = x+v by abel] at H₁
  rw [hf]
  change |along v f (x+v) - along v f x| ≤ b/2
  rw [along_step,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4), add_assoc]
  linarith only [abs_add_le (f (x+(v+v))-f x) (f (x+v)-f (x-v)), H₀,H₁]

theorem smooth_susceptibility_pos {g : Site → ℝ} (h : ∀ z, 0 ≤ g z) (h₀ : 0 < g 0) (r : ℕ) :
    0 < susceptibility (smooth g) r := by
  have hp := original_le_smooth h 0
  have hz : (0 : Site) ∈ cube r := by simp [cube,Fintype.mem_piFinset]
  have hh : smooth g 0 ≤ susceptibility (smooth g) r :=
    Finset.single_le_sum (fun i _ => smooth_nonneg h i) hz
  linarith only [hp,h₀,hh]

/-- The physical site forms construct the full normalized delayed packet
source at every choice of scales for the explicitly smoothed correlation. -/
theorem normalizedPacketSource {g : Site → ℝ} (hg : ∀ z, |g z| ≤ 1)
    (hn : ∀ z, 0 ≤ g z) (h₀ : 0 < g 0) (hc : CubicKernel g)
    (hr : ∀ d, Packet.SiteReflectedPositive g (tip d) (reflection d)) (R : ℕ → ℕ) :
    NormalizedPacketSource (smooth g) R 1 := by
  exact ⟨fun d {_} _ c x y => delayed_gridPacket_of_site_form d g hg (hr d) c x y,
    smooth_cubic hc, fun n => smooth_susceptibility_pos hn h₀ (R n)⟩

#print axioms delayed_gridPacket_of_site_form
#print axioms along_step
#print axioms smooth_coordinate_factor
#print axioms normalizedPacketSource
end IsingScaling.Packet.ParitySmoothing
