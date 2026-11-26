import MathlibProbe.ReflectedLatticePacket
import MathlibProbe.IsingOffOriginPackets
import MathlibProbe.IsingSpatialPacketDifferences
import MathlibProbe.SpatialEnvelopeDoubling

/-! Off-plane reflected sites allow both parities of each displacement.
A signed two-site stencil and its two diagonal terms are evaluated in the
same kernel. Taking the tail supremum only after controlling those diagonal
terms keeps the envelope needed for the translated-block bootstrap. -/
noncomputable section
open Finset Filter
open scoped BigOperators
namespace IsingScaling.GeneralizedNormalDifference
open NormalDifference
private lemma linear_three (j : ℕ) (a b c : ℝ) (f g h : ℕ → ℝ) :
    (Packet.diff^[j]) (fun n => a*f n + b*g n + c*h n) =
      fun n => a*(Packet.diff^[j]) f n+b*(Packet.diff^[j]) g n+c*(Packet.diff^[j]) h n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext n
    simp only [Function.iterate_succ_apply',ih,Packet.diff]
    ring
private lemma shifted_tip (d : PacketNormal) {z : Site} (hz : 0≤tip d z) (n : ℕ) :
    0≤tip d (step d n+z) := by
  cases d <;> simp [tip,step] at * <;> omega

private lemma shifted_displacement (d : PacketNormal) (w z : Site) (p q : ℕ) :
    (step d p + w) - refl d (step d q + z) = step d ((p+q:ℕ):ℤ)+w-refl d z := by
  ext i
  cases d <;> fin_cases i <;> simp [step,NormalDifference.refl] <;> ring

private lemma kernel_symm {g : Site → ℝ} (hcub : Packet.CubicKernel g) (d : PacketNormal) (w z : Site) (m : ℕ) :
    kernel d g w z m = kernel d g z w m := by
  cases d with
  | axis =>
    let S := signedPerm (Equiv.refl _) (fun i => decide (i≠0))
    have hs : S (step .axis m + w - refl .axis z) = step .axis m + z - refl .axis w := by
      have hh (v : Site) : S v = ![v 0,-v 1,-v 2] := by ext i; fin_cases i <;> rfl
      rw [hh]; ext i; fin_cases i <;> (simp [step,NormalDifference.refl,Matrix.vecHead,Matrix.vecTail]; try ring)
    exact (hcub _ _ _).symm.trans (congrArg g hs)
  | faceDiagonal =>
    let S := signedPerm (Equiv.swap 0 1) (fun _ => true)
    have hs : S (step .faceDiagonal m + w - refl .faceDiagonal z) =
        step .faceDiagonal m + z - refl .faceDiagonal w := by
      have hh (v : Site) : S v = ![-v 1,-v 0,-v 2] := by ext i; fin_cases i <;> rfl
      rw [hh]; ext i; fin_cases i <;> (simp [step,NormalDifference.refl,Matrix.vecHead,Matrix.vecTail]; try ring)
    exact (hcub _ _ _).symm.trans (congrArg g hs)

/-- Complete monotonicity of every signed stencil of finitely many closed-half-space sites. -/
theorem packet_positive {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1)
    (d : PacketNormal) (form : Packet.SiteReflectedPositive g (tip d) (refl d)) {ι : Type} [Fintype ι] (Z : ι → Site) (hZ : ∀ i, 0≤tip d (Z i))
    (c : ι → ℝ) (j n : ℕ) :
    0 ≤ (Packet.diff^[j]) (evenPacket c (fun m i k => kernel d g (Z i) (Z k) m)) n := by
  apply Packet.completeMonotone_of_site_reflection hbound (tip d) (refl d) form
    (fun n i => step d n + Z i) (fun n i => shifted_tip d (hZ i) n)
  intro p q i k
  rw [shifted_displacement]
  rfl

/-- Polarization of the actual complete-monotone packets, including noncoplanar
end labels. These offsets contain both parity choices of the normal layer. -/
theorem polarized_decay_of_site_form {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1)
    (hcub : Packet.CubicKernel g)
    (d : PacketNormal) (form : Packet.SiteReflectedPositive g (tip d) (refl d))
    (w z : Site) (hw : 0≤tip d w) (hz : 0≤tip d z)
    (j k n : ℕ) (hn : (j+1)*k≤n) :
    2*((k+1:ℕ):ℝ)^j * |(Packet.diff^[j]) (fun n => kernel d g w z (2*n)) n| ≤
      kernel d g w w (2*k)+kernel d g z z (2*k) := by
  let A (m : ℕ) := kernel d g w w (2*m)
  let B (m : ℕ) := kernel d g z z (2*m)
  let F (m : ℕ) := kernel d g w z (2*m)
  let Z : Fin 2 → Site := ![w,z]
  have hp (v : ℝ) (i m : ℕ) : 0 ≤ (Packet.diff^[i])
      (fun l => (1:ℝ)*A l + (v*v)*B l + (2*v)*F l) m := by
    let C : Fin 2 → ℝ := ![1,v]
    have hpos := packet_positive hbound d form Z (fun a => by fin_cases a; exact hw; exact hz) C i m
    have hid : evenPacket C (fun m a b => kernel d g (Z a) (Z b) m) =
        fun l => (1:ℝ)*A l + (v*v)*B l + (2*v)*F l := by
      funext l
      simp only [evenPacket,Fin.sum_univ_two,Z,C,Matrix.cons_val_zero,Matrix.cons_val_one,A,B,F]
      rw [kernel_symm hcub d z w (2*l)]; ring
    rwa [hid] at hpos
  have ha : ∀ i m, 0≤(Packet.diff^[i]) A m := by
    intro i m
    have hh := hp 0 i m
    simpa only [zero_mul,mul_zero,zero_add,add_zero,one_mul] using hh
  have hb : ∀ i m, 0≤(Packet.diff^[i]) B m := by
    intro i m
    have hh := packet_positive hbound d form (fun _ : Unit => z) (fun _ => hz) (fun _ => 1) i m
    have he : evenPacket (fun _: Unit => (1:ℝ)) (fun m _ _ => kernel d g z z m) = B := by
      funext l; simp [evenPacket,B]
    rwa [he] at hh
  have hu := hp 1 j n
  have hl := hp (-1) j n
  rw [linear_three] at hu hl
  have hbound : 2*|(Packet.diff^[j]) F n| ≤ (Packet.diff^[j]) A n + (Packet.diff^[j]) B n := by
    rcases le_total 0 ((Packet.diff^[j]) F n) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  have ht := mul_le_mul_of_nonneg_left hbound (show 0≤((k+1:ℕ):ℝ)^j by positivity)
  have ha' := Packet.decay_complete ha j k n hn
  have hb' := Packet.decay_complete hb j k n hn
  change 2*((k+1:ℕ):ℝ)^j * |(Packet.diff^[j]) F n| ≤ A k+B k
  nlinarith only [ht,ha',hb']

private theorem self_le_tail {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1)
    (d : PacketNormal) (z : Site) (hz : 0 ≤ tip d z) (k : ℕ) :
    kernel d g z z (2*k) ≤ SpatialEnvelope.tail g (2*k) := by
  let v : Site := step d (2*k:ℕ) + z - refl d z
  have hv : ((2*k:ℕ):ℤ) ≤ v 0 := by
    cases d <;> simp [v,step,NormalDifference.refl,tip,Matrix.vecHead,Matrix.vecTail] at * <;> omega
  exact SpatialEnvelope.le_tail (fun x => (le_abs_self _).trans (hbound x))
    (x:=v) ⟨0, by omega⟩

/-- Relative to the actual lattice tail at radius 2k, for all orders and
all half-space source offsets, including either parity of the chart. -/
theorem tail_difference_of_site_form {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1)
    (hcub : Packet.CubicKernel g) (d : PacketNormal)
    (form : Packet.SiteReflectedPositive g (tip d) (refl d)) (w z : Site)
    (hw : 0 ≤ tip d w) (hz : 0 ≤ tip d z)
    (j k n : ℕ) (hn : (j+1)*k ≤ n) :
    ((k+1:ℕ):ℝ)^j *
      |(Packet.diff^[j]) (fun m => kernel d g w z (2*m)) n| ≤ SpatialEnvelope.tail g (2*k) := by
  have H := polarized_decay_of_site_form hbound hcub d form w z hw hz j k n hn
  have W := self_le_tail hbound d w hw k
  have Z := self_le_tail hbound d z hz k
  linarith only [H,W,Z]



/-- Difference through `ℓ` even-layer time indices. -/
def strideDifference (ℓ : ℕ) (f : ℕ → ℝ) (n : ℕ) := f n - f (n+ℓ)

private lemma stride_commute (ℓ : ℕ) : Function.Commute Packet.diff (strideDifference ℓ) := by
  intro f
  ext n
  simp only [Packet.diff, strideDifference]
  rw [show (n+1)+ℓ = (n+ℓ)+1 by omega]
  ring

private theorem telescope_absolute (f : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (h : ∀ n, N ≤ n → |Packet.diff f n| ≤ C) (ℓ n : ℕ) (hn : N ≤ n) :
    |f n-f (n+ℓ)| ≤ (ℓ:ℝ)*C := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have T := abs_sub_le (f n) (f (n+ℓ)) (f (n+(ℓ+1)))
    have H := h (n+ℓ) (by omega)
    simp only [Packet.diff, Nat.add_assoc] at H
    rw [Nat.cast_succ]
    linarith only [T, H, ih]

private theorem stride_power_bound (f : ℕ → ℝ) (N : ℕ) (C : ℝ) (j ℓ n : ℕ)
    (h : ∀ b, N ≤ b → |(Packet.diff^[j]) f b| ≤ C) (hn : N ≤ n) :
    |((strideDifference ℓ)^[j]) f n| ≤ (ℓ:ℝ)^j*C := by
  induction j generalizing f n with
  | zero => simpa using h n hn
  | succ j ih =>
    have hj (b : ℕ) (hb : N ≤ b) : |Packet.diff (((strideDifference ℓ)^[j]) f) b| ≤ (ℓ:ℝ)^j*C := by
      rw [(stride_commute ℓ).iterate_right j f]
      exact ih (Packet.diff f) b (fun t ht => by simpa only [Function.iterate_succ_apply] using h t ht) hb
    rw [Function.iterate_succ_apply', strideDifference]
    exact (telescope_absolute _ N _ hj ℓ n hn).trans_eq (by rw [pow_succ]; ring)

 /-- A displacement of 2ℓ physical layers, at every order j, on the
actual kernel. The constant is uniform in both ℓ and all half-space offsets. -/
theorem strided_tail_difference_of_site_form {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1)
    (hcub : Packet.CubicKernel g) (d : PacketNormal)
    (form : Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d)) (w z : Site)
    (hw : 0 ≤ tip d w) (hz : 0 ≤ tip d z) (j ℓ k n : ℕ) (hn : (j+1)*k ≤ n) :
    ((k+1:ℕ):ℝ)^j * |((strideDifference ℓ)^[j]) (fun m => kernel d g w z (2*m)) n|
      ≤ (ℓ:ℝ)^j * SpatialEnvelope.tail g (2*k) := by
  let W : ℝ := ((k+1:ℕ):ℝ)^j
  have hW : 0 < W := by dsimp [W]; positivity
  have ub (b : ℕ) (hb : (j+1)*k ≤ b) :
      |(Packet.diff^[j]) (fun m => kernel d g w z (2*m)) b| ≤ SpatialEnvelope.tail g (2*k) / W := by
    apply (le_div_iff₀ hW).mpr
    rw [mul_comm]
    exact tail_difference_of_site_form hbound hcub d form w z hw hz j k b hb
  have H := stride_power_bound _ _ _ j ℓ n ub hn
  calc
    _ ≤ W * ((ℓ:ℝ)^j * (SpatialEnvelope.tail g (2*k) / W)) :=
      mul_le_mul_of_nonneg_left H hW.le
    _ = _ := by field_simp [hW.ne']

section CoordinateBounds
variable {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1) (hcub : Packet.CubicKernel g)
  (forms : ∀ d : PacketNormal, Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d))

include hbound hcub forms

/-- An axial two-step at any transverse offset, relative to the tail. -/
theorem axial_two (k : ℕ) (a b c : ℤ) (ha : 4*(k:ℤ) ≤ a) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c] - g ![a+2,b,c]| ≤ SpatialEnvelope.tail g (2*k) := by
  let w : Site := ![a-4*(k:ℤ),b,c]
  have hu := tail_difference_of_site_form hbound hcub .axis (forms .axis) w 0
    (by simp [tip,w]; omega) (by simp [tip]) 1 k (2*k) (by omega)
  have he (m : ℕ) : kernel .axis g w 0 (2*m) = g ![2*(m:ℤ)+(a-4*k),b,c] := by
    apply congrArg g; ext i; fin_cases i <;> simp [w,step,NormalDifference.refl]
  simpa only [Function.iterate_one,Packet.diff,he,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,pow_one,show 2*(2*(k:ℤ))+(a-4*k)=a by ring,
    show 2*(2*(k:ℤ)+1)+(a-4*k)=a+2 by ring] using hu

/-- A face-diagonal two-step, with both coordinate cosets included. -/
theorem diagonal_two (k : ℕ) (a b c : ℤ) (hab : 8*(k:ℤ) ≤ a-b) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c] - g ![a+2,b-2,c]| ≤ SpatialEnvelope.tail g (2*k) := by
  let w : Site := ![a-4*(k:ℤ),b+4*k,c]
  have hu := tail_difference_of_site_form hbound hcub .faceDiagonal (forms .faceDiagonal) w 0
    (by simp [tip,w]; omega) (by simp [tip]) 1 k (2*k) (by omega)
  have he (m : ℕ) : kernel .faceDiagonal g w 0 (2*m) =
      g ![2*(m:ℤ)+(a-4*k),-(2*(m:ℤ))+(b+4*k),c] := by
    apply congrArg g; ext i; fin_cases i <;> simp [w,step,NormalDifference.refl]
  simpa only [Function.iterate_one,Packet.diff,he,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,pow_one,show 2*(2*(k:ℤ))+(a-4*k)=a by ring,
    show 2*(2*(k:ℤ)+1)+(a-4*k)=a+2 by ring,
    show -(2*(2*(k:ℤ)))+(b+4*k)=b by ring,
    show -(2*(2*(k:ℤ)+1))+(b+4*k)=b-2 by ring] using hu

omit hbound forms

private lemma swap01 (a b c : ℤ) : g ![a,b,c]=g ![b,a,c] := by
  have hv : signedPerm (Equiv.swap 0 1) (fun _=>false) ![a,b,c]=![b,a,c] := by
    ext i; fin_cases i <;> rfl
  exact (hcub _ _ _).symm.trans (congrArg g hv)
private lemma swap02 (a b c : ℤ) : g ![a,b,c]=g ![c,b,a] := by
  have hv : signedPerm (Equiv.swap 0 2) (fun _=>false) ![a,b,c]=![c,b,a] := by
    ext i; fin_cases i <;> rfl
  exact (hcub _ _ _).symm.trans (congrArg g hv)
private lemma signX (a b c : ℤ) : g ![-a,b,c]=g ![a,b,c] := by
  have hv : signedPerm (Equiv.refl _) (fun i=>decide (i=0)) ![a,b,c]=![-a,b,c] := by
    ext i; fin_cases i <;> rfl
  exact (congrArg g hv).symm.trans (hcub _ _ _)
private lemma signY (a b c : ℤ) : g ![a,-b,c]=g ![a,b,c] := by
  have hv : signedPerm (Equiv.refl _) (fun i=>decide (i=1)) ![a,b,c]=![a,-b,c] := by
    ext i; fin_cases i <;> rfl
  exact (congrArg g hv).symm.trans (hcub _ _ _)

include hbound forms

/-- Turning one oblique and one longitudinal even increment gives a
transverse even increment, also when the transverse coordinate changes sign. -/
private theorem transverse_pos (k : ℕ) (a b c : ℤ) (ha : 8*(k:ℤ)+2 ≤ a) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c]-g ![a,b+2,c]| ≤ 2*SpatialEnvelope.tail g (2*k) := by
  have multri (u v w : ℝ) : ((k+1:ℕ):ℝ)*|u-v| ≤
      ((k+1:ℕ):ℝ)*|u-w| + ((k+1:ℕ):ℝ)*|v-w| := by
    rw [← mul_add, abs_sub_comm v w]
    exact mul_le_mul_of_nonneg_left (abs_sub_le u w v) (by positivity)
  by_cases hb : 8*(k:ℤ) ≤ a-(b+2)
  · have d := diagonal_two hbound hcub forms k a (b+2) c hb
    have l := axial_two hbound hcub forms k a b c (by omega)
    rw [show b+2-2=b by omega] at d
    linarith only [multri (g ![a,b,c]) (g ![a,b+2,c]) (g ![a+2,b,c]), d, l]
  · have d := diagonal_two hbound hcub forms k a (-b) c (by omega)
    rw [show -b-2 = -(b+2) by omega, signY hcub, signY hcub] at d
    have l := axial_two hbound hcub forms k a (b+2) c (by omega)
    linarith only [multri (g ![a,b,c]) (g ![a,b+2,c]) (g ![a+2,b+2,c]), d, l]

private theorem transverse_two (k : ℕ) (a b c : ℤ) (ha : 8*k+2 ≤ a.natAbs) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c]-g ![a,b+2,c]| ≤ 2*SpatialEnvelope.tail g (2*k) := by
  by_cases h : 8*(k:ℤ)+2 ≤ a
  · exact transverse_pos hbound hcub forms k a b c h
  · have t := transverse_pos hbound hcub forms k (-a) b c (by omega)
    rwa [signX hcub, signX hcub] at t

private theorem first_coordinate (k : ℕ) (a b c : ℤ)
    (hfar : 8*k+2 ≤ max a.natAbs (max b.natAbs c.natAbs)) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c]-g ![a+2,b,c]| ≤ 2*SpatialEnvelope.tail g (2*k) := by
  by_cases ha : 8*k+2 ≤ a.natAbs
  · have hT := SpatialEnvelope.tail_nonneg (fun x => (le_abs_self _).trans (hbound x)) (2*k)
    by_cases hp : 4*(k:ℤ) ≤ a
    · linarith only [axial_two hbound hcub forms k a b c hp,hT]
    · have l := axial_two hbound hcub forms k (-(a+2)) b c (by omega)
      rw [show -(a+2)+2 = -a by omega, signX hcub, signX hcub, abs_sub_comm] at l
      linarith only [l,hT]
  · by_cases hb : 8*k+2 ≤ b.natAbs
    · rw [swap01 hcub a b c,swap01 hcub (a+2) b c]
      exact transverse_two hbound hcub forms k b a c hb
    · have ht := transverse_two hbound hcub forms k c a b (by omega)
      rw [swap01 hcub a b c, swap01 hcub (a+2) b c,swap02 hcub b a c,swap02 hcub b (a+2) c]
      exact ht

/-- Every physical coordinate, both parities, with no bond-reflection
monotonicity.  The two-site buffer accommodates reversal across a sign plane. -/
theorem coordinate_two_of_site_forms (k : ℕ) (x : Site) (i : Fin 3)
    (hfar : SpatialEnvelope.outside (8*k+2) x) :
    ((k+1:ℕ):ℝ) * |g x-g (x+Pi.single i (2:ℤ))| ≤ 2*SpatialEnvelope.tail g (2*k) := by
  let p := Equiv.swap (0:Fin 3) i
  let S := signedPerm p (fun _ => false)
  have Sx (v : Site) : S v = ![v (p 0),v (p 1),v (p 2)] := by ext j; fin_cases j <;> rfl
  have Sy : S (x + Pi.single i (2:ℤ)) =
      ![x (p 0)+2,x (p 1),x (p 2)] := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [Sx,p,Pi.single_apply] <;> decide
  obtain ⟨j,hj⟩ := hfar
  obtain ⟨j,rfl⟩ := p.surjective j
  have hm : 8*k+2 ≤ max (x (p 0)).natAbs (max (x (p 1)).natAbs (x (p 2)).natAbs) := by
    fin_cases j
    · exact hj.trans (le_max_left _ _)
    · exact hj.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact hj.trans ((le_max_right _ _).trans (le_max_right _ _))
  have H := first_coordinate hbound hcub forms k (x (p 0)) (x (p 1)) (x (p 2)) hm
  calc
    _ = ((k+1:ℕ):ℝ) * |g (S x)-g (S (x+Pi.single i (2:ℤ)))| := by
      rw [show g (S x) = g x from hcub p _ x,
        show g (S (x+Pi.single i (2:ℤ))) = g (x+Pi.single i (2:ℤ)) from hcub p _ _]
    _ ≤ _ := by simpa only [Sy, Sx x] using H

end CoordinateBounds

#print axioms packet_positive
#print axioms strided_tail_difference_of_site_form
#print axioms tail_difference_of_site_form
#print axioms coordinate_two_of_site_forms

end IsingScaling.GeneralizedNormalDifference
