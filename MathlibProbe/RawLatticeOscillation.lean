import MathlibProbe.ModelPacketSmoothedOscillation

/-! # Unaveraged one-step smoothing from physical site and bond mirrors

The positive axis bond mirror is at coordinate 1/2. For the diagonal the
second mirror through x₀−x₁=1 is already a translate of the ordinary site
mirror. These give both parities of every reflected-packet Hankel shift.
All entries in the resulting bounds refer to the original lattice kernel.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace IsingScaling.RawLatticeOscillation
open NormalDifference

/-- The physical right-half-lattice form at the axial bond plane 1/2. -/
def AxialBondForm (g : Site → ℝ) : Prop :=
  Packet.SiteReflectedPositive g (fun x => x 0-1) (fun x => ![1-x 0,x 1,x 2])

private def unitPacket {ι : Type} [Fintype ι] (c : ι → ℝ) (K : ℕ → ι → ι → ℝ) (n : ℕ) :=
  ∑ i, ∑ j, c i*c j*K n i j

private theorem extra_form {g : Site → ℝ}
    (forms : ∀ d, Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d))
    (bond : AxialBondForm g) (d : PacketNormal) :
    Packet.SiteReflectedPositive g (tip d) (fun x => NormalDifference.refl d x - step d 1) := by
  intro ι _ X hx c
  let E : Site := ![1,0,0]
  let Y (i : ι) : Site := X i+E
  cases d with
  | axis =>
    have hY (i) : 0 ≤ Y i 0 - 1 := by
      have hu := hx i
      change 0 ≤ X i 0 at hu
      change 0 ≤ X i 0 + 1 - 1
      omega
    have H := bond Y hY c
    have he (i j) : Y i - (![1 - (Y j) 0, (Y j) 1, (Y j) 2] : Site) =
        X i - (NormalDifference.refl .axis (X j) - step .axis 1) := by
      funext a; fin_cases a <;> simp [Y,E,NormalDifference.refl,step,Matrix.vecHead,Matrix.vecTail] <;> ring
    simpa only [he] using H
  | faceDiagonal =>
    have hY (i) : 0 ≤ tip .faceDiagonal (Y i) := by
      have hu := hx i
      change 0 ≤ X i 0-X i 1 at hu
      change 0 ≤ X i 0 + 1 - (X i 1 + 0)
      omega
    have H := forms .faceDiagonal Y hY c
    have he (i j) : Y i - NormalDifference.refl .faceDiagonal (Y j) =
        X i - (NormalDifference.refl .faceDiagonal (X j) - step .faceDiagonal 1) := by
      funext a; fin_cases a <;> simp [Y,E,NormalDifference.refl,step,Matrix.vecHead,Matrix.vecTail] <;> ring
    simpa only [he] using H

private theorem hankel_shift {g : Site → ℝ} (d : PacketNormal) (e : ℕ)
    (hpos : Packet.SiteReflectedPositive g (tip d)
      (fun x => NormalDifference.refl d x - step d e))
    {ι : Type} [Fintype ι] (Z : ι → Site) (hz : ∀ i, 0 ≤ tip d (Z i)) (c : ι → ℝ)
    {J : Type} [Fintype J] (v : J → ℕ) (γ : J → ℝ) (s : ℕ) :
    0 ≤ ∑ i, ∑ j, γ i * γ j *
      unitPacket c (fun m a b => kernel d g (Z a) (Z b) m) (2*s+e+v i+v j) := by
  classical
  let T (j : J × ι) : Site := step d (s+v j.1:ℕ) + Z j.2
  let b (j : J × ι) := γ j.1 * c j.2
  have hT (j : J × ι) : 0 ≤ tip d (T j) := by
    have H := hz j.2
    cases d <;> simp [T,tip,step,Matrix.vecHead,Matrix.vecTail] at * <;> omega
  have he (i j : J × ι) : g (T i - (NormalDifference.refl d (T j) - step d e)) =
      kernel d g (Z i.2) (Z j.2) (2*s+e+v i.1+v j.1) := by
    apply congrArg g
    funext a
    cases d <;> fin_cases a <;> simp [T,NormalDifference.refl,step,Matrix.vecHead,Matrix.vecTail] <;> ring
  have H := hpos T hT b
  simp only [Fintype.sum_prod_type,he,b] at H
  refine H.trans_eq ?_
  simp only [unitPacket,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Ordinary integer times, including odd Hankel shifts, for every signed
finite stencil of actual half-lattice marks. -/
theorem packet_complete {g : Site → ℝ} (hb : ∀ x, |g x| ≤ 1)
    (forms : ∀ d, Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d))
    (bond : AxialBondForm g) (d : PacketNormal) {ι : Type} [Fintype ι]
    (Z : ι → Site) (hz : ∀ i, 0 ≤ tip d (Z i)) (c : ι → ℝ) (j n : ℕ) :
    0 ≤ (Packet.diff^[j]) (fun m => ∑ a, ∑ b, c a*c b*kernel d g (Z a) (Z b) m) n := by
  classical
  apply Packet.completeMonotone_of_hankel
  · intro J hJ v γ q
    let e := q%2
    have hs : 2*(q/2)+e=q := by dsimp [e]; omega
    have H : Packet.SiteReflectedPositive g (tip d) (fun x => NormalDifference.refl d x-step d e) := by
      by_cases h : e = 0
      · have he : step d e = 0 := by rw [h]; cases d <;> funext a <;> fin_cases a <;> rfl
        simpa only [he,sub_zero] using forms d
      · have he : e=1 := by dsimp [e] at *; omega
        simpa only [he,Nat.cast_one] using extra_form forms bond d
    simpa only [hs,unitPacket] using hankel_shift d e H Z hz c v γ (q/2)
  · refine ⟨∑ a, ∑ b, |c a| * |c b|, ?_⟩
    intro m
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_right (by positivity) (hb _)

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


private theorem self_bound {g : Site → ℝ} (hb : ∀ x, |g x| ≤ 1)
    (d : PacketNormal) (z : Site) (hz : 0 ≤ tip d z) (k : ℕ) :
    kernel d g z z k ≤ SpatialEnvelope.tail g k := by
  let v : Site := step d k + z - NormalDifference.refl d z
  have hv : (k:ℤ) ≤ v 0 := by
    cases d <;> simp [v,step,NormalDifference.refl,tip,Matrix.vecHead,Matrix.vecTail] at * <;> omega
  exact SpatialEnvelope.le_tail (fun x => (le_abs_self _).trans (hb x))
    (x:=v) ⟨0,by omega⟩

/-- A normal step of one actual lattice layer at arbitrary transverse offsets. -/
theorem normal_one {g : Site → ℝ} (hb : ∀ x, |g x| ≤ 1) (hcub : Packet.CubicKernel g)
    (forms : ∀ d, Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d))
    (bond : AxialBondForm g) (d : PacketNormal) (w z : Site)
    (hw : 0 ≤ tip d w) (hz : 0 ≤ tip d z) (k n : ℕ) (hn : 2*k ≤ n) :
    ((k+1:ℕ):ℝ) * |kernel d g w z n-kernel d g w z (n+1)| ≤ SpatialEnvelope.tail g k := by
  let A (m : ℕ) := kernel d g w w m
  let B (m : ℕ) := kernel d g z z m
  let F (m : ℕ) := kernel d g w z m
  let Z : Fin 2 → Site := ![w,z]
  let Q (v : ℝ) (m : ℕ) := A m + v*v*B m + (2*v)*F m
  have cm (v : ℝ) (j t : ℕ) : 0 ≤ (Packet.diff^[j]) (Q v) t := by
    let c : Fin 2 → ℝ := ![1,v]
    have H := packet_complete hb forms bond d Z (fun a => by fin_cases a; exact hw; exact hz) c j t
    have he : (fun m => ∑ a, ∑ b, c a*c b*kernel d g (Z a) (Z b) m) = Q v := by
      funext m
      simp only [Q,Fin.sum_univ_two,Z,c,Matrix.cons_val_zero,Matrix.cons_val_one,A,B,F]
      rw [kernel_symm hcub d z w m]
      ring
    rwa [he] at H
  have hp := cm 1 1 n
  have hm := cm (-1) 1 n
  have hp' := Packet.decay_complete (cm 1) 1 k n hn
  have hm' := Packet.decay_complete (cm (-1)) 1 k n hn
  simp only [Function.iterate_one,Packet.diff,Q,pow_one] at hp hm hp' hm'
  let W : ℝ := ((k+1:ℕ):ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hh : 2*|F n-F (n+1)| ≤ A n-A (n+1)+(B n-B (n+1)) := by
    rcases le_total (F (n+1)) (F n) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith only [hm]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith only [hp]
  have ht := mul_le_mul_of_nonneg_left hh hW
  have hu := self_bound hb d w hw k
  have hv := self_bound hb d z hz k
  change A k ≤ _ at hu
  change B k ≤ _ at hv
  change W * _ ≤ _
  dsimp only [W] at ht ⊢
  change ((k+1:ℕ):ℝ)*|F n-F (n+1)| ≤ _
  nlinarith only [ht,hp',hm',hu,hv]



section CoordinateBounds
variable {g : Site → ℝ} (hbound : ∀ x, |g x| ≤ 1) (hcub : Packet.CubicKernel g)
  (forms : ∀ d : PacketNormal, Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d))
  (bond : AxialBondForm g)
include hbound hcub forms bond

private theorem axial_one (k : ℕ) (a b c : ℤ) (ha : 4*(k:ℤ) ≤ a) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c] - g ![a+1,b,c]| ≤ SpatialEnvelope.tail g k := by
  let w : Site := ![a-4*(k:ℤ),b,c]
  have H := normal_one hbound hcub forms bond .axis w 0
    (by simp [tip,w]; omega) (by simp [tip]) k (4*k) (by omega)
  have he (m : ℕ) : kernel .axis g w 0 m = g ![(m:ℤ)+(a-4*k),b,c] := by
    apply congrArg g; ext i; fin_cases i <;> simp [w,step,NormalDifference.refl]
  simpa only [he,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
    show 4*(k:ℤ)+(a-4*k)=a by ring,
    show 4*(k:ℤ)+1+(a-4*k)=a+1 by ring] using H

private theorem diagonal_one (k : ℕ) (a b c : ℤ) (hab : 8*(k:ℤ) ≤ a-b) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c] - g ![a+1,b-1,c]| ≤ SpatialEnvelope.tail g k := by
  let w : Site := ![a-4*(k:ℤ),b+4*k,c]
  have H := normal_one hbound hcub forms bond .faceDiagonal w 0
    (by simp [tip,w]; omega) (by simp [tip]) k (4*k) (by omega)
  have he (m : ℕ) : kernel .faceDiagonal g w 0 m =
      g ![(m:ℤ)+(a-4*k),-(m:ℤ)+(b+4*k),c] := by
    apply congrArg g; ext i; fin_cases i <;> simp [w,step,NormalDifference.refl]
  simpa only [he,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
    show 4*(k:ℤ)+(a-4*k)=a by ring,
    show 4*(k:ℤ)+1+(a-4*k)=a+1 by ring,
    show -(4*(k:ℤ))+(b+4*k)=b by ring,
    show -(4*(k:ℤ)+1)+(b+4*k)=b-1 by ring] using H
omit hbound forms bond

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

include hbound forms bond

/-- Turning one oblique and one longitudinal unit increment gives a
transverse unit increment, also when the transverse coordinate changes sign. -/
private theorem transverse_pos (k : ℕ) (a b c : ℤ) (ha : 8*(k:ℤ)+2 ≤ a) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c]-g ![a,b+1,c]| ≤ 2*SpatialEnvelope.tail g k := by
  have multri (u v w : ℝ) : ((k+1:ℕ):ℝ)*|u-v| ≤
      ((k+1:ℕ):ℝ)*|u-w| + ((k+1:ℕ):ℝ)*|v-w| := by
    rw [← mul_add, abs_sub_comm v w]
    exact mul_le_mul_of_nonneg_left (abs_sub_le u w v) (by positivity)
  by_cases hb : 8*(k:ℤ) ≤ a-(b+1)
  · have d := diagonal_one hbound hcub forms bond k a (b+1) c hb
    have l := axial_one hbound hcub forms bond k a b c (by omega)
    rw [show b+1-1=b by omega] at d
    linarith only [multri (g ![a,b,c]) (g ![a,b+1,c]) (g ![a+1,b,c]), d, l]
  · have d := diagonal_one hbound hcub forms bond k a (-b) c (by omega)
    rw [show -b-1 = -(b+1) by omega, signY hcub, signY hcub] at d
    have l := axial_one hbound hcub forms bond k a (b+1) c (by omega)
    linarith only [multri (g ![a,b,c]) (g ![a,b+1,c]) (g ![a+1,b+1,c]), d, l]

private theorem transverse_one (k : ℕ) (a b c : ℤ) (ha : 8*k+2 ≤ a.natAbs) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c]-g ![a,b+1,c]| ≤ 2*SpatialEnvelope.tail g k := by
  by_cases h : 8*(k:ℤ)+2 ≤ a
  · exact transverse_pos hbound hcub forms bond k a b c h
  · have t := transverse_pos hbound hcub forms bond k (-a) b c (by omega)
    rwa [signX hcub, signX hcub] at t

private theorem first_coordinate (k : ℕ) (a b c : ℤ)
    (hfar : 8*k+2 ≤ max a.natAbs (max b.natAbs c.natAbs)) :
    ((k+1:ℕ):ℝ) * |g ![a,b,c]-g ![a+1,b,c]| ≤ 2*SpatialEnvelope.tail g k := by
  by_cases ha : 8*k+2 ≤ a.natAbs
  · have hT := SpatialEnvelope.tail_nonneg (fun x => (le_abs_self _).trans (hbound x)) k
    by_cases hp : 4*(k:ℤ) ≤ a
    · linarith only [axial_one hbound hcub forms bond k a b c hp,hT]
    · have l := axial_one hbound hcub forms bond k (-(a+1)) b c (by omega)
      rw [show -(a+1)+1 = -a by omega, signX hcub, signX hcub, abs_sub_comm] at l
      linarith only [l,hT]
  · by_cases hb : 8*k+2 ≤ b.natAbs
    · rw [swap01 hcub a b c,swap01 hcub (a+1) b c]
      exact transverse_one hbound hcub forms bond k b a c hb
    · have ht := transverse_one hbound hcub forms bond k c a b (by omega)
      rw [swap01 hcub a b c, swap01 hcub (a+1) b c,swap02 hcub b a c,swap02 hcub b (a+1) c]
      exact ht

/-- Every actual coordinate step, in either orientation of the far coordinate. -/
theorem coordinate_one (k : ℕ) (x : Site) (i : Fin 3)
    (hfar : SpatialEnvelope.outside (8*k+2) x) :
    ((k+1:ℕ):ℝ) * |g x-g (x+Pi.single i (1:ℤ))| ≤ 2*SpatialEnvelope.tail g k := by
  let p := Equiv.swap (0:Fin 3) i
  let S := signedPerm p (fun _ => false)
  have Sx (v : Site) : S v = ![v (p 0),v (p 1),v (p 2)] := by ext j; fin_cases j <;> rfl
  have Sy : S (x + Pi.single i (1:ℤ)) =
      ![x (p 0)+1,x (p 1),x (p 2)] := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [Sx,p,Pi.single_apply] <;> decide
  obtain ⟨j,hj⟩ := hfar
  obtain ⟨j,rfl⟩ := p.surjective j
  have hm : 8*k+2 ≤ max (x (p 0)).natAbs (max (x (p 1)).natAbs (x (p 2)).natAbs) := by
    fin_cases j
    · exact hj.trans (le_max_left _ _)
    · exact hj.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact hj.trans ((le_max_right _ _).trans (le_max_right _ _))
  have H := first_coordinate hbound hcub forms bond k (x (p 0)) (x (p 1)) (x (p 2)) hm
  calc
    _ = ((k+1:ℕ):ℝ) * |g (S x)-g (S (x+Pi.single i (1:ℤ)))| := by
      rw [show g (S x) = g x from hcub p _ x,
        show g (S (x+Pi.single i (1:ℤ))) = g (x+Pi.single i (1:ℤ)) from hcub p _ _]
    _ ≤ _ := by simpa only [Sy, Sx x] using H

end CoordinateBounds



/-- The original unsmoothed kernel satisfies the integer-radius spatial
inequality (4.2) from the physical site and axial bond forms. -/
theorem localOscillation_of_site_bond {g : Site → ℝ} (hb : ∀ x, |g x| ≤ 1)
    (hcub : Packet.CubicKernel g)
    (forms : ∀ d, Packet.SiteReflectedPositive g (tip d) (NormalDifference.refl d))
    (bond : AxialBondForm g) : SpatialEnvelope.LocalOscillation g 96 16 40 := by
  intro r hr hrpos x hx k hk z hz
  let m := r/16
  let T := SpatialEnvelope.tail g m
  have hT : 0 ≤ T := SpatialEnvelope.tail_nonneg (fun x => (le_abs_self _).trans (hb x)) _
  have hm : (0:ℝ) < ((m+1:ℕ):ℝ) := by positivity
  have hR : (0:ℝ) < r := by exact_mod_cast hrpos
  let B := 2*T / ((m+1:ℕ):ℝ)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (by norm_num) hT) hm.le
  have hstep (u : Site) (hu : u ∈ cube k) (i : Fin 3) :
      |g (x+(u+Pi.single i (1:ℤ))) - g (x+u)| ≤ B := by
    have hfar : SpatialEnvelope.outside (8*m+2) (x+u) :=
      Packet.ParitySmoothing.near_outside hr hk hx hu (fun j => by omega)
    rw [← add_assoc, abs_sub_comm]
    apply (le_div_iff₀ hm).mpr
    rw [mul_comm]
    exact coordinate_one hb hcub forms bond m (x+u) i hfar
  have walk := Packet.ParitySmoothing.cube_walk (fun u => g (x+u)) k B hB hstep z hz
  simp only [add_zero] at walk
  have hrm : (r:ℝ) ≤ 16*((m+1:ℕ):ℝ) := by
    have h : r ≤ 16*(m+1) := by dsimp only [m]; omega
    exact_mod_cast h
  have hfinal : B ≤ 32*T/r := by
    rw [le_div_iff₀ hR]
    change (2*T/((m+1:ℕ):ℝ))*r ≤ _
    rw [div_mul_eq_mul_div,div_le_iff₀ hm]
    linarith only [mul_le_mul_of_nonneg_left hrm hT]
  calc
    _ ≤ 3*(k:ℝ)*(32*T/r) := walk.trans (mul_le_mul_of_nonneg_left hfinal (by positivity))
    _ = _ := by dsimp only [T,m]; ring

/-- The nonnegative parity obstruction to passing from even-layer
spectra to unaveraged points already violates the axial two-site bond test. -/
theorem checkerboard_fails_bond : ¬ AxialBondForm
    (fun x => if (x 0 + x 1 + x 2)%2=0 then 1 else 0) := by
  intro H
  let X : Fin 2 → Site := ![![1,0,0], ![2,0,0]]
  have h := H X (fun i => by fin_cases i <;> norm_num [X]) ![(1:ℝ),-1]
  simp only [Fin.sum_univ_two] at h
  change (0:ℝ) ≤ (1*1*0+1*(-1)*1)+((-1)*1*1+(-1)*(-1)*0) at h
  norm_num at h

#print axioms packet_complete
#print axioms coordinate_one
#print axioms localOscillation_of_site_bond
#print axioms checkerboard_fails_bond

end IsingScaling.RawLatticeOscillation
