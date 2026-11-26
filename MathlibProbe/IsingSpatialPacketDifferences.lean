import MathlibProbe.IsingAnnularMass

/-! Source estimates for the actual free thermodynamic two-point law.
The normal increment is two lattice layers, so different lattice parity
classes are kept explicit. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators
namespace IsingScaling
namespace Packet

private lemma decreasing_iter {a : ℕ → ℝ}
    (h : ∀ j n, 0 ≤ (diff^[j]) a n) (j : ℕ) : Antitone ((diff^[j]) a) := by
  apply antitone_nat_of_succ_le
  intro n
  have H := h (j+1) n
  rwa [Function.iterate_succ_apply', diff, sub_nonneg] at H

private lemma sum_diff (a : ℕ → ℝ) (n k : ℕ) :
    ∑ t ∈ Finset.range k, diff a (n+t) = a n - a (n+k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; dsimp only [diff]; rw [← Nat.add_assoc]; ring

/-- All-order scalar smoothing, proved just from finite differences. -/
theorem decay_complete {a : ℕ → ℝ} (h : ∀ j n, 0 ≤ (diff^[j]) a n)
    (j k n : ℕ) (hn : (j+1)*k ≤ n) :
    ((k+1:ℕ):ℝ)^j * (diff^[j]) a n ≤ a k := by
  have hrec (i m : ℕ) :
      ((k+1:ℕ):ℝ) * (diff^[i+1]) a (m+k) ≤ (diff^[i]) a m := by
    let b := (diff^[i]) a
    have H : ∀ t ∈ Finset.range (k+1), (diff^[i+1]) a (m+k) ≤ diff b (m+t) :=
      fun t ht => by
        have H := decreasing_iter h (i+1) (Nat.add_le_add_left (show t≤k by simpa using ht) m)
        simpa only [Function.iterate_succ_apply'] using H
    have H' := Finset.sum_le_sum H
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sum_diff] at H'
    exact H'.trans (sub_le_self _ (h i _))
  have hmid (b : ℕ) : ((k+1:ℕ):ℝ)^b * (diff^[b]) a ((b+1)*k) ≤ a k := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [pow_succ, Nat.succ_mul (b+1), mul_assoc]
      exact (mul_le_mul_of_nonneg_left (hrec b ((b+1)*k)) (by positivity)).trans ih
  exact (mul_le_mul_of_nonneg_left (decreasing_iter h j hn) (by positivity)).trans (hmid j)

private lemma linear_three (j : ℕ) (a b c : ℝ) (f g h : ℕ → ℝ) :
    (diff^[j]) (fun n => a*f n + b*g n + c*h n) =
      fun n => a*(diff^[j]) f n+b*(diff^[j]) g n+c*(diff^[j]) h n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext n
    simp only [Function.iterate_succ_apply',ih,diff]
    ring

end Packet

namespace NormalDifference

def tip : PacketNormal → Site → ℤ
  | .axis,z => z 0
  | .faceDiagonal,z => z 0-z 1

def refl : PacketNormal → Site → Site
  | .axis,z => ![-z 0,z 1,z 2]
  | .faceDiagonal,z => ![z 1,z 0,z 2]

def step : PacketNormal → ℤ → Site
  | .axis,n => ![n,0,0]
  | .faceDiagonal,n => ![n,-n,0]

def mirror (d : PacketNormal) (L : ℕ) : BoxSiteMirror L :=
  match d with
  | .axis => axisSiteMirror L
  | .faceDiagonal => diagonalSiteMirror L

private theorem mirror_tip (d : PacketNormal) (L) (x : BoxSite L) : (mirror d L).tip x = tip d x := by
  cases d <;> rfl

private theorem mirror_refl (d : PacketNormal) (L) (x : BoxSite L) :
    ((mirror d L).refl x).val = refl d x := by
  ext i
  cases d <;> fin_cases i <;> rfl

def kernel (d : PacketNormal) (g : Site → ℝ) (w z : Site) (m : ℕ) : ℝ :=
  g (step d (m:ℤ)+w-refl d z)

private lemma shifted_tip (d : PacketNormal) {z : Site} (hz : 0≤tip d z) (n : ℕ) :
    0≤tip d (step d n+z) := by
  cases d <;> simp [tip,step] at * <;> omega

private lemma shifted_displacement (d : PacketNormal) (w z : Site) (p q : ℕ) :
    (step d p + w) - refl d (step d q + z) = step d ((p+q:ℕ):ℤ)+w-refl d z := by
  ext i
  cases d <;> fin_cases i <;> simp [step,refl] <;> ring

private lemma kernel_symm {β g} (hg : IsFreeTwoPoint β g) (d : PacketNormal) (w z : Site) (m : ℕ) :
    kernel d g w z m = kernel d g z w m := by
  cases d with
  | axis =>
    let S := signedPerm (Equiv.refl _) (fun i => decide (i≠0))
    have hs : S (step .axis m + w - refl .axis z) = step .axis m + z - refl .axis w := by
      have hh (v : Site) : S v = ![v 0,-v 1,-v 2] := by ext i; fin_cases i <;> rfl
      rw [hh]; ext i; fin_cases i <;> (simp [step,refl,Matrix.vecHead,Matrix.vecTail]; try ring)
    exact (freeLimit_signedPerm hg _ _ _).symm.trans (congrArg g hs)
  | faceDiagonal =>
    let S := signedPerm (Equiv.swap 0 1) (fun _ => true)
    have hs : S (step .faceDiagonal m + w - refl .faceDiagonal z) =
        step .faceDiagonal m + z - refl .faceDiagonal w := by
      have hh (v : Site) : S v = ![-v 1,-v 0,-v 2] := by ext i; fin_cases i <;> rfl
      rw [hh]; ext i; fin_cases i <;> (simp [step,refl,Matrix.vecHead,Matrix.vecTail]; try ring)
    exact (freeLimit_signedPerm hg _ _ _).symm.trans (congrArg g hs)

private theorem packet_positive {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (d : PacketNormal) {ι : Type} [Fintype ι] (Z : ι → Site) (hZ : ∀ i, 0≤tip d (Z i))
    (c : ι → ℝ) (j n : ℕ) :
    0 ≤ (Packet.diff^[j]) (evenPacket c (fun m i k => kernel d g (Z i) (Z k) m)) n := by
  apply (hg.stationary_pair_limit hβ).completeMonotone_evenPacket (tip d) (refl d) (mirror d)
    (mirror_tip d) (mirror_refl d) (fun n i => step d n + Z i) (fun n i => shifted_tip d (hZ i) n)
  intro p q i k
  rw [shifted_displacement]; rfl

/-- Polarization of the actual complete-monotone packets, including noncoplanar
end labels. These offsets contain both parity choices of the normal layer. -/
theorem polarized_decay {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (d : PacketNormal) (w z : Site) (hw : 0≤tip d w) (hz : 0≤tip d z)
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
    have hpos := packet_positive hg hβ d Z (fun a => by fin_cases a; exact hw; exact hz) C i m
    have hid : evenPacket C (fun m a b => kernel d g (Z a) (Z b) m) =
        fun l => (1:ℝ)*A l + (v*v)*B l + (2*v)*F l := by
      funext l
      simp only [evenPacket,Fin.sum_univ_two,Z,C,Matrix.cons_val_zero,Matrix.cons_val_one,A,B,F]
      rw [kernel_symm hg d z w (2*l)]; ring
    rwa [hid] at hpos
  have ha : ∀ i m, 0≤(Packet.diff^[i]) A m := by
    intro i m
    have hh := hp 0 i m
    simpa only [zero_mul,mul_zero,zero_add,add_zero,one_mul] using hh
  have hb : ∀ i m, 0≤(Packet.diff^[i]) B m := by
    intro i m
    have hh := packet_positive hg hβ d (fun _ : Unit => z) (fun _ => hz) (fun _ => 1) i m
    have he : evenPacket (fun _: Unit => (1:ℝ)) (fun m _ _ => kernel d g z z m) = B := by
      funext l; simp [evenPacket,B]
    rwa [he] at hh
  have hu := hp 1 j n
  have hl := hp (-1) j n
  rw [Packet.linear_three] at hu hl
  have hbound : 2*|(Packet.diff^[j]) F n| ≤ (Packet.diff^[j]) A n + (Packet.diff^[j]) B n := by
    rcases le_total 0 ((Packet.diff^[j]) F n) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  have ht := mul_le_mul_of_nonneg_left hbound (show 0≤((k+1:ℕ):ℝ)^j by positivity)
  have ha' := Packet.decay_complete ha j k n hn
  have hb' := Packet.decay_complete hb j k n hn
  change 2*((k+1:ℕ):ℝ)^j * |(Packet.diff^[j]) F n| ≤ A k+B k
  nlinarith only [ht,ha',hb']

private lemma self_susceptibility {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (d : PacketNormal) (z : Site) (hz : 0≤tip d z) (k R : ℕ) (hk : 0<k) (hR : 0<R) :
    ((min (2*k) R:ℕ):ℝ)^3 * kernel d g z z (2*k) ≤ 1728*susceptibility g R := by
  let v : Site := step d (2*k:ℕ) + z - refl d z
  have hv : ((2*k:ℕ):ℤ) ≤ v 0 := by cases d <;> simp [v,step,refl,tip,Matrix.vecHead,Matrix.vecTail] at * <;> omega
  let K := (v 0).toNat
  have hK : 2*k ≤ K := by dsimp [K]; omega
  have heq : signedPerm (Equiv.refl _) (fun _ => false) ![(K:ℤ), v 1, v 2] = v := by
    ext i
    fin_cases i
    · change (K:ℤ)=v 0; dsimp [K]; omega
    · rfl
    · rfl
  have H := hg.site_susceptibility_density hβ K R (by omega) hR (v 1) (v 2)
    (Equiv.refl _) (fun _ => false)
  rw [heq] at H
  have hmin : ((min (2*k) R:ℕ):ℝ) ≤ ((min K R:ℕ):ℝ) := by exact_mod_cast min_le_min_right R hK
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hmin 3)
    ((hg.positive_cube_mass hβ).1 v)).trans H

/-- Actual susceptibility-normalized spatial difference estimate, at every
order, in each coordinate or face-diagonal positive-time packet chart. -/
theorem susceptibility_difference {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (d : PacketNormal) (w z : Site) (hw : 0≤tip d w) (hz : 0≤tip d z)
    (j k n R : ℕ) (hk : 0<k) (hR : 0<R) (hn : (j+1)*k≤n) :
    ((min (2*k) R : ℕ):ℝ)^3 * ((k+1:ℕ):ℝ)^j *
      |(Packet.diff^[j]) (fun m => kernel d g w z (2*m)) n| ≤ 1728*susceptibility g R := by
  have H := polarized_decay hg hβ d w z hw hz j k n hn
  have H' := mul_le_mul_of_nonneg_left H (show 0≤((min (2*k) R:ℕ):ℝ)^3 by positivity)
  have h1 := self_susceptibility hg hβ d w hw k R hk hR
  have h2 := self_susceptibility hg hβ d z hz k R hk hR
  nlinarith only [H',h1,h2]

end NormalDifference
end IsingScaling
