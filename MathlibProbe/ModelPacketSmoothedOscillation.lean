import MathlibProbe.RotorPacketParitySmoothing
import MathlibProbe.IsingSpatialFiniteStencil

/-! # Spatial oscillation of the averaged physical lattice pair

At distance at least r, a coordinate two-step difference in the original
kernel is bounded by twice the tail at 2m divided by m+1, with m=floor(r/16).
The four-site collar required by the binomial stencil remains in that
region throughout a path of coordinate size at most r/40. The signed
coordinate walk uses at most three times its largest coordinate many
unit steps. The positive central stencil term compares the original tail
with 64 times the smoothed tail at the smaller radius m. This proves the
oscillation hypothesis with a numerical constant from physical site forms.
-/

noncomputable section
open Finset
namespace IsingScaling.Packet.ParitySmoothing

private theorem interval_walk (F : ℤ → ℝ) (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ t : ℤ, -(k:ℤ) ≤ t → t < k → |F (t+1)-F t| ≤ b)
    (t : ℤ) (ht : -(k:ℤ) ≤ t ∧ t ≤ k) : |F t-F 0| ≤ (k:ℝ)*b := by
  cases t with
  | ofNat n =>
    change -(k:ℤ) ≤ (n:ℤ) ∧ (n:ℤ) ≤ k at ht
    have H := dist_le_range_sum_of_dist_le (f := fun j : ℕ => F j) n (d := fun _ => b)
      (fun {j} hj => by
        rw [Real.dist_eq, abs_sub_comm]
        exact h j (by omega) (by omega))
    rw [Real.dist_eq, abs_sub_comm] at H
    have hnk : n ≤ k := by omega
    exact (by simpa only [Nat.cast_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using H :
      |F (n:ℤ)-F 0| ≤ (n:ℝ)*b).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hnk) hb)
  | negSucc n =>
    have H := dist_le_range_sum_of_dist_le (f := fun j : ℕ => F (-(j:ℤ))) (n+1) (d := fun _ => b)
      (fun {j} hj => by
        rw [Real.dist_eq]
        have hh := h (-(j:ℤ)-1) (by omega) (by omega)
        rw [show -(j:ℤ)-1+1 = -(j:ℤ) by omega,
          show -(j:ℤ)-1 = -((j+1:ℕ):ℤ) by omega] at hh
        exact hh)
    rw [Real.dist_eq, abs_sub_comm] at H
    have hnk : n+1 ≤ k := by omega
    have he : -((n+1:ℕ):ℤ) = Int.negSucc n := by omega
    exact (by simpa only [he,Nat.cast_zero,neg_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      using H : |F (Int.negSucc n)-F 0| ≤ ((n+1:ℕ):ℝ)*b).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hnk) hb)

theorem cube_walk (F : Site → ℝ) (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ y ∈ cube k, ∀ i : Fin 3, |F (y + Pi.single i (1:ℤ))-F y| ≤ b)
    (z : Site) (hz : z ∈ cube k) : |F z-F 0| ≤ 3*(k:ℝ)*b := by
  have hzc (i : Fin 3) : -(k:ℤ) ≤ z i ∧ z i ≤ k := by
    have hh : ∀ j, -(k:ℤ) ≤ z j ∧ z j ≤ k := by
      simpa only [cube,Fintype.mem_piFinset,Finset.mem_Icc] using hz
    exact hh i
  have walk (u : ℤ → Site) (i : Fin 3)
      (hu : ∀ t : ℤ, -(k:ℤ) ≤ t → t < k → u t ∈ cube k)
      (hs : ∀ t : ℤ, u t + Pi.single i (1:ℤ) = u (t+1))
      (t : ℤ) (ht : -(k:ℤ) ≤ t ∧ t ≤ k) : |F (u t)-F (u 0)| ≤ (k:ℝ)*b := by
    apply interval_walk (fun v => F (u v)) k b hb _ t ht
    intro v hv hv'
    rw [← hs v]
    exact h _ (hu v hv hv') i
  have memc (i j l : ℤ) (hi : -(k:ℤ) ≤ i ∧ i ≤ k) (hj : -(k:ℤ) ≤ j ∧ j ≤ k)
      (hl : -(k:ℤ) ≤ l ∧ l ≤ k) : (![i,j,l] : Site) ∈ cube k := by
    simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc]
    intro a; fin_cases a <;> first | exact hi | exact hj | exact hl
  have h0 : -(k:ℤ) ≤ 0 ∧ (0:ℤ) ≤ k := by omega
  have A := walk (fun t => ![t,0,0]) 0 (fun t ht hs => memc _ _ _ ⟨ht,hs.le⟩ h0 h0)
    (by intro t; funext i; fin_cases i <;> simp [Pi.single_apply]) (z 0) (hzc 0)
  have B := walk (fun t => ![z 0,t,0]) 1 (fun t ht hs => memc _ _ _ (hzc 0) ⟨ht,hs.le⟩ h0)
    (by intro t; funext i; fin_cases i <;> simp [Pi.single_apply]) (z 1) (hzc 1)
  have C := walk (fun t => ![z 0,z 1,t]) 2
    (fun t ht hs => memc _ _ _ (hzc 0) (hzc 1) ⟨ht,hs.le⟩)
    (by intro t; funext i; fin_cases i <;> simp [Pi.single_apply]) (z 2) (hzc 2)
  have hZ : (![z 0,z 1,z 2] : Site) = z := by funext i; fin_cases i <;> rfl
  have ho : (![0,0,0] : Site) = 0 := by funext i; fin_cases i <;> rfl
  rw [hZ] at C
  rw [ho] at A
  have H₁ := abs_sub_le (F z) (F ![z 0,z 1,0]) (F ![z 0,0,0])
  have H₂ := abs_sub_le (F z) (F ![z 0,0,0]) (F 0)
  linarith only [H₁,H₂,A,B,C]

theorem near_outside {r k : ℕ} (hr : 40 ≤ r) (hk : 40*k ≤ r)
    {x u : Site} (hx : SpatialEnvelope.outside r x) (hu : u ∈ cube k) {y : Site}
    (hy : ∀ j, (x+u) j-4 ≤ y j ∧ y j ≤ (x+u) j+4) :
    SpatialEnvelope.outside (8*(r/16)+2) y := by
  obtain ⟨i,hi⟩ := hx
  refine ⟨i,?_⟩
  have hbox : ∀ j, -(k:ℤ) ≤ u j ∧ u j ≤ k := by
    simpa only [cube,Fintype.mem_piFinset,Finset.mem_Icc] using hu
  have h₁ := hbox i
  have h₂ := hy i
  change x i+u i-4 ≤ y i ∧ y i ≤ x i+u i+4 at h₂
  omega

/-- Site mirrors of the original kernel give the oscillation of the
actual smoothed mark with no bound on ordinary one-step differences of g. -/
theorem localOscillation_of_site_forms {g : Site → ℝ} (hb : ∀ z, |g z| ≤ 1)
    (hn : ∀ z, 0 ≤ g z) (hc : Packet.CubicKernel g)
    (forms : ∀ d : PacketNormal, Packet.SiteReflectedPositive g
      (NormalDifference.tip d) (NormalDifference.refl d)) :
    SpatialEnvelope.LocalOscillation (smooth g) 3072 16 40 := by
  intro r hr hrpos x hx k hk z hz
  let m := r/16
  have hb' : ∀ z, g z ≤ 1 := fun z => (le_abs_self _).trans (hb z)
  let T := SpatialEnvelope.tail g (2*m)
  let T' := SpatialEnvelope.tail (smooth g) m
  have hT : 0 ≤ T := SpatialEnvelope.tail_nonneg hb' _
  have hT' : 0 ≤ T' := SpatialEnvelope.tail_nonneg (smooth_le_one hb') _
  have hcT : T ≤ 64 * T' := by
    apply SpatialEnvelope.tail_le (by positivity)
    intro a ha
    have ha' : SpatialEnvelope.outside m a := by
      rcases ha with ⟨j,hj⟩; exact ⟨j, by omega⟩
    exact (original_le_smooth hn a).trans (mul_le_mul_of_nonneg_left
      (SpatialEnvelope.le_tail (smooth_le_one hb') ha') (by norm_num))
  have hmpos : (0:ℝ) < ((m+1:ℕ):ℝ) := by positivity
  have hR : (0:ℝ) < r := by exact_mod_cast hrpos
  let B := T / ((m+1:ℕ):ℝ)
  have hB : 0 ≤ B := div_nonneg hT hmpos.le
  have hstep (u : Site) (hu : u ∈ cube k) (i : Fin 3) :
      |smooth g (x+(u+Pi.single i (1:ℤ))) - smooth g (x+u)| ≤ B := by
    rw [← add_assoc]
    have hs := smooth_step_le (g := g) (x+u) i (2*B) (by
      intro y hy
      have hy' := near_outside hr hk hx hu hy
      have hh := GeneralizedNormalDifference.coordinate_two_of_site_forms hb hc forms m y i hy'
      rw [abs_sub_comm] at hh
      rw [show 2*B = 2*T/((m+1:ℕ):ℝ) by dsimp only [B]; ring, le_div_iff₀ hmpos]
      simpa only [T,mul_comm ((m+1:ℕ):ℝ)] using hh)
    linarith only [hs]
  have walk := cube_walk (fun u => smooth g (x+u)) k B hB hstep z hz
  simp only [add_zero] at walk
  apply walk.trans
  have hrm : (r:ℝ) ≤ 16*((m+1:ℕ):ℝ) := by
    have h₁ : r ≤ 16*(m+1) := by dsimp only [m]; omega
    exact_mod_cast h₁
  have hfinal : B ≤ 1024*T'/r := by
    rw [le_div_iff₀ hR]
    change (T/((m+1:ℕ):ℝ))*r ≤ _
    rw [div_mul_eq_mul_div,div_le_iff₀ hmpos]
    calc
      T * r ≤ (64*T') * (16*((m+1:ℕ):ℝ)) := mul_le_mul hcT hrm hR.le (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 3*(k:ℝ)*(1024*T'/r) := mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = 3072 * (k:ℝ) / r * SpatialEnvelope.tail (smooth g) (r/16) := by
      dsimp only [T',m]
      ring

#print axioms localOscillation_of_site_forms
end IsingScaling.Packet.ParitySmoothing
