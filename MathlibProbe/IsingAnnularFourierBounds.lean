import MathlibProbe.IsingMacroscopicDifferences
import MathlibProbe.IsingTangentAnnularPartition
import MathlibProbe.PuncturedFourierShells
import MathlibProbe.SpatialCutoffDifferences
import MathlibProbe.IsingShellCones

/-! Third-dimensional low-frequency volume and fourth-difference high-frequency
estimates for a finite cover of the expanding annuli. -/
noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology FourierTransform NNReal ContDiff
namespace IsingScaling.ShellCone
open IsingRotation IsingRotation.FourierShell

private theorem iter_real_complex (v : Space) (f : Space→ℝ) (k : ℕ) (x : Space) :
    ((translateDifference v)^[k] (fun y=>(f y:ℂ))) x = ((Cutoff.diff v)^[k] f x:ℝ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',translateDifference,Cutoff.diff,ih,ih]
    simp only [Complex.ofReal_sub]

private theorem iter_along (v : Space) (f : Space→ℝ) (k : ℕ) (x : Space) (n : ℕ) :
    (Packet.diff^[k]) (fun a : ℕ => f (x+(a:ℝ) • v)) n =
      ((Cutoff.diff v)^[k] f) (x+(n:ℝ) • v) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',Packet.diff,Cutoff.diff,ih,ih]
    rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul,add_assoc]

private theorem physical_cutoff_input {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : Packet.NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : Packet.OffOriginLimit g R f) (hBnd : BoundedAwayFromOrigin f)
    (q : Chart) (i : Fin 3) :
    ∃ B : ℝ, 0≤B ∧ ∀ k ≤ 4, ∀ {L t : ℝ}, 1≤L → 0≤t → ∀ x, L/8 ≤ inner ℝ (normal q i) x →
      ‖((Cutoff.diff (t • normal q i))^[k] f) x‖ ≤ B*(t/L)^k := by
  obtain ⟨b,hb⟩ := hBnd (1/32) (by norm_num)
  have hs (d : Bool) (u : ℝ) (hu : (1/8:ℝ)/4 ≤ u) :
      f (Packet.packetVector d (u/2) 0 0) ≤ max b 0 := by
    have hu' : (1/32:ℝ) ≤ u := by linarith
    have hfirst : (Packet.packetVector d (u/2) 0 0) 0 = u := by
      cases d <;> change _ = u <;> simp [Packet.packetVector,xyz] <;> ring
    have hcoord := PiLp.norm_apply_le (p:=2) (Packet.packetVector d (u/2) 0 0) (0:Fin 3)
    rw [hfirst,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ u)] at hcoord
    exact (le_abs_self _).trans ((hb _ (hu'.trans hcoord)).trans (le_max_left _ _))
  let B (k : ℕ) := max b 0*(4*(k:ℝ)/(1/8))^k
  have hB (k) : 0 ≤ B k := mul_nonneg (le_max_right _ _) (pow_nonneg (by positivity) _)
  refine ⟨∑ k ∈ Finset.range 5, B k,Finset.sum_nonneg (fun k _=>hB k),?_⟩
  intro k hk L t hL ht x hproj
  have H := hsp.three_cone_differences_of_source src hR hf q.1 q.2 i x (δ:=1/8) hL
    (by norm_num) ht (normal q i) rfl (by linarith) k (le_max_right _ _) hs
  have hin (m : ℕ) : ((m:ℝ)*t) • normal q i = (m:ℝ) • (t • normal q i) := mul_smul .. 
  simp_rw [hin] at H
  rw [iter_along] at H
  simp only [Nat.cast_zero,zero_smul,add_zero] at H
  exact (show ‖_‖≤B k*(t/L)^k from H).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun a _ => hB a) (show k ∈ Finset.range 5 by simp; omega)) (by positivity))

private theorem sum_volume {ι : Type} [Fintype ι] {u : ι→ℕ→V→ℂ} {A : ι→ℝ}
    (H : ∀ i, VolumeShellBounds (u i) (A i)) :
    VolumeShellBounds (fun j x => ∑ i, u i j x) (∑ i, A i) := by
  have hd (j : ℕ) (p : V) : 𝓕 (fun x => ∑ i, u i j x) p = ∑ i, 𝓕 (u i j) p := by
    simp only [Real.fourier_eq,Finset.smul_sum]
    rw [integral_finsetSum _ (fun i _ => (Real.fourierIntegral_convergent_iff p).2 ((H i).integrable j))]
  refine ⟨Finset.sum_nonneg (fun i _ => (H i).nonneg),
    fun j => integrable_finsetSum _ (fun i _ => (H i).integrable j),?_,?_⟩
  · intro j p
    rw [hd,Finset.sum_mul]
    exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => (H i).low j p)
  · intro j p hp
    rw [hd,Finset.sum_div,Finset.sum_mul]
    exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => (H i).high j hp)

private theorem piece_vol_bounds (q : Chart) (u : ℕ→V→ℂ) {C : ℝ} (hC : 0≤C)
    (hi : ∀ j, Integrable (u j))
    (hm : ∀ j x, ‖u j x‖ ≤ C) (hs : ∀ j x, 6*(2:ℝ)^j ≤ ‖x‖ → u j x=0)
    (hD : ∀ j i {t : ℝ}, 0≤t → t≤(2:ℝ)^j/256 → ∀ x,
      let D := (translateDifference (t • normal q i))^[4] (u j)
      ‖D x‖ ≤ C*(t/(2:ℝ)^j)^4 ∧ (6*(2:ℝ)^j ≤ ‖x‖ → D x=0))
    (halfP : ∀ p : V, p≠0 → ∃ i t, 0<t ∧ t≤3/‖p‖ ∧ ∀ (v : V→ℂ),
      Integrable v → ‖𝓕 v p‖ ≤ (1/16:ℝ)*(∫ x, ‖((translateDifference (t • normal q i))^[4] v) x‖)) :
    ∃ A, VolumeShellBounds u A := by
  let V₁ := volume.real (Metric.ball (0:V) 1)
  let B := V₁*6^3*C
  have hb : 0≤B := by dsimp [B,V₁]; positivity
  have low (j : ℕ) (p : V) : ‖𝓕 (u j) p‖ ≤ B*((2:ℝ)^j)^3 := by
    apply (norm_fourier_le_integral ..).trans
    apply (norm_integral_from_ball (r:=6*2^j) (by positivity) (hi j) (hs j) (hm j)).trans
    dsimp only [B,V₁]; ring_nf; rfl
  let K : ℝ := 768
  refine ⟨B*K^4,⟨by dsimp [K]; positivity,hi,?_,?_⟩⟩
  · intro j p
    have heq : ((2:ℝ)^j)^3 = 8^j := by rw [←pow_mul,Nat.mul_comm,pow_mul]; norm_num
    rw [← heq]
    exact (low j p).trans (by gcongr; exact le_mul_of_one_le_right hb (by norm_num [K]))
  · intro j p hp
    let L := (2:ℝ)^j
    have hL : 0<L := by dsimp [L]; positivity
    have hp' := norm_pos_iff.mpr hp
    obtain ⟨i,t,ht,hpT,hH⟩ := halfP p hp
    have htP := (le_div_iff₀ hp').mp hpT
    have heq : (1/2:ℝ)^j = 1/L := by simp [L]
    rw [heq,mul_one_div,le_div_iff₀ hL]
    by_cases hsmall : t≤L/256
    · let D := (translateDifference (t • normal q i))^[4] (u j)
      have hvol := norm_integral_from_ball (r:=6*L) (D:=C*(t/L)^4) (by positivity)
        (translateDifference_integrable (t • normal q i) (hi j) 4)
        (fun x => (hD j i ht.le hsmall x).2) (fun x => (hD j i ht.le hsmall x).1)
      have hpow := pow_le_pow_left₀ (mul_nonneg ht.le hp'.le) htP 4
      have hh := (hH (u j) (hi j)).trans (mul_le_mul_of_nonneg_left hvol (by norm_num))
      have halg : (1/16:ℝ)*(V₁*(6*L)^3*(C*(t/L)^4)) = B*t^4/(16*L) := by
        dsimp only [V₁,B]; field_simp
      change _ ≤ (1/16:ℝ)*(V₁*(6*L)^3*(C*(t/L)^4)) at hh
      rw [halg] at hh
      have h1 := (le_div_iff₀ (by positivity : 0<16*L)).mp hh
      have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hp'.le 4)
      have h3 := mul_le_mul_of_nonneg_left hpow hb
      rw [mul_pow] at h3
      rw [le_div_iff₀ (pow_pos hp' _)]
      dsimp only [K]; nlinarith only [h2,h3,hb]
    · have hLp : L*‖p‖ ≤ K := by
        have hh := mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) hp'.le
        dsimp [K]; linarith
      have hpow := pow_le_pow_left₀ (mul_nonneg hL.le hp'.le) hLp 4
      rw [mul_pow] at hpow
      have hBpow := mul_le_mul_of_nonneg_left hpow hb
      have hlow := mul_le_mul_of_nonneg_right (low j p) (mul_nonneg hL.le (pow_nonneg hp'.le 4))
      rw [le_div_iff₀ (pow_pos hp' _)]
      change ‖𝓕 (u j) p‖*(L*‖p‖^4) ≤ B*L^3*(L*‖p‖^4) at hlow
      nlinarith only [hBpow,hlow]

private theorem one_physical_piece {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : Packet.NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : Packet.OffOriginLimit g R f) (hBnd : BoundedAwayFromOrigin f)
    (q : Chart) (γ : Space→ℝ) (hs : ContDiff ℝ ∞ γ) (hk : HasCompactSupport γ)
    (hcone : tsupport γ ⊆ patch 1 4 q) :
    ∃ A, VolumeShellBounds (fun j x => ((γ (((2:ℝ)^j)⁻¹ • x)*f x:ℝ):ℂ)) A := by
  let u (j : ℕ) (x : V) : ℂ := ((γ (((2:ℝ)^j)⁻¹ • x)*f x:ℝ):ℂ)
  have hcut (i : Fin 3) := physical_cutoff_input src hR hf hsp hBnd q i
  have hD (i : Fin 3) : ∃ C : ℝ, 0≤C ∧ ∀ {L t : ℝ}, 1≤L → 0≤t → t≤L/256 → ∀ x,
      let D := (Cutoff.diff (t • normal q i))^[4] (fun z => γ (L⁻¹ • z)*f z)
      ‖D x‖ ≤ C*(t/L)^4 ∧ (6*L≤‖x‖ → D x=0) := by
    obtain ⟨B,hB,HB⟩ := hcut i
    apply Cutoff.localized_fourth _ (norm_normal_le q i) _ _ hs hk _ hB HB
    intro y hy
    exact ⟨((hcone hy).2 i).le,by linarith [(hcone hy).1]⟩
  choose C hC hCbound using hD
  obtain ⟨D,hD₀,hγ⟩ := Cutoff.smooth_difference_bound 0 γ hs hk
  obtain ⟨F,hF⟩ := hBnd (1/8) (by norm_num)
  let M := max (D*F) 0 + ∑ i, C i
  have hM : 0≤M := add_nonneg (le_max_right ..) (Finset.sum_nonneg (fun i _=>hC i))
  have hMC (i : Fin 3) : C i≤M := by
    apply (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)).trans
    exact le_add_of_nonneg_left (le_max_right ..)
  have hMF : D*F≤M := (le_max_left ..).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>hC i)))
  have hgeometry (j : ℕ) (x : Space) (hx : ((2:ℝ)^j)⁻¹ • x ∈ tsupport γ) :
      1/8≤‖x‖ ∧ ‖x‖<6*2^j := by
    let L := (2:ℝ)^j
    have hL : 0<L := by dsimp [L]; positivity
    have hL1 : 1≤L := one_le_pow₀ (by norm_num)
    have hcut := hcone hx
    obtain ⟨hu,hl⟩ := hcut
    have hh := (hl 0).trans_le (real_inner_le_norm _ _)
    have he := mul_le_mul_of_nonneg_right (norm_normal_le q 0) (norm_nonneg (L⁻¹ • x))
    change ‖L⁻¹ • x‖ < 4+1 at hu
    change 1/4 < ‖normal q 0‖*‖L⁻¹ • x‖ at hh
    have hnorm : ‖L⁻¹ • x‖=‖x‖/L := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hL.le),inv_mul_eq_div]
    rw [hnorm] at hh hu he
    have hlow : 1/8<‖x‖/L := by linarith
    have hlow' := (lt_div_iff₀ hL).mp hlow
    have hu' := (div_lt_iff₀ hL).mp hu
    change _ ∧ ‖x‖ < 6*L
    constructor <;> linarith
  have hm (j x) : ‖u j x‖ ≤ M := by
    by_cases hx : ((2:ℝ)^j)⁻¹ • x ∈ tsupport γ
    · have hα : ‖γ (((2:ℝ)^j)⁻¹ • x)‖ ≤ D := by simpa using hγ 0 (((2:ℝ)^j)⁻¹ • x)
      have hξ := hF x (hgeometry j x hx).1
      have hv := mul_le_mul hα hξ (norm_nonneg _) hD₀
      simpa only [u,Complex.norm_real,norm_mul] using hv.trans hMF
    · simp [u,image_eq_zero_of_notMem_tsupport hx,hM]
  have hsupp (j x) (hx : 6*(2:ℝ)^j≤‖x‖) : u j x=0 := by
    have hz : ((2:ℝ)^j)⁻¹ • x ∉ tsupport γ := fun h => (not_lt_of_ge hx) (hgeometry j x h).2
    simp [u,image_eq_zero_of_notMem_tsupport hz]
  have hmeas := measurable_of_continuousOn_compl_singleton 0 hf
  have hi (j : ℕ) : Integrable (u j) := by
    let W := Metric.ball (0:V) (6*(2:ℝ)^j)
    apply (integrableOn_iff_integrable_of_support_subset (s:=W) ?_).mp
    · apply volume.integrableOn_of_bounded measure_ball_lt_top.ne
          (f:=u j) (M:=M) _ (Eventually.of_forall (hm j))
      dsimp only [u]
      have Hsc : Measurable (fun x : V => ((2:ℝ)^j)⁻¹ • x) := by fun_prop
      exact (Complex.continuous_ofReal.measurable.comp ((hs.continuous.measurable.comp Hsc).mul hmeas)).aestronglyMeasurable
    · intro x hx
      by_contra h
      exact hx (hsupp j x (by simpa [W, Metric.mem_ball, not_lt] using h))
  apply piece_vol_bounds q u hM hi hm hsupp _ (fun p hp => exists_halfPeriod q hp)
  intro j i t ht hT x
  have H := hCbound i (L := (2:ℝ)^j) (one_le_pow₀ (by norm_num)) ht hT x
  change _ ∧ _ at H
  dsimp only
  have he (a : V) : ((translateDifference (t • normal q i))^[4] (u j)) a =
      (((Cutoff.diff (t • normal q i))^[4] (fun z => γ (((2:ℝ)^j)⁻¹ • z)*f z)) a : ℝ) :=
    iter_real_complex .. 
  rw [he,Complex.norm_real]
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (hMC i) (by positivity)),
    fun hx => by rw [H.2 hx,Complex.ofReal_zero]⟩

end IsingScaling.ShellCone

namespace IsingScaling.Packet
open IsingRotation IsingRotation.FourierShell ShellCone

/-- The dyadic mother annulus of every actual spatial tangent has summable
Fourier amplitudes away from frequency zero. The constants depend on the
cutoff and the finite cone covering; no scale-ratio input is used. -/
theorem OffOriginLimit.exists_volume_shell_bounds_of_source {g : Site → ℝ} {R : ℕ → ℕ}
    {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (hBnd : BoundedAwayFromOrigin f) :
    ∃ A : ℝ, VolumeShellBounds (fun j x => (spatialShell f j x:ℂ)) A := by
  classical
  obtain ⟨γ,hγ,hsum⟩ := exists_shell_pieces spatialShellMother spatialShellMother_smooth spatialShellMother_tsupport
  have H (q : Chart) := one_physical_piece src hR hf hsp hBnd q (γ q) (hγ q).1 (hγ q).2.1 (hγ q).2.2
  choose A hA using H
  refine ⟨∑ q, A q,?_⟩
  have hh := sum_volume hA
  convert hh using 1
  funext j x
  change ((spatialShellMother (((2:ℝ)^j)⁻¹ • x)*f x:ℝ):ℂ) =
    ∑ q, ((γ q (((2:ℝ)^j)⁻¹ • x)*f x:ℝ):ℂ)
  rw [←Complex.ofReal_sum,←Finset.sum_mul,hsum]

theorem OffOriginLimit.exists_volume_shell_bounds {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) :
    ∃ A : ℝ, VolumeShellBounds (fun j x => (spatialShell f j x:ℂ)) A :=
  hsp.exists_volume_shell_bounds_of_source (normalizedPacketSource_of_free hβ hg R) hR hf
    (hsp.boundedAwayFromOrigin_of_free hg hβ hR)

end IsingScaling.Packet

