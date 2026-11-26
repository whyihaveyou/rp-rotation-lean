import MathlibProbe.IsingOffOriginBounds
import MathlibProbe.IsingSmoothPackets
import MathlibProbe.IsingSpatialPacketDifferences

/-! Forward differences of the actual spatial tangent in positive-time charts.
A polarized pair uses the sum of the diagonal spectra to bound either sign of
its mixed numerator. For a general cubic kernel the result bounds the
mixed increment by (2 j h / t)^j times the same profile on the normal
at time t/2. Thus a bound off the origin is sufficient on any buffered
cone. Every packet used here has the same kernel, scale sequence and
susceptibility normalization as the spatial limit. -/
noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology NNReal
namespace IsingScaling.Packet

private def specFactor (t h : ℝ) (j : ℕ) (E : ℝ≥0) :=
  Real.exp (-t*(E:ℝ))*(1-Real.exp (-h*(E:ℝ)))^j

private lemma one_sub_exp_mem {h : ℝ} (hh : 0≤h) (E : ℝ≥0) :
    0≤1-Real.exp (-h*(E:ℝ)) ∧ 1-Real.exp (-h*(E:ℝ))≤1 := by
  refine ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) E.2)),
    sub_le_self _ (Real.exp_pos _).le⟩

private lemma specFactor_nonneg {h : ℝ} (hh : 0≤h) (t : ℝ) (j : ℕ) (E : ℝ≥0) :
    0≤specFactor t h j E := mul_nonneg (Real.exp_pos _).le (pow_nonneg (one_sub_exp_mem hh E).1 _)

private lemma integrable_specFactor {ρ : Measure ℝ≥0} {h t : ℝ} (hh : 0≤h) (j : ℕ)
    (H : Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ) :
    Integrable (specFactor t h j) ρ := by
  apply H.mono' (by unfold specFactor; fun_prop)
  exact Eventually.of_forall fun E => by
    rw [Real.norm_eq_abs,abs_of_nonneg (specFactor_nonneg hh t j E)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (pow_le_one₀ (one_sub_exp_mem hh E).1 (one_sub_exp_mem hh E).2)

/-- All orders of the finite increment identify the untruncated tilted
energy integral; only strictly positive-time tilts need be finite. -/
private theorem diff_rep {F : ℝ→ℝ} {ρ : Measure ℝ≥0}
    (H : ∀ t : ℝ, 0<t → Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = F t)
    {t h : ℝ} (ht : 0<t) (hh : 0≤h) (j m : ℕ) :
    (diff^[j]) (fun n : ℕ => F (t+n*h)) m =
      ∫ E, specFactor (t+m*h) h j E ∂ρ := by
  induction j generalizing m with
  | zero => simpa [specFactor] using (H (t+m*h) (by positivity)).2.symm
  | succ j ih =>
    rw [Function.iterate_succ_apply',diff,ih,ih,←integral_sub
      (integrable_specFactor hh j (H _ (by positivity)).1)
      (integrable_specFactor hh j (H _ (by positivity)).1)]
    apply integral_congr_ae
    exact Eventually.of_forall fun E => by
      dsimp only [specFactor]
      rw [show -(t+((m+1:ℕ):ℝ)*h)*(E:ℝ) = -(t+(m:ℝ)*h)*E+(-h*E) by push_cast; ring,
        Real.exp_add,pow_succ]
      ring

private lemma specFactor_upper (j : ℕ) {t h : ℝ} (ht : 0<t) (hh : 0≤h)
    (E : ℝ≥0) : specFactor t h j E ≤ (2*(j:ℝ)*h/t)^j * Real.exp (-(t/2)*(E:ℝ)) := by
  by_cases hz : j=0
  · subst j
    simp only [specFactor,pow_zero,mul_one,one_mul,Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right (by linarith) E.2
  have hj : 0<j := Nat.pos_of_ne_zero hz
  let a := t/(2*(j:ℝ))
  have hjr : 0<(j:ℝ) := by exact_mod_cast hj
  have ha : 0<a := by dsimp [a]; positivity
  have h₁ : 1-Real.exp (-h*(E:ℝ)) ≤ h*E := by linarith [Real.add_one_le_exp (-h*(E:ℝ))]
  have h₂ : (a*(E:ℝ))*Real.exp (-(a*(E:ℝ))) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have h₃ : (1-Real.exp (-h*(E:ℝ))) * Real.exp (-(a*(E:ℝ))) ≤ 2*(j:ℝ)*h/t := by
    calc
      _ ≤ (h/a) * ((a*(E:ℝ))*Real.exp (-(a*(E:ℝ)))) := by
        rw [show (h/a) * ((a*(E:ℝ))*Real.exp (-(a*(E:ℝ)))) =
          (h*(E:ℝ))*Real.exp (-(a*(E:ℝ))) by field_simp]
        exact mul_le_mul_of_nonneg_right h₁ (Real.exp_pos _).le
      _ ≤ h/a := mul_le_of_le_one_right (div_nonneg hh ha.le) h₂
      _ = _ := by dsimp [a]; field_simp
  have h₄ := pow_le_pow_left₀ (mul_nonneg (one_sub_exp_mem hh E).1 (Real.exp_pos _).le) h₃ j
  have H := mul_le_mul_of_nonneg_right h₄ (Real.exp_pos (-(t/2)*(E:ℝ))).le
  apply le_trans (b := ((1-Real.exp (-h*(E:ℝ))) * Real.exp (-(a*(E:ℝ))))^j * Real.exp (-(t/2)*E)) _ H
  apply le_of_eq
  unfold specFactor
  rw [mul_pow,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
  rw [show (j:ℝ)* -(a*(E:ℝ)) + -(t/2)*E = -t*E by dsimp [a]; field_simp; ring]
  ring

private lemma diff_linear₂ (A B : ℝ) (f g : ℕ→ℝ) (j : ℕ) :
    (diff^[j]) (fun n=> A*f n+B*g n) = fun n=>A*(diff^[j]) f n+B*(diff^[j]) g n := by
  induction j with
  | zero => rfl
  | succ j ih => funext n; simp only [Function.iterate_succ_apply',ih,diff]; ring

theorem OffOriginLimit.normal_difference_of_source {g : Site → ℝ}
    {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool) {t h : ℝ}
    (ht : 0<t) (hh : 0≤h) (x y : ℝ) (j : ℕ) :
    |(diff^[j]) (fun n : ℕ => f (packetVector d (t+n*h) x y)) 0| ≤
      (2*(j:ℝ)*h/t)^j * f (packetVector d (t/2) 0 0) := by
  let S (u : ℝ) := f (packetVector d u 0 0)
  let F (u : ℝ) := f (packetVector d u x y)
  let s (n : ℕ) := S (t+n*h)
  let v (n : ℕ) := F (t+n*h)
  have quad (b : ℝ) : 0≤ (1+b*b)*(diff^[j]) s 0+(2*b)*(diff^[j]) v 0 := by
    let c : Fin 2 → ℝ := ![1,b]
    let X : Fin 2 → ℝ := ![x,0]
    let Y : Fin 2 → ℝ := ![y,0]
    obtain ⟨ρ,H⟩ := finiteTimePacket_laplace_of_moments src.moments src.cube_pos hR hf hsp d c X Y
    have hs (u : ℝ) (hu : 0<u) : finiteTimePacket f d c X Y u = (1+b*b)*S u+(2*b)*F u := by
      have hswap := packet_transverse_swap_of_cubic src.cubic hR hsp d hu x 0 y 0
      simp only [sub_zero,zero_sub] at hswap
      simp only [finiteTimePacket,Fin.sum_univ_two,c,X,Y,Matrix.cons_val_zero,Matrix.cons_val_one,
        sub_self,sub_zero,zero_sub,one_mul,mul_one,S,F]
      rw [←hswap]; ring
    have hseq : (fun n : ℕ => finiteTimePacket f d c X Y (t+n*h)) =
        fun n => (1+b*b)*s n+(2*b)*v n := funext fun n=> hs _ (by positivity)
    have hr := diff_rep H ht hh j 0
    rw [hseq,diff_linear₂] at hr
    change (1+b*b)*(diff^[j]) s 0+(2*b)*(diff^[j]) v 0 = _ at hr
    rw [hr]
    exact integral_nonneg fun E => specFactor_nonneg hh _ _ E
  have hp := quad 1
  have hm := quad (-1)
  have hb : |(diff^[j]) v 0| ≤ (diff^[j]) s 0 := abs_le.mpr ⟨by linarith,by linarith⟩
  obtain ⟨ρ,H'⟩ := finiteTimePacket_laplace_of_moments src.moments src.cube_pos hR hf hsp d (fun _ : Unit => (1:ℝ))
    (fun _=>0) (fun _=>0)
  have H (u : ℝ) (hu : 0<u) : Integrable (fun E : ℝ≥0 => Real.exp (-u*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-u*(E:ℝ)) ∂ρ) = S u := by
    simpa [finiteTimePacket,S] using H' u hu
  have hrepr := diff_rep H ht hh j 0
  change (diff^[j]) s 0 = _ at hrepr
  simp only [Nat.cast_zero,zero_mul,add_zero] at hrepr
  have hint := integral_mono (integrable_specFactor hh j (H t ht).1)
    ((H (t/2) (by positivity)).1.const_mul ((2*(j:ℝ)*h/t)^j)) (specFactor_upper j ht hh)
  rw [integral_const_mul,(H _ (half_pos ht)).2] at hint
  exact hb.trans (hrepr.le.trans hint)

theorem OffOriginLimit.normal_difference {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool) {t h : ℝ}
    (ht : 0<t) (hh : 0≤h) (x y : ℝ) (j : ℕ) :
    |(diff^[j]) (fun n : ℕ => f (packetVector d (t+n*h) x y)) 0| ≤
      1728*(2*(j:ℝ)*h/t)^j/(min t 1)^3 := by
  let S (u : ℝ) := f (packetVector d u 0 0)
  have H := hsp.normal_difference_of_source (normalizedPacketSource_of_free hβ hg R) hR hf d ht hh x y j
  have hpoint := hsp.coordinate_density hg hβ hR (packetVector d (t/2) 0 0)
    (packetVector_ne d (half_pos ht) 0 0) 0
  have hval : (packetVector d (t/2) 0 0) 0 = t := by
    cases d <;> change _ = t <;> simp [packetVector,IsingRotation.xyz] <;> ring
  rw [hval,abs_of_pos ht] at hpoint
  have hpos : 0< min t 1 := lt_min ht zero_lt_one
  have HH := (le_div_iff₀ (pow_pos hpos 3)).mpr (show S (t/2)*(min t 1)^3≤1728 by
    simpa only [S,mul_comm] using hpoint)
  calc
    _ ≤ (2*(j:ℝ)*h/t)^j * S (t/2) := H
    _ ≤ (2*(j:ℝ)*h/t)^j * (1728/(min t 1)^3) := mul_le_mul_of_nonneg_left HH (by positivity)
    _ = _ := by ring

/-- Normal vectors use the physical lattice coordinates, so the face
diagonal has length √2. -/
def latticeNormal (d : Bool) : Space := IsingRotation.xyz 1 (if d then -1 else 0) 0

def chartTime (d : Bool) (z : Space) : ℝ := if d then (z 0-z 1)/4 else z 0/2

private lemma chart_line (d : Bool) (z : Space) (a : ℝ) :
    packetVector d (chartTime d z+a/2) (if d then (z 0+z 1)/2 else z 1) (z 2) =
      z+a • latticeNormal d := by
  ext i
  cases d <;> fin_cases i <;>
    simp [packetVector,chartTime,latticeNormal,IsingRotation.xyz] <;> ring

private lemma chart_inner (d : Bool) (z : Space) :
    inner ℝ (latticeNormal d) z = (if d then 4 else 2)*chartTime d z := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  cases d <;> simp [Fin.sum_univ_three,chartTime,latticeNormal,IsingRotation.xyz] <;> ring

theorem OffOriginLimit.cubic_profile_of_cubic {g : Site → ℝ} (hcub : CubicKernel g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool) (z : Space) :
    f (cubicMotion p s z) = f z := by
  by_cases hz : z=0
  · simp [hz]
  let T := cubicMotion p s
  let q (n : ℕ) := gridIndex (R n) z
  have hq := gridIndex_scaled_tendsto (v := fun _ => z) hR tendsto_const_nhds
  have hq' := T.continuous.continuousAt.tendsto.comp hq
  have hs' : Tendsto (fun n => scaledSite (R n) (signedPerm p s (q n))) atTop (𝓝 (T z)) := by
    simpa only [Function.comp_def,T,cubicMotion_scaledSite,q] using hq'
  apply tendsto_nhds_unique (hsp (T z) (fun hzero => hz (T.injective (hzero.trans T.map_zero.symm))) _ hs')
  exact (hsp z hz q hq).congr' (Eventually.of_forall fun n =>
    congrArg (fun v : ℝ => normalization g (R n) * v) (hcub p s (q n)).symm)

theorem OffOriginLimit.cubic_profile {β g} (hg : IsFreeTwoPoint β g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool) (z : Space) :
    f (cubicMotion p s z) = f z :=
  hsp.cubic_profile_of_cubic (freeLimit_signedPerm hg) hR p s z

/-- In a signed cubic chart, the source buffer is the single lower bound
on the scalar product with the physical normal. Its transverse coordinate
is unrestricted; the forward step can have any nonnegative size. -/
theorem OffOriginLimit.cone_difference_of_source {g : Site → ℝ}
    {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool) (d : Bool) (x : Space) {L δ h : ℝ}
    (hL : 1≤L) (hδ : 0<δ) (hh : 0≤h)
    (hbuf : δ*L ≤ inner ℝ ((cubicMotion p s).symm (latticeNormal d)) x)
    (j : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hself : ∀ u : ℝ, δ/4 ≤ u → f (packetVector d (u/2) 0 0) ≤ B) :
    |(diff^[j]) (fun n : ℕ => f (x+((n:ℝ)*h) • (cubicMotion p s).symm (latticeNormal d))) 0| ≤
      (B*(4*(j:ℝ)/δ)^j)*(h/L)^j := by
  let T := cubicMotion p s
  let z := T x
  let t := chartTime d z
  have hI : inner ℝ (T.symm (latticeNormal d)) x = inner ℝ (latticeNormal d) z :=
    T.symm.inner_map_eq_flip _ _
  rw [hI,chart_inner] at hbuf
  have htL : δ*L/4 ≤ t := by
    change δ*L ≤ (if d then (4:ℝ) else 2)*t at hbuf
    have hδL : 0<δ*L := mul_pos hδ (by linarith)
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte] at hbuf <;> linarith
  have ht : 0<t := (by positivity : 0<δ*L/4).trans_le htL
  have ht0 : δ/4≤t := by nlinarith only [htL,mul_le_mul_of_nonneg_left hL hδ.le]
  let X := if d then (z 0+z 1)/2 else z 1
  have H := hsp.normal_difference_of_source src hR hf d ht (show 0≤h/2 by positivity) X (z 2) j
  have he (n : ℕ) : t + (n:ℝ)*(h/2) = chartTime d z + ((n:ℝ)*h)/2 := by dsimp [t]; ring
  have hv (n : ℕ) : f (packetVector d (t+n*(h/2)) X (z 2)) =
      f (x+((n:ℝ)*h) • T.symm (latticeNormal d)) := by
    rw [he,show X=(if d then (z 0+z 1)/2 else z 1) from rfl,chart_line]
    convert hsp.cubic_profile_of_cubic src.cubic hR p s (x+((n:ℝ)*h) • T.symm (latticeNormal d)) using 1
    congr 1
    simp [z,T]
  simp_rw [hv] at H
  change |(diff^[j]) (fun n : ℕ => f (x+((n:ℝ)*h) • T.symm (latticeNormal d))) 0| ≤ _
  have hL' : 0<L := by linarith
  have h₁ : 2*(j:ℝ)*(h/2)/t ≤ (4*(j:ℝ)/δ)*(h/L) := by
    rw [div_le_iff₀ ht]
    field_simp [hδ.ne',hL'.ne']
    nlinarith only [mul_le_mul_of_nonneg_right htL (show 0≤4*(j:ℝ)*h by positivity)]
  calc
    _ ≤ (2*(j:ℝ)*(h/2)/t)^j * f (packetVector d (t/2) 0 0) := H
    _ ≤ (2*(j:ℝ)*(h/2)/t)^j * B := mul_le_mul_of_nonneg_left (hself t ht0) (by positivity)
    _ ≤ ((4*(j:ℝ)/δ)*(h/L))^j * B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h₁ j) hB
    _ = _ := by rw [mul_pow]; ring

theorem OffOriginLimit.cone_difference {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool) (d : Bool) (x : Space) {L δ h : ℝ}
    (hL : 1≤L) (hδ : 0<δ) (hh : 0≤h)
    (hbuf : δ*L ≤ inner ℝ ((cubicMotion p s).symm (latticeNormal d)) x)
    (j : ℕ) :
    |(diff^[j]) (fun n : ℕ => f (x+((n:ℝ)*h) • (cubicMotion p s).symm (latticeNormal d))) 0| ≤
      (1728*(4*(j:ℝ)/δ)^j/(min (δ/4) 1)^3)*(h/L)^j := by
  let B := 1728/(min (δ/4) 1)^3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hself (u : ℝ) (hu : δ/4 ≤ u) : f (packetVector d (u/2) 0 0) ≤ B := by
    have hu' : 0 < u := lt_of_lt_of_le (by positivity : 0<δ/4) hu
    have hp := hsp.coordinate_density hg hβ hR (packetVector d (u/2) 0 0)
      (packetVector_ne d (half_pos hu') 0 0) 0
    have hv : (packetVector d (u/2) 0 0) 0 = u := by
      cases d <;> simp [packetVector,IsingRotation.xyz] <;> ring
    rw [hv,abs_of_pos hu'] at hp
    apply (le_div_iff₀ (pow_pos (lt_min (by positivity) zero_lt_one) 3)).mpr
    have hnn := hsp.nonneg_of_free hg hβ hR _ (packetVector_ne d (half_pos hu') 0 0)
    calc
      _ ≤ f (packetVector d (u/2) 0 0)*(min u 1)^3 := by
        apply mul_le_mul_of_nonneg_left _ hnn
        exact pow_le_pow_left₀ (le_min (by positivity) zero_le_one) (min_le_min_right 1 hu) 3
      _ ≤ _ := by simpa only [mul_comm] using hp
  have H := hsp.cone_difference_of_source (normalizedPacketSource_of_free hβ hg R)
    hR hf p s d x hL hδ hh hbuf j hB hself
  dsimp only [B] at H
  convert H using 1 <;> ring

/-- The three positive normals of one cubic shell chart. -/
private theorem exists_normal_chart (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool)
    (i : Fin 3) (v : Space) (hv : v = (cubicMotion p s).symm
      (![IsingRotation.xyz 1 0 0,IsingRotation.xyz 1 (-1) 0,IsingRotation.xyz 1 0 (-1)] i)) :
    ∃ (q : Equiv.Perm (Fin 3)) (s' : Fin 3 → Bool) (d : Bool),
      v = (cubicMotion q s').symm (latticeNormal d) := by
    fin_cases i
    · exact ⟨p,s,false,hv⟩
    · exact ⟨p,s,true,hv⟩
    · let e : Equiv.Perm (Fin 3) := Equiv.swap 1 2
      let q := e.trans p
      let s' : Fin 3 → Bool := fun i => s (e i)
      refine ⟨q,s',true,?_⟩
      let T := cubicMotion p s
      let U := cubicMotion q s'
      let z := IsingRotation.xyz 1 0 (-1)
      change v = T.symm z at hv
      change v = U.symm (latticeNormal true)
      apply U.injective
      rw [LinearIsometryEquiv.apply_symm_apply,hv]
      have he (w : Space) (i : Fin 3) : U w i = T w (e i) := rfl
      ext i
      rw [he,LinearIsometryEquiv.apply_symm_apply]
      fin_cases i <;> rfl

theorem OffOriginLimit.three_cone_differences_of_source {g : Site → ℝ}
    {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool) (i : Fin 3) (x : Space) {L δ h : ℝ}
    (hL : 1≤L) (hδ : 0<δ) (hh : 0≤h)
    (v : Space) (hv : v = (cubicMotion p s).symm
      (![IsingRotation.xyz 1 0 0,IsingRotation.xyz 1 (-1) 0,IsingRotation.xyz 1 0 (-1)] i))
    (hbuf : δ*L ≤ inner ℝ v x) (j : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hself : ∀ d : Bool, ∀ u : ℝ, δ/4 ≤ u → f (packetVector d (u/2) 0 0) ≤ B) :
    |(diff^[j]) (fun n : ℕ => f (x+((n:ℝ)*h) • v)) 0| ≤
      (B*(4*(j:ℝ)/δ)^j)*(h/L)^j := by
  obtain ⟨q,s',d,hd⟩ := exists_normal_chart p s i v hv
  rw [hd] at hbuf ⊢
  exact hsp.cone_difference_of_source src hR hf q s' d x hL hδ hh hbuf j hB (hself d)

theorem OffOriginLimit.three_cone_differences {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3→Bool) (i : Fin 3) (x : Space) {L δ h : ℝ}
    (hL : 1≤L) (hδ : 0<δ) (hh : 0≤h)
    (v : Space) (hv : v = (cubicMotion p s).symm
      (![IsingRotation.xyz 1 0 0,IsingRotation.xyz 1 (-1) 0,IsingRotation.xyz 1 0 (-1)] i))
    (hbuf : δ*L ≤ inner ℝ v x) (j : ℕ) :
    |(diff^[j]) (fun n : ℕ => f (x+((n:ℝ)*h) • v)) 0| ≤
      (1728*(4*(j:ℝ)/δ)^j/(min (δ/4) 1)^3)*(h/L)^j := by
  obtain ⟨q,s',d,hd⟩ := exists_normal_chart p s i v hv
  rw [hd] at hbuf ⊢
  exact hsp.cone_difference hg hβ hR hf q s' d x hL hδ hh hbuf j

end IsingScaling.Packet
