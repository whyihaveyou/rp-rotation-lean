import MathlibProbe.IsingSmoothPackets

/-! Hermitian transverse packets from the real Ising packet spectrum. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ComplexConjugate
namespace IsingScaling.Packet
open IsingRotation

private abbrev Plane := ℝ × ℝ

/-- Equality under the original cubic normal reflection also identifies
negative normal times, with both transverse coordinates fixed. -/
theorem packet_normal_reflect_of_cubic {g : Site → ℝ} (hcub : CubicKernel g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (d : Bool) {t : ℝ} (ht : 0<t) (x y : ℝ) :
    f (packetVector d (-t) x y) = f (packetVector d t x y) := by
  let p : Equiv.Perm (Fin 3) := if d then Equiv.swap 0 1 else Equiv.refl _
  let s (i : Fin 3) := !d && decide (i=0)
  let T := cubicMotion p s
  have hT : T (packetVector d t x y) = packetVector d (-t) x y := by
    cases d
    · ext i
      fin_cases i
      · change -(2*t) = 2*(-t)
        ring
      · rfl
      · rfl
    · ext i
      fin_cases i
      · change x-2*t = x+2*(-t)
        ring
      · change x+2*t = x-2*(-t)
        ring
      · rfl
  let q (n : ℕ) := packetSite d ⌊t*R n⌋₊
    (roundPoint (R n) x-roundPoint (R n) 0) (roundPoint (R n) y-roundPoint (R n) 0)
  have hq : Tendsto (fun n => scaledSite (R n) (q n)) atTop (𝓝 (packetVector d t x y)) := by
    simpa only [sub_zero] using packetSite_tendsto hR d ht x 0 y 0
  have hq' := T.continuous.continuousAt.tendsto.comp hq
  have hs' : Tendsto (fun n => scaledSite (R n) (signedPerm p s (q n))) atTop
        (𝓝 (T (packetVector d t x y))) := by
    simpa only [Function.comp_def, T, cubicMotion_scaledSite] using hq'
  have hn : T (packetVector d t x y) ≠ 0 := by
    intro hz
    apply packetVector_ne d ht x y
    apply T.injective
    simpa using hz
  rw [←hT]
  apply tendsto_nhds_unique (hsp _ hn _ hs')
  simpa only [hcub p s] using hsp _ (packetVector_ne d ht x y) q hq

/-- Specialization to the free Ising two-point kernel. -/
theorem packet_normal_reflect {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (d : Bool) {t : ℝ} (ht : 0<t) (x y : ℝ) :
    f (packetVector d (-t) x y) = f (packetVector d t x y) :=
  packet_normal_reflect_of_cubic (freeLimit_signedPerm hg) hR hsp d ht x y

/-- A modulated complex transverse test produces an actual positive-time
Laplace measure. Transverse exchange follows from a signed permutation
of the physical lattice spins in both permitted normal geometries. -/
theorem complexPlaneTimePacket_laplace_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    (φ : ℝ×ℝ → ℂ) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*E)) ρ ∧
      ((∫ E : ℝ≥0, Real.exp (-t*E) ∂ρ : ℝ) : ℂ) =
      ∫ p : (ℝ×ℝ)×(ℝ×ℝ), conj (φ p.1) * φ p.2 *
        (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ) := by
  let U : Plane → ℝ := fun p => (φ p).re
  let V : Plane → ℝ := fun p => (φ p).im
  have hU : HasCompactSupport U := hsupp.comp_left (g := Complex.re) rfl
  have hV : HasCompactSupport V := hsupp.comp_left (g := Complex.im) rfl
  obtain ⟨ρ,hρ⟩ := planeTimePacket_laplace_of_source src hR hf hsp d U (Complex.continuous_re.comp hφ) hU
  obtain ⟨σ,hσ⟩ := planeTimePacket_laplace_of_source src hR hf hsp d V (Complex.continuous_im.comp hφ) hV
  refine ⟨ρ+σ,?_⟩
  intro t ht
  refine ⟨(hρ t ht).1.add_measure (hσ t ht).1, ?_⟩
  let K (p : Plane×Plane) := f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2))
  have hK : Continuous K := by
    apply hf.comp_continuous _ (fun p => packetVector_ne d ht _ _)
    cases d <;> apply continuous_xyz <;> fun_prop
  let J (p : Plane×Plane) := conj (φ p.1) * φ p.2 * (K p : ℂ)
  have hJs (p : Plane×Plane) : conj (J p) = J p.swap := by
    have hsym : K p = K p.swap := packet_transverse_swap_of_cubic src.cubic hR hsp d ht _ _ _ _
    simp [J, hsym, mul_comm]
  have hreal : ((∫ p, J p).re : ℂ) = ∫ p, J p := by
    apply Complex.conj_eq_iff_re.mp
    rw [← integral_conj]
    simp_rw [hJs]
    exact integral_prod_swap J
  let JI (H : Plane → ℝ) (p : Plane×Plane) := H p.1 * H p.2 * K p
  have hJI (H : Plane → ℝ) (hH : Continuous H) (hHS : HasCompactSupport H) :
      Integrable (JI H) := by
    apply ((hH.comp continuous_fst).mul (hH.comp continuous_snd) |>.mul hK).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (IsCompact.prod hHS hHS)
    intro p hn
    by_cases h : p.1 ∈ tsupport H
    · have hh : p.2 ∉ tsupport H := fun hh => hn ⟨h,hh⟩
      simp [image_eq_zero_of_notMem_tsupport hh]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have hJ : Integrable J := by
    have hc : Continuous J := by unfold J; fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (IsCompact.prod hsupp hsupp)
    intro p hn
    by_cases h : p.1 ∈ tsupport φ
    · have hh : p.2 ∉ tsupport φ := fun hh => hn ⟨h,hh⟩
      simp [J, image_eq_zero_of_notMem_tsupport hh]
    · simp [J, image_eq_zero_of_notMem_tsupport h]
  have hre (p : Plane×Plane) : (J p).re = JI U p + JI V p := by
    simp [J, JI, U, V, Complex.mul_re]
    ring
  refine Eq.trans ?_ hreal
  apply congrArg Complex.ofReal
  rw [integral_add_measure (hρ t ht).1 (hσ t ht).1, (hρ t ht).2, (hσ t ht).2]
  change (∫ p, JI U p) + (∫ p, JI V p) = (∫ p, J p).re
  rw [← integral_add (hJI U (Complex.continuous_re.comp hφ) hU)
      (hJI V (Complex.continuous_im.comp hφ) hV)]
  calc
    _ = ∫ p, (J p).re := integral_congr_ae (ae_of_all _ fun p => (hre p).symm)
    _ = _ := integral_re hJ

/-- Specialization to the free Ising two-point kernel. -/
theorem complexPlaneTimePacket_laplace {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    (φ : ℝ×ℝ → ℂ) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*E)) ρ ∧
      ((∫ E : ℝ≥0, Real.exp (-t*E) ∂ρ : ℝ) : ℂ) =
      ∫ p : (ℝ×ℝ)×(ℝ×ℝ), conj (φ p.1) * φ p.2 *
        (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ) :=
  complexPlaneTimePacket_laplace_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp d φ hφ hsupp

#print axioms complexPlaneTimePacket_laplace

/-- The Fourier time pairing can therefore use the same physical complex
packet almost everywhere on the entire real line. -/
theorem complexPlaneTimePacket_abs_laplace_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    (φ : ℝ×ℝ → ℂ) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, t ≠ 0 →
      Integrable (fun E : ℝ≥0 => Real.exp (-|t| * E)) ρ ∧
      ((∫ E : ℝ≥0, Real.exp (-|t| * E) ∂ρ : ℝ) : ℂ) =
      ∫ p : (ℝ×ℝ)×(ℝ×ℝ), conj (φ p.1) * φ p.2 *
        (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ) := by
  obtain ⟨ρ,hρ⟩ := complexPlaneTimePacket_laplace_of_source src hR hf hsp d φ hφ hsupp
  refine ⟨ρ,fun t ht => ⟨(hρ |t| (abs_pos.mpr ht)).1, (hρ |t| (abs_pos.mpr ht)).2.trans ?_⟩⟩
  rcases lt_or_gt_of_ne ht with hn | hp
  · apply integral_congr_ae
    apply ae_of_all
    intro p
    have hh := packet_normal_reflect_of_cubic src.cubic hR hsp d (neg_pos.mpr hn)
      (p.1.1-p.2.1) (p.1.2-p.2.2)
    rw [neg_neg] at hh
    simpa only [abs_of_neg hn] using congrArg
      (fun a : ℝ => conj (φ p.1) * φ p.2 * (a:ℂ)) hh.symm
  · rw [abs_of_pos hp]

/-- Specialization to the free Ising two-point kernel. -/
theorem complexPlaneTimePacket_abs_laplace {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    (φ : ℝ×ℝ → ℂ) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, t ≠ 0 →
      Integrable (fun E : ℝ≥0 => Real.exp (-|t| * E)) ρ ∧
      ((∫ E : ℝ≥0, Real.exp (-|t| * E) ∂ρ : ℝ) : ℂ) =
      ∫ p : (ℝ×ℝ)×(ℝ×ℝ), conj (φ p.1) * φ p.2 *
        (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ) :=
  complexPlaneTimePacket_abs_laplace_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp d φ hφ hsupp

#print axioms complexPlaneTimePacket_abs_laplace

end IsingScaling.Packet
