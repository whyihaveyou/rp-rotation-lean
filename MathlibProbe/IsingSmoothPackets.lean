import MathlibProbe.IsingOffOriginPackets
import MathlibProbe.PacketQuadrature

/-! Compact transverse smearing of the original lattice packet spectrum
on a coordinate normal and on a face-diagonal normal. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace IsingScaling.Packet
open IsingRotation

/-- The packet autocorrelation obtained by integration over two copies of
a compact transverse support has a positive Laplace spectrum on t>0.
The signed test function and transverse coordinates may vary arbitrarily
within their stated integrability and continuity classes. -/
theorem compactTimePacket_laplace_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    {X : Type} [MetricSpace X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] (φ : X → ℝ) (hφ : Integrable φ μ) (hm : Measurable φ)
    (x y : X → ℝ) (hx : Continuous x) (hy : Continuous y) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*E) ∂ρ) = ∫ p : X×X,
        φ p.1 * φ p.2 * f (packetVector d t (x p.1-x p.2) (y p.1-y p.2)) ∂μ.prod μ := by
  let K (t : Laplace.Time) : C(X×X,ℝ) :=
    ⟨fun p => f (packetVector d t (x p.1-x p.2) (y p.1-y p.2)), by
      apply hf.comp_continuous _ (fun p => packetVector_ne d t.2 _ _)
      cases d <;> apply continuous_xyz <;> fun_prop⟩
  obtain ⟨ρ,hρ⟩ := Quadrature.exists_smooth_packet_laplace μ φ hφ hm K (by
    intro S c
    obtain ⟨σ,hσ⟩ := finiteTimePacket_laplace_of_moments src.moments src.cube_pos hR hf hsp d (ι := ↥S)
      (fun i => c i) (fun i => x i) (fun i => y i)
    refine ⟨σ, fun t => ⟨(hσ t t.2).1, (hσ t t.2).2.trans ?_⟩⟩
    calc
      _ = ∑ i : ↥S, ∑ j ∈ S, c i*c j*K t (i,j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_coe_sort S (fun j => c i*c j*K t (i,j))
      _ = _ := Finset.sum_coe_sort S (fun i => ∑ j ∈ S, c i*c j*K t (i,j)))
  exact ⟨ρ, fun t ht => hρ ⟨t,ht⟩⟩

/-- Specialization to the free Ising two-point kernel. -/
theorem compactTimePacket_laplace {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    {X : Type} [MetricSpace X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] (φ : X → ℝ) (hφ : Integrable φ μ) (hm : Measurable φ)
    (x y : X → ℝ) (hx : Continuous x) (hy : Continuous y) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*E) ∂ρ) = ∫ p : X×X,
        φ p.1 * φ p.2 * f (packetVector d t (x p.1-x p.2) (y p.1-y p.2)) ∂μ.prod μ :=
  compactTimePacket_laplace_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp d μ φ hφ hm x y hx hy

#print axioms compactTimePacket_laplace

/-- In particular, the physical packet may be specified directly by a
compactly supported real test on the entire transverse coordinate plane. -/
theorem planeTimePacket_laplace_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    (φ : ℝ×ℝ → ℝ) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*E) ∂ρ) =
      ∫ p : (ℝ×ℝ)×(ℝ×ℝ), φ p.1 * φ p.2 *
        f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) := by
  let K : Set (ℝ×ℝ) := tsupport φ ∪ {0}
  have hK : IsCompact K := (show IsCompact (tsupport φ) from hsupp).union isCompact_singleton
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := ⟨⟨0,Or.inr (mem_singleton _)⟩⟩
  let μ := (volume : Measure (ℝ×ℝ)).comap ((↑) : K → ℝ×ℝ)
  have emb := MeasurableEmbedding.subtype_coe hK.measurableSet
  let : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val emb
  have hpres : MeasurePreserving ((↑) : K → ℝ×ℝ) μ (volume.restrict K) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe hK.measurableSet volume⟩
  have htest := hφ.comp (continuous_subtype_val (p := (· ∈ K)))
  obtain ⟨ρ,hρ⟩ := compactTimePacket_laplace_of_source src hR hf hsp d μ _ 
    (htest.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) htest.measurable
    (fun v => v.val.1) (fun v => v.val.2)
    (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
  refine ⟨ρ, fun t ht => ⟨(hρ t ht).1, (hρ t ht).2.trans ?_⟩⟩
  let F (p : (ℝ×ℝ)×(ℝ×ℝ)) := φ p.1 * φ p.2 *
        f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2))
  calc
    _ = ∫ p, F p ∂(volume.restrict K).prod (volume.restrict K) :=
      (hpres.prod hpres).integral_comp (emb.prodMap emb) F
    _ = ∫ p, F p := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      by_cases hx : p.1 ∈ K
      · have hy : p.2 ∉ tsupport φ := fun h => hp ⟨hx,Or.inl h⟩
        simp [F, image_eq_zero_of_notMem_tsupport hy]
      · have hh : p.1 ∉ tsupport φ := fun h => hx (Or.inl h)
        simp [F, image_eq_zero_of_notMem_tsupport hh]

/-- Specialization to the free Ising two-point kernel. -/
theorem planeTimePacket_laplace {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    (φ : ℝ×ℝ → ℝ) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*E)) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*E) ∂ρ) =
      ∫ p : (ℝ×ℝ)×(ℝ×ℝ), φ p.1 * φ p.2 *
        f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) :=
  planeTimePacket_laplace_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp d φ hφ hsupp

#print axioms planeTimePacket_laplace

/-- Reflection of both transverse coordinates preserves a fixed normal
displacement. For an oblique normal this is the signed permutation
(a,b,c) ↦ (-b,-a,-c) of the original spins. -/
theorem packet_transverse_swap_of_cubic {g : Site → ℝ} (hcub : CubicKernel g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (d : Bool) {t : ℝ} (ht : 0<t)
    (x₁ x₂ y₁ y₂ : ℝ) :
    f (packetVector d t (x₁-x₂) (y₁-y₂)) =
      f (packetVector d t (x₂-x₁) (y₂-y₁)) := by
  have swap (k : ℕ) (a b u v : ℤ) :
      g (packetSite d k (b-a) (v-u)) = g (packetSite d k (a-b) (u-v)) := by
    cases d
    · let T := signedPerm (Equiv.refl _) (fun i => decide (i ≠ 0))
      have he : T (packetSite false k (a-b) (u-v)) = packetSite false k (b-a) (v-u) := by
        funext i
        fin_cases i
        · rfl
        · change -(a-b) = b-a
          ring
        · change -(u-v) = v-u
          ring
      rw [← he]
      exact hcub _ _ _
    · let T := signedPerm (Equiv.swap 0 1) (fun _ => true)
      have he : T (packetSite true k (a-b) (u-v)) = packetSite true k (b-a) (v-u) := by
        funext i
        fin_cases i
        · change -(a-b-(2*k:ℕ)) = b-a+(2*k:ℕ)
          ring
        · change -(a-b+(2*k:ℕ)) = b-a-(2*k:ℕ)
          ring
        · change -(u-v) = v-u
          ring
      rw [← he]
      exact hcub _ _ _
  have h₁ := hsp _ (packetVector_ne d ht _ _) _ (packetSite_tendsto hR d ht x₁ x₂ y₁ y₂)
  have h₂ := hsp _ (packetVector_ne d ht _ _) _ (packetSite_tendsto hR d ht x₂ x₁ y₂ y₁)
  apply tendsto_nhds_unique h₁
  exact h₂.congr' (Eventually.of_forall fun n => congrArg ((normalization g (R n)) * ·)
    (swap _ _ _ _ _))

/-- Specialization to the free Ising two-point kernel. -/
theorem packet_transverse_swap {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hsp : OffOriginLimit g R f) (d : Bool) {t : ℝ} (ht : 0<t)
    (x₁ x₂ y₁ y₂ : ℝ) :
    f (packetVector d t (x₁-x₂) (y₁-y₂)) =
      f (packetVector d t (x₂-x₁) (y₂-y₁)) :=
  packet_transverse_swap_of_cubic (freeLimit_signedPerm hg) hR hsp d ht x₁ x₂ y₁ y₂

end IsingScaling.Packet
