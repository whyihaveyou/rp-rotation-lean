import MathlibProbe.IsingPacketCoordinates
import MathlibProbe.IsingComplexPackets
import MathlibProbe.NormalPacketFourier
import Mathlib.MeasureTheory.Group.Prod

/-! A three-dimensional locally integrable physical density gives the
energy-weighted integrability required by the one-dimensional normal
Fourier theorem, including packets adjacent to time zero. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate NNReal
namespace IsingScaling.Packet
open IsingRotation

private abbrev P₂ := ℝ × ℝ
private abbrev T₃ := ℝ × P₂

private theorem packet_pullback_locallyIntegrable (F : T₃ → ℝ) (hF : LocallyIntegrable F) :
    LocallyIntegrable (fun p : ℝ × P₂ × P₂ => F (p.1,p.2.1-p.2.2)) := by
  let T (p : ℝ × P₂ × P₂) : T₃ × P₂ := ((p.1,p.2.1-p.2.2),p.2.2)
  have hT : Continuous T := by unfold T; fun_prop
  have hP : MeasurePreserving T :=
    (volume_preserving_prodAssoc.symm).comp
      ((MeasurePreserving.id (volume : Measure ℝ)).prod
        (measurePreserving_sub_prod (volume : Measure P₂) volume))
  rw [locallyIntegrable_iff]
  intro K hK
  let S := (fun p => (T p).1) '' K
  let U := (fun p => (T p).2) '' K
  have hS : IsCompact S := hK.image (continuous_fst.comp hT)
  have hU : IsCompact U := hK.image (continuous_snd.comp hT)
  have h₁ : Integrable (S.indicator F) :=
    (integrable_indicator_iff hS.measurableSet).2 (hF.integrableOn_isCompact hS)
  have h₂ : Integrable (U.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hU.measurableSet).2 (integrableOn_const hU.measure_lt_top.ne)
  have hi := hP.integrable_comp_of_integrable (h₁.mul_prod h₂)
  apply hi.integrableOn.congr_fun _ hK.measurableSet
  intro p hp
  change S.indicator F (T p).1 * U.indicator (fun _ => (1:ℝ)) (T p).2 = _
  rw [indicator_of_mem (mem_image_of_mem _ hp), indicator_of_mem (mem_image_of_mem _ hp), mul_one]

private def timeCut (t : ℝ) := max 0 (min 1 (2-|t|))

private theorem timeCut_one {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) : timeCut t = 1 := by
  simp [timeCut,abs_of_pos ht.1,min_eq_left (show 1 ≤ 2-t by linarith [ht.2])]

private theorem timeCut_out {t : ℝ} (ht : t ∉ Icc (-2:ℝ) 2) : timeCut t = 0 := by
  have hh : 2 < |t| := by
    by_contra! hb
    exact ht (abs_le.mp hb)
  simp [timeCut,min_eq_right (show 2-|t| ≤ 1 by linarith),
    max_eq_left (show 2-|t| ≤ 0 by linarith)]

/-- Local L¹ in three-dimensional space passes to local time L¹ for the
actual Hermitian autocorrelation, through the volume-preserving
transverse difference map and a compact continuous cutoff in time. -/
theorem physical_packet_integrableOn_unit {f : Space → ℝ} (hloc : LocallyIntegrable f)
    (d : Bool) (φ : P₂ → ℂ) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    IntegrableOn (fun t : ℝ => ∫ p : P₂ × P₂, conj (φ p.1) * φ p.2 *
      (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ)) (Ioc 0 1) := by
  let L (w : ℝ × P₂ × P₂) := f (packetChart d (w.1,w.2.1-w.2.2))
  have hL : LocallyIntegrable L :=
    packet_pullback_locallyIntegrable _ (locallyIntegrable_packetChart hloc d)
  let χ (w : ℝ × P₂ × P₂) : ℂ := (timeCut w.1 : ℂ) * conj (φ w.2.1) * φ w.2.2
  have hc : Continuous χ := by unfold χ timeCut; fun_prop
  have hsχ : HasCompactSupport χ := by
    apply HasCompactSupport.intro ((isCompact_Icc (a := (-2:ℝ)) (b := 2)).prod (IsCompact.prod hs hs))
    intro w hw
    by_cases ht : w.1 ∈ Icc (-2:ℝ) 2
    · by_cases hx : w.2.1 ∈ tsupport φ
      · have hy : w.2.2 ∉ tsupport φ := fun hy => hw ⟨ht,hx,hy⟩
        simp [χ,image_eq_zero_of_notMem_tsupport hy]
      · simp [χ,image_eq_zero_of_notMem_tsupport hx]
    · simp [χ,timeCut_out ht]
  have hi := (hL.integrable_smul_right_of_hasCompactSupport hc hsχ).integral_prod_left
  apply hi.integrableOn.congr_fun _ measurableSet_Ioc
  intro t ht
  apply integral_congr_ae
  apply ae_of_all
  intro p
  simp [L,χ,timeCut_one ht,Complex.real_smul,mul_comm]

/-- Positive energy spectrum of the lattice limit, with finite inverse
linear energy weight and the complete two-sided physical packet. -/
theorem complexPlaneTimePacket_weighted_of_source {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ} (src : NormalizedPacketSource g R delay) (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (d : Bool) (φ : P₂ → ℂ)
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, Integrable PacketFourier.weight ρ ∧ ∀ t : ℝ, t ≠ 0 →
      PacketFourier.packet ρ t =
        ∫ p : P₂ × P₂, conj (φ p.1) * φ p.2 *
          (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ) := by
  obtain ⟨ρ,hρ⟩ := complexPlaneTimePacket_abs_laplace_of_source src hR hf hsp d φ hφ hs
  let J (t : ℝ) := ∫ p : P₂ × P₂, conj (φ p.1) * φ p.2 *
        (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ)
  have hJ : IntegrableOn J (Ioc (0:ℝ) 1) := physical_packet_integrableOn_unit hloc d φ hφ hs
  refine ⟨ρ, PacketFourier.integrable_weight_of_time_correlation (fun t => (J t).re) hJ.re ?_, ?_⟩
  · intro t ht
    have h := hρ t ht.ne'
    have he := congrArg Complex.re h.2
    exact ⟨by simpa [abs_of_pos ht] using h.1, by simpa [abs_of_pos ht,J] using he⟩
  · intro t ht
    simpa only [PacketFourier.packet,integral_complex_ofReal,neg_mul,mul_comm (|t|)] using
      (hρ t ht).2

/-- Specialization to the free Ising two-point kernel. -/
theorem complexPlaneTimePacket_weighted {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg : IsFreeTwoPoint β g) {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    {f : Space → ℝ} (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f)
    (hloc : LocallyIntegrable f) (d : Bool) (φ : P₂ → ℂ)
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ ρ : Measure ℝ≥0, Integrable PacketFourier.weight ρ ∧ ∀ t : ℝ, t ≠ 0 →
      PacketFourier.packet ρ t =
        ∫ p : P₂ × P₂, conj (φ p.1) * φ p.2 *
          (f (packetVector d t (p.1.1-p.2.1) (p.1.2-p.2.2)) : ℂ) :=
  complexPlaneTimePacket_weighted_of_source (normalizedPacketSource_of_free hβ hg R) hR hf hsp hloc d φ hφ hs

#print axioms complexPlaneTimePacket_weighted
end IsingScaling.Packet
