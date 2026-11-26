import MathlibProbe.IsingOffOriginPackets
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Exact change of variables for physical axial and oblique packets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix ENNReal
namespace IsingScaling.Packet
open IsingRotation

/-- Coordinates are ordered as (normal time, transverse x, transverse y). -/
def packetChart (d : Bool) : (ℝ × ℝ × ℝ) ≃L[ℝ] Space :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun v => packetVector d v.1 v.2.1 v.2.2
    invFun := fun w => if d then ((w 0-w 1)/4,(w 0+w 1)/2,w 2) else
      ((w 0)/2,w 1,w 2)
    map_add' := by
      intro u v
      cases d <;> ext i <;> fin_cases i <;> simp [packetVector,xyz] <;> ring
    map_smul' := by
      intro r v
      cases d <;> ext i <;> fin_cases i <;> simp [packetVector,xyz] <;> ring
    left_inv := by
      intro v
      cases d <;> ext <;> simp [packetVector,xyz]
      ring
    right_inv := by
      intro v
      cases d <;> ext i <;> fin_cases i <;> simp [packetVector,xyz] <;> ring }

@[simp] theorem packetChart_apply (d : Bool) (v : ℝ×ℝ×ℝ) :
    packetChart d v = packetVector d v.1 v.2.1 v.2.2 := rfl

private theorem coordVolume : MeasurePreserving (fun a : ℝ×ℝ×ℝ => ![a.1,a.2.1,a.2.2]) := by
  let e₃ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  let e := e₃.trans ((MeasurableEquiv.refl ℝ).prodCongr e₂)
  have h₃ : MeasurePreserving e₃ := volume_preserving_piFinSuccAbove _ _
  have h₂ : MeasurePreserving e₂ := volume_preserving_piFinTwo _
  have he : MeasurePreserving e :=
    ((MeasurePreserving.id volume).prod h₂).comp h₃
  have eq : (fun a : ℝ×ℝ×ℝ => ![a.1,a.2.1,a.2.2]) = e.symm := by
    funext a
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  rw [eq]
  exact he.symm

private def coordsM (d : Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if d then !![2,1,0;-2,1,0;0,0,1] else !![2,0,0;0,1,0;0,0,1]

/-- Pushforward factors of Lebesgue volume are 1/4 in the face-diagonal
chart and 1/2 in the axial chart. -/
theorem packetChart_volume (d : Bool) : MeasurePreserving (packetChart d) volume
    ((if d then (4:ℝ≥0∞)⁻¹ else (2:ℝ≥0∞)⁻¹) • volume) := by
  let F := Matrix.toLin' (coordsM d)
  let c := if d then (4:ℝ≥0∞)⁻¹ else (2:ℝ≥0∞)⁻¹
  have hd : LinearMap.det F = if d then 4 else 2 := by
    rw [show LinearMap.det F = Matrix.det (coordsM d) from LinearMap.det_toLin' _, Matrix.det_fin_three]
    cases d
    · change (2:ℝ)*1*1-2*0*0-0*0*1+0*0*0+0*0*0-0*1*0 = 2
      norm_num
    · change (2:ℝ)*1*1-2*0*0-1*(-2)*1+1*0*0+0*(-2)*0-0*1*0 = 4
      norm_num
  have hf : MeasurePreserving F volume (c • volume) := by
    refine ⟨F.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (f := F) (by rw [hd]; cases d <;> norm_num)]
    rw [hd]
    cases d <;> norm_num [c, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_inv_of_pos]
  have hs := PiLp.volume_preserving_toLp (Fin 3)
  have hq : MeasurePreserving (@WithLp.toLp 2 (Fin 3 → ℝ)) (c • volume) (c • volume) :=
    ⟨hs.measurable, by rw [Measure.map_smul, hs.map_eq]⟩
  have heq : (fun a : ℝ×ℝ×ℝ => WithLp.toLp 2 (F ![a.1,a.2.1,a.2.2])) = packetChart d := by
    funext a
    cases d <;> ext i <;> fin_cases i <;>
      simp [F,coordsM,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
        packetVector,xyz] <;> ring
  rw [← heq]
  exact hq.comp (hf.comp coordVolume)

theorem locallyIntegrable_packetChart {f : Space → ℝ} (hf : LocallyIntegrable f)
    (d : Bool) : LocallyIntegrable (f ∘ packetChart d) := by
  rw [locallyIntegrable_iff]
  intro K hK
  let S := packetChart d '' K
  have hS : IsCompact S := hK.image (packetChart d).continuous
  have hi : Integrable (S.indicator f) :=
    (integrable_indicator_iff hS.measurableSet).2 (hf.integrableOn_isCompact hS)
  have hj := (packetChart_volume d).integrable_comp_of_integrable
    (hi.smul_measure (c := if d then (4:ℝ≥0∞)⁻¹ else (2:ℝ≥0∞)⁻¹) (by cases d <;> norm_num))
  apply hj.integrableOn.congr_fun _ hK.measurableSet
  intro v hv
  exact indicator_of_mem (mem_image_of_mem (packetChart d) hv) f

#print axioms packetChart_volume
end IsingScaling.Packet
