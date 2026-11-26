import MathlibProbe.RotorPeriodicPairResponse
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Common periodic spin laws for the rotor pressure readouts

A uniformly chosen origin embeds a configuration of the finite surface-spin
Gibbs law into the compact space of spin configurations on the lattice.
The pressure pair readout is its correlation. Translation permutes the
origins and compactness extracts one limit for all continuous cylinder tests.
-/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
namespace IsingScaling.Rotor.PressureSelection

abbrev SpinField (N : ℕ) := Site → Spin N

private theorem continuousEnergy {N : ℕ} {V : Type*} [Fintype V] (H : V → V → ℝ) :
    Continuous (energy (N := N) H) := by
  unfold energy
  exact (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
    continuous_const.mul (by fun_prop)))).div_const _

/-- The exact normalized periodic Gibbs law of the unit sphere spins. -/
def sphereGibbs (N : ℕ) [NeZero N] {V : Type*} [Fintype V] (H : V → V → ℝ) :
    ProbabilityMeasure (V → Spin N) :=
  let θ := Measure.pi (fun _ : V => SiteReflection.surfacePrior N)
  ⟨θ.tilted (energy H), isProbabilityMeasure_tilted
    (((continuousEnergy (N := N) H).rexp).integrable_of_hasCompactSupport
      (μ := θ) (HasCompactSupport.of_compactSpace _))⟩

theorem gibbs_integral_dot (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (H : V → V → ℝ) (v w : V) :
    (∫ s : V → Spin N, ⟪(s v).val, (s w).val⟫_ℝ ∂(sphereGibbs N H : Measure (V → Spin N))) =
      dotPair N H v w := by
  let θ := Measure.pi (fun _ : V => SiteReflection.surfacePrior N)
  change (∫ s, _ ∂(θ.tilted (energy H))) =
    (∫ s : V → Spin N, Real.exp (energy H s) * ⟪(s v).val, (s w).val⟫_ℝ ∂θ) /
      (∫ s : V → Spin N, Real.exp (energy H s) ∂θ)
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div]

def liftAt {N : ℕ} {V : Type*} (D : Site → V → V) (v : V)
    (s : V → Spin N) (x : Site) : Spin N := s (D x v)

private theorem continuousLift {N : ℕ} {V : Type*} (D : Site → V → V) (v : V) :
    Continuous (liftAt (N := N) D v) :=
  continuous_pi fun x => continuous_apply (D x v)

private def atRoot {N : ℕ} {V : Type*} [Fintype V] (D : Site → V → V) (v : V)
    (P : ProbabilityMeasure (V → Spin N)) : ProbabilityMeasure (SpinField N) :=
  P.map (continuousLift D v).measurable.aemeasurable

/-- Choose one physical spin configuration and an independent uniform site. -/
def rootedLaw (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (H : V → V → ℝ) : ProbabilityMeasure (SpinField N) := by
  classical
  let μ (v : V) : Measure (SpinField N) := atRoot D v (sphereGibbs N H)
  refine ⟨(Fintype.card V : ℝ≥0∞)⁻¹ • ∑ v, μ v, ⟨?_⟩⟩
  have h (v : V) : μ v Set.univ = 1 := (atRoot D v (sphereGibbs N H)).prop.measure_univ
  simp [Measure.smul_apply, Measure.finsetSum_apply, h]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

theorem rootedLaw_integral (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (H : V → V → ℝ) (F : C(SpinField N, ℝ)) :
    (∫ s, F s ∂(rootedLaw N D H : Measure _)) =
      (∑ v, ∫ s, F (liftAt D v s) ∂(sphereGibbs N H : Measure _)) / Fintype.card V := by
  classical
  let μ (v : V) : Measure (SpinField N) := atRoot D v (sphereGibbs N H)
  have hi (v : V) : Integrable F (μ v) := by
    let : IsProbabilityMeasure (μ v) := (atRoot D v (sphereGibbs N H)).prop
    exact F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ s, F s ∂((Fintype.card V : ℝ≥0∞)⁻¹ • ∑ v, μ v)) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun v _ => hi v)]
  have hv (v : V) : (∫ s, F s ∂(μ v)) =
      ∫ s, F (liftAt D v s) ∂(sphereGibbs N H : Measure _) :=
    integral_map (continuousLift D v).measurable.aemeasurable F.continuous.aestronglyMeasurable
  simp only [hv, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]

def fieldDot (N : ℕ) (x y : Site) : C(SpinField N, ℝ) where
  toFun s := ⟪(s x).val,(s y).val⟫_ℝ
  continuous_toFun := by fun_prop

def fieldPair {N : ℕ} (P : ProbabilityMeasure (SpinField N)) (z : Site) : ℝ :=
  ∫ s, fieldDot N 0 z s ∂(P : Measure _)

theorem fieldPair_rootedLaw (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (h0 : ∀ v, D 0 v = v) (H : V → V → ℝ) (z : Site) :
    fieldPair (rootedLaw N D H) z = averagedDot N D H z := by
  rw [fieldPair, rootedLaw_integral, averagedDot]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simpa [fieldDot, liftAt, h0] using gibbs_integral_dot N H v (D z v)

/-- Simultaneous compactness of the full sphere-spin field. -/
theorem spinField_subsequence (N : ℕ) (P : ℕ → ProbabilityMeasure (SpinField N)) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ l : ℕ → ℕ,
      StrictMono l ∧ Tendsto (P ∘ l) atTop (𝓝 Q) ∧
      ∀ F : C(SpinField N, ℝ), Tendsto (fun m => ∫ s, F s ∂(P (l m) : Measure _))
         atTop (𝓝 (∫ s, F s ∂(Q : Measure _))) := by
  obtain ⟨Q, l, hl, hQ⟩ := CompactSpace.tendsto_subseq P
  exact ⟨Q, l, hl, hQ, fun F =>
    (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hQ⟩

/-- Displacement acts by the ordinary additive group of the original lattice. -/
structure DisplacementAction {V : Type*} (D : Site → V → V) : Prop where
  zero : ∀ v, D 0 v = v
  add : ∀ x y v, D (x+y) v = D x (D y v)

namespace DisplacementAction

def shiftEquiv {V : Type*} {D : Site → V → V} (hD : DisplacementAction D) (x : Site) :
    V ≃ V where
  toFun := D x
  invFun := D (-x)
  left_inv v := by rw [← hD.add, neg_add_cancel, hD.zero]
  right_inv v := by rw [← hD.add, add_neg_cancel, hD.zero]

end DisplacementAction

namespace Seam

private theorem period_translate {L : ℕ} {p q : IsingScaling.Site}
    (h : SamePeriodClass L p q) (z : IsingScaling.Site) : SamePeriodClass L (p+z) (q+z) := by
  obtain ⟨i,j,k,h0,h1,h2⟩ := h
  exact ⟨i,j,k,by simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using h0,
    by simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using h1,
    by simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using h2⟩

private theorem period_trans {L : ℕ} {p q r : IsingScaling.Site}
    (h : SamePeriodClass L p q) (h' : SamePeriodClass L q r) : SamePeriodClass L p r := by
  obtain ⟨i,j,k,h0,h1,h2⟩ := h
  obtain ⟨i',j',k',h0',h1',h2'⟩ := h'
  exact ⟨i+i',j+j',k+k',by linear_combination h0 + h0',
    by linear_combination h1 + h1',by linear_combination h2 + h2'⟩

theorem adapted_displacement_action (L : ℕ) [NeZero L] :
    DisplacementAction (adaptedDestination (L := L)) := by
  constructor
  · intro v
    apply (adapted_step_unique L _ _ _).mp
    exact ⟨0,0,0,by simp,by simp,by simp⟩
  · intro x y v
    apply (adapted_step_unique L _ _ _).mp
    have h := period_trans (period_translate (adapted_step_same_period L y v) x)
      (adapted_step_same_period L x (adaptedDestination y v))
    simpa only [add_assoc, add_comm y x] using h

private def cyclicResidue {L : ℕ} [NeZero L] (v : Fin L) (z : ℤ) : Fin L :=
  ⟨(((v.val : ℤ)+z)%L).toNat, by
    have hL : 0 < (L : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h := Int.emod_lt_of_pos ((v.val : ℤ)+z) hL
    omega⟩

private theorem cyclicResidue_zero {L : ℕ} [NeZero L] (v : Fin L) : cyclicResidue v 0 = v := by
  apply Fin.ext
  change (((v.val : ℤ)+0)%L).toNat = v.val
  have h : (v.val : ℤ) < L := by exact_mod_cast v.isLt
  simp [Int.emod_eq_of_lt (by positivity : 0 ≤ (v.val : ℤ)) h]

private theorem cyclicResidue_add {L : ℕ} [NeZero L] (v : Fin L) (x y : ℤ) :
    cyclicResidue v (x+y) = cyclicResidue (cyclicResidue v y) x := by
  apply Fin.ext
  dsimp [cyclicResidue]
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hL), Int.emod_add_emod]
  rw [add_comm x y, add_assoc]

theorem cubic_displacement_action (L : ℕ) [NeZero L] :
    DisplacementAction (baseMove (L := L)) := by
  constructor
  · rintro ⟨i,j,k⟩
    change (cyclicResidue i 0, cyclicResidue j 0, cyclicResidue k 0) = _
    simp only [cyclicResidue_zero]
  · rintro x y ⟨i,j,k⟩
    change (cyclicResidue i (x 0+y 0),cyclicResidue j (x 1+y 1), cyclicResidue k (x 2+y 2)) =
      (cyclicResidue (cyclicResidue i (y 0)) (x 0),cyclicResidue (cyclicResidue j (y 1)) (x 1),
      cyclicResidue (cyclicResidue k (y 2)) (x 2))
    simp only [cyclicResidue_add]

end Seam

def shiftField {N : ℕ} (u : Site) : C(SpinField N, SpinField N) where
  toFun s x := s (x+u)
  continuous_toFun := continuous_pi fun x => continuous_apply (x+u)

def ShiftInvariant {N : ℕ} (P : ProbabilityMeasure (SpinField N)) : Prop :=
  ∀ u : Site, MeasurePreserving (shiftField (N := N) u)
    (P : Measure (SpinField N)) (P : Measure (SpinField N))

private theorem invariant_of_integrals {N : ℕ} (P : ProbabilityMeasure (SpinField N))
    (h : ∀ u, ∀ F : C(SpinField N, ℝ),
      (∫ s, F (shiftField u s) ∂(P : Measure _)) = ∫ s, F s ∂(P : Measure _)) :
    ShiftInvariant P := by
  intro u
  refine ⟨(shiftField u).continuous.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (shiftField u).continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact h u F.toContinuousMap

theorem rootedLaw_invariant (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (hD : DisplacementAction D) (H : V → V → ℝ) :
    ShiftInvariant (rootedLaw N D H) := by
  apply invariant_of_integrals
  intro u F
  change (∫ s, (F.comp (shiftField u)) s ∂(rootedLaw N D H : Measure _)) = _
  rw [rootedLaw_integral, rootedLaw_integral]
  have hu (v : V) (s : V → Spin N) :
      shiftField u (liftAt D v s) = liftAt D (hD.shiftEquiv u v) s := by
    funext x
    change s (D (x+u) v) = s (D x (D u v))
    rw [hD.add]
  simp only [ContinuousMap.comp_apply, hu]
  rw [Equiv.sum_comp (hD.shiftEquiv u) (fun v => ∫ s, F (liftAt D v s) ∂(sphereGibbs N H : Measure _))]

theorem ShiftInvariant.of_tendsto {N : ℕ} {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (hQ : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n, ShiftInvariant (P n)) : ShiftInvariant Q := by
  apply invariant_of_integrals
  intro u F
  have he (n : ℕ) : (∫ s, F (shiftField u s) ∂(P n : Measure _)) =
      ∫ s, F s ∂(P n : Measure _) := by
    rw [← integral_map (hP n u).measurable.aemeasurable F.continuous.aestronglyMeasurable,
        (hP n u).map_eq]
  have h1 := (ProbabilityMeasure.continuous_integral_continuousMap
    (F.comp (shiftField u))).continuousAt.tendsto.comp hQ
  have h2 := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hQ
  exact tendsto_nhds_unique h1 (h2.congr' (Filter.Eventually.of_forall fun n => (he n).symm))

theorem periodic_spin_limit (N : ℕ) [NeZero N] (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, Nonempty (V n)] (D : ∀ n, Site → V n → V n) (hD : ∀ n, DisplacementAction (D n))
    (H : ∀ n, V n → V n → ℝ) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant Q ∧
      Tendsto (fun j => rootedLaw N (D (l j)) (H (l j))) atTop (𝓝 Q) ∧
      ∀ z, Tendsto (fun j => averagedDot N (D (l j)) (H (l j)) z) atTop (𝓝 (fieldPair Q z)) := by
  obtain ⟨Q,l,hl,hQ,hF⟩ := spinField_subsequence N (fun n => rootedLaw N (D n) (H n))
  refine ⟨Q,l,hl,ShiftInvariant.of_tendsto hQ (fun j => rootedLaw_invariant N _ (hD (l j)) _),
    hQ, ?_⟩
  intro z
  exact (hF (fieldDot N 0 z)).congr' (Eventually.of_forall fun j =>
    fieldPair_rootedLaw N (D (l j)) (hD (l j)).zero (H (l j)) z)

theorem cubic_spin_limit (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : ℕ → Site → ℝ) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant Q ∧
      Tendsto (fun j => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides (l j)) (J (l j))))
        atTop (𝓝 Q) ∧
      ∀ z, Tendsto (fun j => cubicPair N (sides (l j)) (J (l j)) z) atTop (𝓝 (fieldPair Q z)) :=
  periodic_spin_limit N (fun n => Seam.Cell (sides n)) (fun _ => Seam.baseMove)
    (fun n => Seam.cubic_displacement_action (sides n)) (fun n => Seam.ordinarySeries (sides n) (J n))

theorem diagonal_spin_limit (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : ℕ → Site → ℝ) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant Q ∧
      Tendsto (fun j => rootedLaw N Seam.adaptedDestination
        (Seam.adaptedSeries (sides (l j)) (J (l j)))) atTop (𝓝 Q) ∧
      ∀ z, Tendsto (fun j => diagonalPair N (sides (l j)) (J (l j)) z) atTop (𝓝 (fieldPair Q z)) :=
  periodic_spin_limit N (fun n => Seam.Site (sides n)) (fun _ => Seam.adaptedDestination)
    (fun n => Seam.adapted_displacement_action (sides n)) (fun n => Seam.adaptedSeries (sides n) (J n))

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.fieldPair_rootedLaw
#print axioms IsingScaling.Rotor.PressureSelection.spinField_subsequence
#print axioms IsingScaling.Rotor.PressureSelection.cubic_spin_limit
#print axioms IsingScaling.Rotor.PressureSelection.diagonal_spin_limit
