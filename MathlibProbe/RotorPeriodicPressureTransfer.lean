import MathlibProbe.RotorPhysicalSiteReflection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Two finite Gibbs pressures for the periodic rotor selection

The unperturbed cubic tori and the varied diagonal-adapted tori may have
different finite vertex sets. A common limiting pressure at each of the
two interactions compares their limiting pair-energy responses. The
proof integrates the tangent-line inequality for the exponential on the
actual normalized product sphere measure. Both directed copies of each
bond occur with the factor one half.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped InnerProductSpace Topology

namespace IsingScaling.Rotor.PressureSelection

section Integral

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

private def Z (h : X → ℝ) := ∫ s, Real.exp (h s) ∂μ
private def mean (h f : X → ℝ) := (∫ s, Real.exp (h s) * f s ∂μ) / Z μ h

private lemma integrable_cont {u : X → ℝ} (hu : Continuous u) : Integrable u μ :=
  hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem lower_log_ratio {h k : X → ℝ} (hh : Continuous h) (hk : Continuous k) :
    mean μ h (fun s => k s - h s) ≤ Real.log (Z μ k) - Real.log (Z μ h) := by
  let a := Real.log (Z μ k) - Real.log (Z μ h)
  have hz : 0 < Z μ h := integral_exp_pos (integrable_cont μ hh.rexp)
  have hw : 0 < Z μ k := integral_exp_pos (integrable_cont μ hk.rexp)
  have hs : Real.exp (-a) * Z μ k = Z μ h := by
    dsimp [a]
    rw [neg_sub, Real.exp_sub, Real.exp_log hz, Real.exp_log hw]
    field_simp
  have hpoint (s : X) :
      Real.exp (h s) * (k s - h s) - a * Real.exp (h s) + Real.exp (h s) ≤
        Real.exp (-a) * Real.exp (k s) := by
    calc
      _ = Real.exp (h s) * (k s - h s - a + 1) := by ring
      _ ≤ Real.exp (h s) * Real.exp (k s - h s - a) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = Real.exp (-a) * Real.exp (k s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hdiff := integrable_cont μ (hh.rexp.mul (hk.sub hh))
  have hleft := (hdiff.sub ((integrable_cont μ hh.rexp).const_mul a)).add (integrable_cont μ hh.rexp)
  have hi := integral_mono hleft ((integrable_cont μ hk.rexp).const_mul (Real.exp (-a))) hpoint
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hi
  rw [integral_add (f := fun x => Real.exp (h x) * (k x - h x) - a * Real.exp (h x))
      (g := fun x => Real.exp (h x))
      (hdiff.sub ((integrable_cont μ hh.rexp).const_mul a)) (integrable_cont μ hh.rexp),
    integral_sub (f := fun x => Real.exp (h x) * (k x - h x)) (g := fun x => a * Real.exp (h x))
      hdiff ((integrable_cont μ hh.rexp).const_mul a)] at hi
  simp only [integral_const_mul] at hi
  change _ - a * Z μ h + Z μ h ≤ Real.exp (-a) * Z μ k at hi
  rw [hs] at hi
  change _ / Z μ h ≤ a
  apply (div_le_iff₀ hz).2
  linarith

private theorem upper_log_ratio {h k : X → ℝ} (hh : Continuous h) (hk : Continuous k) :
    Real.log (Z μ k) - Real.log (Z μ h) ≤ mean μ k (fun s => k s - h s) := by
  have H := lower_log_ratio μ hk hh
  have e : mean μ k (fun s => h s-k s) = -mean μ k (fun s => k s-h s) := by
    unfold mean
    rw [← neg_div, ← integral_neg]
    apply congrArg (fun a : ℝ => a / Z μ k)
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by ring
  rw [e] at H
  linarith

private theorem upper_log_shift {h k : X → ℝ} (hh : Continuous h) (hk : Continuous k)
    (d : ℝ) (he : ∀ s, k s ≤ h s + d) :
    Real.log (Z μ k) ≤ Real.log (Z μ h) + d := by
  have hz : 0 < Z μ h := integral_exp_pos (integrable_cont μ hh.rexp)
  have hw : 0 < Z μ k := integral_exp_pos (integrable_cont μ hk.rexp)
  apply (Real.log_le_iff_le_exp hw).2
  rw [Real.exp_add, Real.exp_log hz]
  calc
    Z μ k ≤ ∫ s, Real.exp (h s) * Real.exp d ∂μ := by
      apply integral_mono (integrable_cont μ hk.rexp) ((integrable_cont μ hh.rexp).mul_const _)
      intro s
      change Real.exp (k s) ≤ Real.exp (h s) * Real.exp d
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (he s)
    _ = Z μ h * Real.exp d := integral_mul_const _ _

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
private theorem mean_const_mul (h f : X → ℝ) (c : ℝ) :
    mean μ h (fun x => c * f x) = c * mean μ h f := by
  unfold mean
  simp only [mul_left_comm (Real.exp _) c, integral_const_mul, mul_div_assoc]

private theorem mean_sum {ι : Type*} [Fintype ι] {h : X → ℝ} (hh : Continuous h)
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) :
    mean μ h (fun x => ∑ i, f i x) = ∑ i, mean μ h (f i) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum (f := fun i x => Real.exp (h x) * f i x) univ
    (fun i _ => integrable_cont μ (hh.rexp.mul (hf i))), Finset.sum_div]

end Integral

/-- The sites of either finite torus can be enumerated by a finite type.
The kernel may contain periodized long-range auxiliary bonds. -/
def energy {N : ℕ} {V : Type*} [Fintype V] (J : V → V → ℝ) (s : V → Spin N) : ℝ :=
  (∑ v, ∑ w, J v w * ⟪(s v).val, (s w).val⟫_ℝ) / 2

private lemma energy_cont {N : ℕ} {V : Type*} [Fintype V] (J : V → V → ℝ) :
    Continuous (energy (N := N) J) := by
  unfold energy
  exact (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
    continuous_const.mul (by fun_prop)))).div_const _

private abbrev prior (N : ℕ) [NeZero N] (V : Type*) [Fintype V] :=
  Measure.pi (fun _ : V => SiteReflection.surfacePrior N)

/-- Log partition function per site of the finite zero-field sphere model. -/
def pressure (N : ℕ) [NeZero N] {V : Type*} [Fintype V] (J : V → V → ℝ) : ℝ :=
  Real.log (Z (prior N V) (energy J)) / Fintype.card V

/-- The perturbed minus base pair energy, read under the law at H. -/
def response (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (H J K : V → V → ℝ) : ℝ :=
  mean (prior N V) (energy H) (fun s => energy K s - energy J s) / Fintype.card V

/-- Dot pair of the actual, potentially long-range, finite sphere Gibbs law. -/
def dotPair (N : ℕ) [NeZero N] {V : Type*} [Fintype V] (H : V → V → ℝ) (v w : V) : ℝ :=
  mean (prior N V) (energy H) (fun s => ⟪(s v).val,(s w).val⟫_ℝ)

theorem abs_dotPair_le_one (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (H : V → V → ℝ) (v w : V) : |dotPair N H v w| ≤ 1 := by
  let μ := prior N V
  let W (s : V → Spin N) := Real.exp (energy H s)
  have hW : Continuous W := (energy_cont H).rexp
  have hG : Continuous (fun s : V → Spin N => W s * ⟪(s v).val,(s w).val⟫_ℝ) :=
    hW.mul (by fun_prop)
  have hz : 0 < Z μ (energy H) := integral_exp_pos (integrable_cont μ hW)
  unfold dotPair mean
  rw [abs_div, abs_of_pos hz, div_le_one hz]
  calc
    _ ≤ ∫ s : V → Spin N, ‖W s * ⟪(s v).val,(s w).val⟫_ℝ‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono (integrable_cont μ hG).norm (integrable_cont μ hW)
      intro s
      change ‖W s * ⟪(s v).val,(s w).val⟫_ℝ‖ ≤ W s
      rw [norm_mul, Real.norm_eq_abs (W s), abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (Real.exp_pos _).le
      simpa [norm_eq_of_mem_sphere (s v), norm_eq_of_mem_sphere (s w)] using
        (norm_inner_le_norm (𝕜 := ℝ) (s v).val (s w).val)

theorem response_eq_dotPair (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (H J K : V → V → ℝ) :
    response N H J K = (∑ v, ∑ w, (K v w-J v w) * dotPair N H v w) / 2 / Fintype.card V := by
  classical
  let F (v w : V) (s : V → Spin N) := (K v w-J v w) * ⟪(s v).val,(s w).val⟫_ℝ
  have hc (v w : V) : Continuous (F v w) := by unfold F; fun_prop
  have he : (fun s : V → Spin N => energy K s - energy J s) =
      fun s => (1/2 : ℝ) * ∑ v, ∑ w, F v w s := by
    funext s
    simp only [energy, F, ← sub_div, ← Finset.sum_sub_distrib, ← sub_mul]
    ring
  rw [response, he, mean_const_mul, mean_sum _ (energy_cont H)
    (fun v s => ∑ w, F v w s) (fun v => continuous_finsetSum _ (fun w _ => hc v w))]
  simp_rw [mean_sum _ (energy_cont H) (F _) (hc _)]
  simp only [F, mean_const_mul, dotPair]
  ring

/-- The disjoint union of two identical finite volumes. -/
def twoCopies {V : Type*} (J : V → V → ℝ) : V ⊕ V → V ⊕ V → ℝ
  | .inl i, .inl j | .inr i, .inr j => J i j
  | _, _ => 0

private lemma energy_twoCopies {N : ℕ} {V : Type*} [Fintype V]
    (J : V → V → ℝ) (f g : V → Spin N) :
    energy (twoCopies J) (Sum.elim f g) = energy J f + energy J g := by
  simp [energy, Fintype.sum_sum_type, twoCopies, add_div]

theorem pressure_twoCopies (N : ℕ) [NeZero N] {V : Type*} [Fintype V] (J : V → V → ℝ) :
    pressure N (twoCopies J) = pressure N J := by
  let E := MeasurableEquiv.sumPiEquivProdPi (fun _ : V ⊕ V => Spin N)
  have h := measurePreserving_sumPiEquivProdPi_symm (fun _ : V ⊕ V => SiteReflection.surfacePrior N)
  have hZ : Z (prior N (V ⊕ V)) (energy (twoCopies J)) =
      Z (prior N V) (energy J) * Z (prior N V) (energy J) := by
    calc
      _ = ∫ s : (V → Spin N) × (V → Spin N), Real.exp (energy (twoCopies J) (E.symm s))
            ∂(prior N V).prod (prior N V) := (h.integral_comp' _).symm
      _ = ∫ s : (V → Spin N) × (V → Spin N),
          Real.exp (energy J s.1) * Real.exp (energy J s.2) ∂(prior N V).prod (prior N V) := by
        apply integral_congr_ae
        refine Eventually.of_forall fun s => ?_
        change Real.exp (energy (twoCopies J) (Sum.elim s.1 s.2)) = _
        rw [energy_twoCopies, Real.exp_add]
      _ = _ := by
        simpa only [Z] using (integral_prod_mul (μ := prior N V) (ν := prior N V)
          (fun s : V → Spin N => Real.exp (energy J s)) (fun s : V → Spin N => Real.exp (energy J s)))
  have hz : 0 < Z (prior N V) (energy J) := integral_exp_pos (integrable_cont _ (energy_cont J).rexp)
  unfold pressure
  rw [hZ, Real.log_mul hz.ne' hz.ne', Fintype.card_sum, Nat.cast_add]
  by_cases hc : (Fintype.card V : ℝ) = 0
  · simp [hc]
  · have hd : (Fintype.card V:ℝ) + (Fintype.card V:ℝ) ≠ 0 := by positivity
    field_simp [hc, hd]

theorem finite_pressure_sandwich (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (J K : V → V → ℝ) :
    response N J J K ≤ pressure N K - pressure N J ∧
      pressure N K - pressure N J ≤ response N K J K := by
  unfold response pressure
  rw [← sub_div]
  exact ⟨div_le_div_of_nonneg_right (lower_log_ratio _ (energy_cont J) (energy_cont K)) (by positivity),
    div_le_div_of_nonneg_right (upper_log_ratio _ (energy_cont J) (energy_cont K)) (by positivity)⟩

/-- A bound valid at every spin configuration controls both directions of
the per-site log partition function comparison. -/
theorem pressure_distance (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (J K : V → V → ℝ) (d : ℝ)
    (hb : ∀ s : V → Spin N, |energy K s - energy J s| ≤ d) :
    |pressure N K - pressure N J| ≤ d / Fintype.card V := by
  have hf := upper_log_shift (prior N V) (energy_cont J) (energy_cont K) d
    (fun s => by linarith [(abs_le.mp (hb s)).2])
  have hr := upper_log_shift (prior N V) (energy_cont K) (energy_cont J) d
    (fun s => by linarith [(abs_le.mp (hb s)).1])
  unfold pressure
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card V : ℝ))]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)

theorem pressure_distance_by_coupling (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    (J K : V → V → ℝ) :
    |pressure N K - pressure N J| ≤ (∑ v, ∑ w, |K v w-J v w|) / 2 / Fintype.card V := by
  apply pressure_distance
  intro s
  have hb (v w : V) : |⟪(s v).val, (s w).val⟫_ℝ| ≤ 1 := by
    simpa [Real.norm_eq_abs, norm_eq_of_mem_sphere (s v), norm_eq_of_mem_sphere (s w)] using
      (norm_inner_le_norm (𝕜 := ℝ) (s v).val (s w).val)
  simp only [energy, ← sub_div, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    ← Finset.sum_sub_distrib, ← sub_mul]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hb v w)

/-- C and A may have unrelated sizes. The four thermodynamic pressure
limits are the geometric input; their common values cancel. The two
response limits refer to the original finite Gibbs integrals. -/
theorem compare_two_periodic_limits (N : ℕ) [NeZero N] (C A : ℕ → ℕ)
    (JC KC : (n : ℕ) → Fin (C n) → Fin (C n) → ℝ)
    (JA KA : (n : ℕ) → Fin (A n) → Fin (A n) → ℝ)
    {p q u v : ℝ}
    (hCJ : Tendsto (fun n => pressure N (JC n)) atTop (𝓝 p))
    (hCK : Tendsto (fun n => pressure N (KC n)) atTop (𝓝 q))
    (hAJ : Tendsto (fun n => pressure N (JA n)) atTop (𝓝 p))
    (hAK : Tendsto (fun n => pressure N (KA n)) atTop (𝓝 q))
    (hu : Tendsto (fun n => response N (JC n) (JC n) (KC n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => response N (KA n) (JA n) (KA n)) atTop (𝓝 v)) :
    u ≤ v :=
  (le_of_tendsto_of_tendsto' hu (hCK.sub hCJ) (fun n =>
    (finite_pressure_sandwich N (JC n) (KC n)).1)).trans
    (le_of_tendsto_of_tendsto' (hAK.sub hAJ) hv (fun n =>
      (finite_pressure_sandwich N (JA n) (KA n)).2))

/-- Matching only the two shape-dependent pressure *increments* is enough.
The individual pressures and increments are allowed to oscillate. -/
theorem compare_two_shapes_of_pressure_defect (N : ℕ) [NeZero N] (C A : ℕ → ℕ)
    (JC KC : (n : ℕ) → Fin (C n) → Fin (C n) → ℝ)
    (JA KA : (n : ℕ) → Fin (A n) → Fin (A n) → ℝ) {u v : ℝ}
    (hgap : Tendsto (fun n => (pressure N (KC n) - pressure N (JC n)) -
      (pressure N (KA n) - pressure N (JA n))) atTop (𝓝 0))
    (hu : Tendsto (fun n => response N (JC n) (JC n) (KC n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => response N (KA n) (JA n) (KA n)) atTop (𝓝 v)) :
    u ≤ v := by
  have h := le_of_tendsto_of_tendsto' hu (hgap.add hv) (fun i => by
    change response N (JC i) (JC i) (KC i) ≤ _ - _ + _
    linarith [(finite_pressure_sandwich N (JC i) (KC i)).1,
      (finite_pressure_sandwich N (JA i) (KA i)).2])
  simpa using h

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.finite_pressure_sandwich
#print axioms IsingScaling.Rotor.PressureSelection.response_eq_dotPair
#print axioms IsingScaling.Rotor.PressureSelection.pressure_twoCopies
#print axioms IsingScaling.Rotor.PressureSelection.compare_two_periodic_limits
#print axioms IsingScaling.Rotor.PressureSelection.pressure_distance_by_coupling
#print axioms IsingScaling.Rotor.PressureSelection.compare_two_shapes_of_pressure_defect
