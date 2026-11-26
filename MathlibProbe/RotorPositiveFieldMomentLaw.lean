import MathlibProbe.RotorDotPositiveFieldContinuation
import MathlibProbe.RotorHeisenbergFreeCubeDLR

/-!
# Positive-field continuation of the whole free Heisenberg spin law

Use the actual finite-cube correlation of each fixed spin-coordinate monomial.
On a real large-field interval the local Gibbs specification already selects one
state. Holomorphic continuation compares scaled volumes and lattice translates
for each individual monomial. Stone–Weierstrass determination by these moments
identifies every accumulation point of the prescribed free Gibbs distributions.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace IsingScaling.Rotor.HeisenbergField.PositiveFieldLaw
open ComplexPartition PressureSelection PressureSelection.LocalGibbs PositiveFieldContinuation

/-- Ratio for the specified continuous observable under the actual free-cube
spin integral. At real longitudinal field its value is the Gibbs expectation. -/
def cubeRatio (β : ℝ) (F : C(SpinField 3,ℝ)) (n : ℕ) (z : ℂ) : ℂ :=
  marked (cubeCoupling n β) (uniform z) (complexMark (F.comp (extendCube n))) /
    partition (cubeCoupling n β) (uniform z)

theorem cubeRatio_real (β h : ℝ) (F : C(SpinField 3,ℝ)) (n : ℕ) :
    cubeRatio β F n (h : ℂ) = Complex.ofReal (∫ s, F s ∂(cubeLaw β h n : Measure _)) :=
  (cubeLaw_eq_complex_moment n β h F).symm

private theorem cubeRatio_holo {β : ℝ} (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (F : C(SpinField 3,ℝ)) (n : ℕ) : DifferentiableOn ℂ (cubeRatio β F n) rightHalfPlane :=
  (entire_marked_uniform _ _).differentiableOn.div (entire_partition_uniform _).differentiableOn
    (C.nonzero n)

/-- The sites and coordinate powers are fixed before the volume varies.
Finitely many initial cubes may be omitted for each moment and compact set. -/
def CubeMomentBounds (β : ℝ) : Prop :=
  ∀ (d : MomentDegree) (K : Set ℂ), IsCompact K → K ⊆ rightHalfPlane →
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, ‖cubeRatio β (spinMoment d) n z‖ ≤ M

private def shiftIndex (u : Site) : (Site × Fin 3) ↪ (Site × Fin 3) where
  toFun i := (i.1+u,i.2)
  inj' := by
    intro ⟨i,k⟩ ⟨j,l⟩ h
    obtain ⟨hij,hkl⟩ := Prod.mk.inj h
    exact Prod.ext (add_right_cancel hij) hkl

/-- A translated monomial is another member of the same family of tests. -/
theorem shift_moment (u : Site) (d : MomentDegree) :
    ∃ e : MomentDegree, (spinMoment d).comp (shiftField u) = spinMoment e := by
  refine ⟨d.embDomain (shiftIndex u),?_⟩
  ext s
  simp only [ContinuousMap.comp_apply,spinMoment_apply,Finsupp.support_embDomain,Finset.prod_map,
    Finsupp.embDomain_apply_self]
  rfl

private theorem bound_all {β : ℝ} (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (hb : CubeMomentBounds β) (d : MomentDegree) (K : Set ℂ) (hk : IsCompact K) (hs : K ⊆ rightHalfPlane) :
    ∃ M : ℝ, ∀ n z, z ∈ K → ‖cubeRatio β (spinMoment d) n z‖ ≤ M := by
  obtain ⟨m,hm⟩ := hb d K hk hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp hm
  choose b h using fun n => hk.exists_bound_of_continuousOn
    ((cubeRatio_holo C (spinMoment d) n).continuousOn.mono hs)
  let B := ∑ i ∈ Finset.range N, max (b i) 0
  refine ⟨max m B, fun n z hz => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn z hz).trans (le_max_left _ _)
  · have hi : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hw : max (b n) 0 ≤ B := Finset.single_le_sum (fun i _ => le_max_right (b i) 0) hi
    exact ((h n z hz).trans (le_max_left _ _)).trans (hw.trans (le_max_right _ _))

private theorem interval {β : ℝ} (hβ : 0 ≤ β) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, a < t → ScalarThermodynamicLimit β t := by
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp (LargeField.scalar_thermodynamic_limit_eventually hβ)
  refine ⟨max t₀ 0 + 1, by linarith [le_max_right t₀ 0], fun t ht => ht₀ t ?_⟩
  linarith [le_max_left t₀ 0]

/-- Every moment of the original free cubes converges, and their full
moment family is stationary in the thermodynamic limit. -/
theorem scalar_limit_of_compact_moment_bounds {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    (hb : CubeMomentBounds β) {h : ℝ} (hh : 0 < h) : ScalarThermodynamicLimit β h := by
  obtain ⟨a,ha,H⟩ := interval hβ
  have hab : a < a+1 := by linarith
  refine ⟨?_,?_,(freeDotComparison_of_complex_control hβ C D hh).rectangle⟩
  · intro d
    let F := spinMoment d
    have high (t : ℝ) (hat : a < t) (_ : t < a+1) :
        ∃ b : ℂ, Tendsto (fun n => cubeRatio β F n (t : ℂ)) atTop (𝓝 b) := by
      obtain ⟨b,hb'⟩ := (H t hat).moments d
      refine ⟨(b : ℂ), ?_⟩
      simp only [F,cubeRatio_real]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hb'
    obtain ⟨l,hl⟩ := RotorVitali.rightHalfPlane_vitali_limit_exists ha hab
      (cubeRatio_holo C F) (bound_all C hb d) high hh
    refine ⟨l.re,?_⟩
    simp only [cubeRatio_real] at hl
    simpa [F,Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hl
  · intro u d
    obtain ⟨e,he⟩ := shift_moment u d
    have heval (s : SpinField 3) : spinMoment e s = spinMoment d (shiftField u s) :=
      congrArg (fun f : C(SpinField 3,ℝ) => f s) he.symm
    have high (t : ℝ) (hat : a < t) (_ : t < a+1) :
        Tendsto (fun n => cubeRatio β (spinMoment e) n (t : ℂ) -
          cubeRatio β (spinMoment d) n (t : ℂ)) atTop (𝓝 0) := by
      simp only [cubeRatio_real,heval,← Complex.ofReal_sub]
      simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp ((H t hat).translates u d)
    have hl := RotorVitali.rightHalfPlane_vitali_compare ha hab
      (cubeRatio_holo C (spinMoment e)) (cubeRatio_holo C (spinMoment d))
      (bound_all C hb e) (bound_all C hb d) high hh
    simp only [cubeRatio_real,heval,← Complex.ofReal_sub] at hl
    simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hl

/-- Finite physical compact bounds imply the positive-field thermodynamic
input for the entire original free-spin probability law. -/
theorem positiveFieldThermodynamicInput_of_compact_moment_bounds {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    (hb : CubeMomentBounds β) : PositiveFieldThermodynamicInput β :=
  fun _ hh => (scalar_limit_of_compact_moment_bounds hβ C D hb hh).exists_commonFreeLimit

/-- The same uniquely selected free limit satisfies the physical field
specification, is stationary, and gives the free-rectangle pair readout. -/
theorem existsUnique_gibbs_common_free_limit {β : ℝ} (hβ : 0 ≤ β)
    (C : FreeDotControl BoxSite (fun n => cubeCoupling n β))
    (D : FreeDotControl BondMirror.V (fun n => rectangleCoupling n β))
    (hb : CubeMomentBounds β) {h : ℝ} (hh : 0 < h) :
    ∃! P : ProbabilityMeasure (SpinField 3), IsFieldGibbs β h P ∧ CommonFreeLimit β h P := by
  obtain ⟨P,hP⟩ := positiveFieldThermodynamicInput_of_compact_moment_bounds hβ C D hb h hh
  exact ⟨P, ⟨field_gibbs_of_free_cube_limit (L := id) tendsto_id hP.centered,hP⟩,
    fun Q hQ => hQ.2.unique hP⟩

end IsingScaling.Rotor.HeisenbergField.PositiveFieldLaw
