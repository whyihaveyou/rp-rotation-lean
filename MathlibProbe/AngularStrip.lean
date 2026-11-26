import MathlibProbe.AngularEntire
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! Gluing the axis and diagonal continuations of AS-6. The two chart
families are interlaced: consecutive left endpoints are π/4 apart, and
each chart has width π/2. -/

open Set Complex Function Filter
open scoped Topology Real

namespace IsingRotation

/-- Vertical strip of an axis (even index) or a diagonal (odd index). -/
def angularStrip (n : ℤ) : Set ℂ :=
  {z | (n : ℝ) * (π / 4) < z.re ∧ z.re < ((n : ℝ) + 2) * (π / 4)}

private lemma strip_open (n : ℤ) : IsOpen (angularStrip n) :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

private lemma strip_convex (n : ℤ) : Convex ℝ (angularStrip n) :=
  (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)

lemma angularStrip_cover (z : ℂ) : ∃ n : ℤ, z ∈ angularStrip n := by
  let w := Real.pi / 4
  have hw : 0 < w := by dsimp [w]; positivity
  let a := z.re / w
  refine ⟨⌊a + 1/2⌋ - 1, ?_⟩
  change _ * w < z.re ∧ z.re < (_ + 2) * w
  push_cast
  rw [← lt_div_iff₀ hw, ← div_lt_iff₀ hw]
  change _ < a ∧ a < _
  constructor <;> linarith [Int.floor_le (a+1/2), Int.lt_floor_add_one (a+1/2)]

private lemma frequently_agree_real {f g : ℂ → ℂ} {x : ℝ}
    (h : ∀ᶠ t : ℝ in 𝓝 x, f (t : ℂ) = g t) :
    ∃ᶠ z in 𝓝[≠] (x : ℂ), f z = g z := by
  have hc : Tendsto Complex.ofReal (𝓝[≠] x) (𝓝[≠] (x : ℂ)) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ _ => by simp_all
  exact hc.frequently ((h.filter_mono nhdsWithin_le_nhds).frequently)

private lemma strip_compatible (H : ℤ → ℂ → ℂ) (h : ℝ → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (H i) (angularStrip i))
    (hr : ∀ i (x : ℝ), (x : ℂ) ∈ angularStrip i → H i x = h x)
    {i j : ℤ} {z : ℂ} (hi : z ∈ angularStrip i) (hj : z ∈ angularStrip j) :
    H i z = H j z := by
  let S := angularStrip i ∩ angularStrip j
  have hS : IsOpen S := (strip_open i).inter (strip_open j)
  have hpc : IsPreconnected S := ((strip_convex i).inter (strip_convex j)).isPreconnected
  have hx : (z.re : ℂ) ∈ S := ⟨hi, hj⟩
  have hf : AnalyticOnNhd ℂ (H i) S := ((hd i).mono inter_subset_left).analyticOnNhd hS
  have hg : AnalyticOnNhd ℂ (H j) S := ((hd j).mono inter_subset_right).analyticOnNhd hS
  apply hf.eqOn_of_preconnected_of_frequently_eq hg hpc hx _ (show z ∈ S from ⟨hi,hj⟩)
  apply frequently_agree_real
  have hnear := continuous_ofReal.continuousAt (hS.mem_nhds hx)
  filter_upwards [hnear] with x hxs
  exact (hr i x hxs.1).trans (hr j x hxs.2).symm

/-- Full gluing in AS-6, with the global period deduced from the real trace. -/
theorem glue_angularStrips (H : ℤ → ℂ → ℂ) (h : ℝ → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (H i) (angularStrip i))
    (hr : ∀ i (x : ℝ), (x : ℂ) ∈ angularStrip i → H i x = h x)
    (hp : Periodic h (π / 2)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Periodic F ((π / 2 : ℝ) : ℂ) ∧
      (∀ i, EqOn F (H i) (angularStrip i)) ∧ (∀ x : ℝ, F x = h x) := by
  classical
  choose index hindex using angularStrip_cover
  let F (z : ℂ) := H (index z) z
  have heq (i) : EqOn F (H i) (angularStrip i) := fun z hz =>
    strip_compatible H h hd hr (hindex z) hz
  have dF : Differentiable ℂ F := by
    intro z
    let i := index z
    have hn := (strip_open i).mem_nhds (hindex z)
    exact ((hd i).differentiableAt hn).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hn (heq i))
  have rF (x : ℝ) : F x = h x := hr _ x (hindex _)
  refine ⟨F, dF, ?_, heq, rF⟩
  have ds : Differentiable ℂ (fun z : ℂ => F (z + ((π / 2 : ℝ) : ℂ))) :=
    dF.comp (differentiable_id.add_const _)
  have e : (fun z : ℂ => F (z + ((π / 2 : ℝ) : ℂ))) = F := by
    apply (ds.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
      (dF.differentiableOn.analyticOnNhd isOpen_univ)
      (z₀ := ((0 : ℝ) : ℂ))
    apply frequently_agree_real
    apply Eventually.of_forall
    intro x
    simp only [← ofReal_add, rF, hp x]
  exact fun x => congrFun e x

/-- A bound from a suitably chosen normal at each point suffices. -/
theorem angularStrip_constant (H : ℤ → ℂ → ℂ) (h : ℝ → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (H i) (angularStrip i))
    (hr : ∀ i (x : ℝ), (x : ℂ) ∈ angularStrip i → H i x = h x)
    (hp : Periodic h (π / 2)) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ z : ℂ, ∃ i, z ∈ angularStrip i ∧ ‖H i z‖ ≤ C * Real.exp (2 * |z.im|))
    (x y : ℝ) : h x = h y := by
  obtain ⟨F,dF,pF,eF,rF⟩ := glue_angularStrips H h hd hr hp
  have bF (z : ℂ) : ‖F z‖ ≤ C * Real.exp (2 * |z.im|) := by
    obtain ⟨i,hi,hb⟩ := hg z
    simpa only [eF i hi] using hb
  rw [← rF x, ← rF y]
  exact angularEntire_constant F dF pF C hC bF _ _

end IsingRotation
