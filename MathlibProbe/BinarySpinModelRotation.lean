import MathlibProbe.PottsPhysicalSiteReflection
import MathlibProbe.IsingTangentExistence
import MathlibProbe.RotorSphereSign
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
Two colours form the two vertices of the one-dimensional unit simplex.
Their scalar product is the product of their signs. The equal-colour bond
observable is one half of one plus this product. The resulting constant
β/2 per undirected edge cancels in the ratio defining the finite Gibbs
expectation. Passing to the free thermodynamic limit preserves the
identity at β_Ising = β_Potts/2 and hence preserves the cube-normalized
pair measure at every scale.
-/
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology BigOperators CompactlySupported
namespace IsingScaling.BinarySpin
open Potts.SiteBox

private def colourConfig (L : ℕ) : Config 2 L ≃ IsingScaling.Spin L :=
  (Equiv.refl (BoxSite L)).arrowCongr finTwoEquiv

private theorem simplex_sign (a b : Fin 2) :
    simplex a b = value (finTwoEquiv a) * value (finTwoEquiv b) := by
  fin_cases a <;> fin_cases b <;> norm_num [simplex, equalColour, finTwoEquiv, value]

private theorem indicator_sign (a b : Fin 2) :
    2 * equalColour a b = 1 + value (finTwoEquiv a) * value (finTwoEquiv b) := by
  fin_cases a <;> fin_cases b <;> norm_num [equalColour, finTwoEquiv, value]

/-- Number of oriented nearest-neighbour bonds in the actual free cube. -/
def directedEdgeCount (L : ℕ) : ℝ :=
  ∑ x : BoxSite L, ∑ y : BoxSite L, if latticeDistance x y = 1 then 1 else 0

theorem potts_weight {L : ℕ} (β : ℝ) (σ : Config 2 L) :
    weight equalColour β σ = Real.exp (β * directedEdgeCount L / 4) *
      gibbsWeight (β / 2) L (colourConfig L σ) := by
  let A (x y : BoxSite L) : ℝ := if latticeDistance x y = 1 then 1 else 0
  let B (x y : BoxSite L) : ℝ := if latticeDistance x y = 1 then
    value ((colourConfig L σ) x) * value ((colourConfig L σ) y) else 0
  have h (x y : BoxSite L) :
      2 * bondTerm equalColour σ x y = A x y + B x y := by
    by_cases he : latticeDistance x y = 1
    · simp only [bondTerm, A, B, he, ite_true]
      exact indicator_sign (σ x) (σ y)
    · simp [bondTerm, A, B, he]
  have hsum : 2 * (∑ x, ∑ y, bondTerm equalColour σ x y) =
      (∑ x, ∑ y, A x y) + ∑ x, ∑ y, B x y := by
    simp only [Finset.mul_sum, h, Finset.sum_add_distrib]
  rw [weight, gibbsWeight, ← Real.exp_add]
  apply congrArg Real.exp
  change β * ((∑ x, ∑ y, bondTerm equalColour σ x y) / 2) =
    β * (∑ x, ∑ y, A x y) / 4 + β / 2 * ((∑ x, ∑ y, B x y) / 2)
  linear_combination (β / 4) * hsum

theorem potts_box_pair {L : ℕ} (β : ℝ) (x y : BoxSite L) :
    boxPair 2 β x y = IsingScaling.boxCorrelation (β / 2) L x y := by
  classical
  let E := colourConfig L
  let c := Real.exp (β * directedEdgeCount L / 4)
  let W := gibbsWeight (β / 2) L
  let F (τ : IsingScaling.Spin L) := W τ * value (τ x) * value (τ y)
  have hw (σ : Config 2 L) : weight equalColour β σ = c * W (E σ) :=
    potts_weight β σ
  have hf (σ : Config 2 L) :
      weight equalColour β σ * simplex (σ x) (σ y) = c * F (E σ) := by
    rw [hw, simplex_sign]
    change _ = c * (W (E σ) * value (finTwoEquiv (σ x)) * value (finTwoEquiv (σ y)))
    ring
  have hnum : (∑ σ : Config 2 L,
      weight equalColour β σ * simplex (σ x) (σ y)) = c * ∑ τ, F τ := by
    calc
      _ = ∑ σ : Config 2 L, c * F (E σ) := Finset.sum_congr rfl fun σ _ => hf σ
      _ = c * (∑ σ : Config 2 L, F (E σ)) := (Finset.mul_sum ..).symm
      _ = c * ∑ τ, F τ := congrArg (c * ·) (Equiv.sum_comp E F)
  have hden : (∑ σ : Config 2 L, weight equalColour β σ) = c * ∑ τ, W τ := by
    calc
      _ = ∑ σ : Config 2 L, c * W (E σ) := Finset.sum_congr rfl fun σ _ => hw σ
      _ = c * (∑ σ : Config 2 L, W (E σ)) := (Finset.mul_sum ..).symm
      _ = c * ∑ τ, W τ := congrArg (c * ·) (Equiv.sum_comp E W)
  have hc : c ≠ 0 := Real.exp_ne_zero _
  unfold boxPair IsingScaling.boxCorrelation
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hc


theorem potts_lattice_pair (β : ℝ) (L : ℕ) (x y : Site) :
    latticePair 2 β L x y = IsingScaling.freePair (β/2) L x y := by
  by_cases hx : x ∈ cube L
  · by_cases hy : y ∈ cube L
    · rw [latticePair, dite_eq_left hx, dite_eq_left hy, potts_box_pair, boxCorrelation_eq_freePair]
    · simp [latticePair, hx, hy, IsingScaling.freePair, occupation]
  · simp [latticePair, hx, IsingScaling.freePair, occupation]

/-- The kernel defined directly from the unit-simplex two-point function. -/
def pottsThermodynamic (β : ℝ) (z : Site) : ℝ := ⨆ L : ℕ, latticePair 2 β L 0 z

theorem potts_thermodynamic_eq (β : ℝ) :
    pottsThermodynamic β = thermodynamicTwoPoint (β/2) := by
  funext z
  simp only [pottsThermodynamic, thermodynamicTwoPoint, potts_lattice_pair, freePair_origin]

theorem potts_thermodynamic_limit {β : ℝ} (hβ : 0 ≤ β) (x y : Site) :
    Tendsto (fun L : ℕ => latticePair 2 β L x y) atTop (𝓝 (pottsThermodynamic β (x-y))) := by
  simpa only [potts_lattice_pair, potts_thermodynamic_eq] using
    thermodynamicTwoPoint_stationary (show 0 ≤ β/2 by positivity) x y

theorem potts_packet_spectrum {β : ℝ} (hβ : 0 ≤ β)
    (d : PacketNormal) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
      evenPacket c (fun m i j => pottsThermodynamic β
        (signedPerm p s (d.displacement m (x i-x j) (y i-y j)))) n := by
  rw [potts_thermodynamic_eq]
  exact thermodynamic_packet_spectrum (by positivity) d p s c x y

theorem potts_tangent_rotation {β : ℝ} (hβ : 0 ≤ β) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (hlim : ∀ f : C_c(Space, ℝ), Tendsto
      (fun j => ∫ x, f x ∂twoPointMeasure (pottsThermodynamic β) (R j))
      atTop (𝓝 (∫ x, f x ∂μ))) (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ := by
  have hb : 0 ≤ β/2 := by positivity
  have hg := thermodynamicTwoPoint_isLimit hb
  obtain ⟨hn, hχ⟩ := hg.positive_cube_mass hb
  have ht : IsTwoPointTangent (β/2) μ :=
    ⟨thermodynamicTwoPoint (β/2), R, hg, hn, fun j => hχ (R j), hR,
      by simpa only [potts_thermodynamic_eq] using hlim⟩
  exact ht.rotation_invariant hb O

/-- Every diverging scale sequence for the physical free kernel has a nonzero
orthogonally invariant tangent along a subsequence. -/
theorem potts_exists_invariant_tangent {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
      (∀ f : C_c(Space, ℝ), Tendsto (fun j => ∫ x, f x ∂twoPointMeasure
        (pottsThermodynamic β) (R (u j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧
      (∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ) := by
  rw [potts_thermodynamic_eq]
  exact exists_rotation_invariant_tangent (by positivity) hR

theorem potts_rotated_test_difference {β : ℝ} (hβ : 0 ≤ β)
    (f : C_c(Space, ℝ)) (O : Space ≃ₗᵢ[ℝ] Space) :
    Tendsto (fun r : ℕ => (∫ x, f (O x) ∂twoPointMeasure (pottsThermodynamic β) r) -
      (∫ x, f x ∂twoPointMeasure (pottsThermodynamic β) r)) atTop (𝓝 0) := by
  rw [potts_thermodynamic_eq]
  exact thermodynamicTwoPoint_rotated_test_difference (by positivity) f O

#print axioms potts_rotated_test_difference
#print axioms potts_lattice_pair
#print axioms potts_packet_spectrum
#print axioms potts_tangent_rotation
#print axioms potts_exists_invariant_tangent

end IsingScaling.BinarySpin
end

/-!
For the one-component rotor, the unit sphere has exactly two points.
Equip it with uniform probability. The dot product is the product of
the two signs. On a cube the a priori product measure puts the same mass
on every sign configuration, so the scalar Gibbs correlations agree
with the free Ising correlations at the same inverse temperature.
-/

noncomputable section
open Finset Filter MeasureTheory
open scoped Topology BigOperators CompactlySupported InnerProductSpace ENNReal
namespace IsingScaling.BinarySpin
open Rotor.SiteReflection

private def sphereSign (b : Bool) : Rotor.Spin 1 :=
  ⟨EuclideanSpace.single 0 (value b), by
    cases b <;> simp [value]⟩

private theorem sphereSign_apply (b : Bool) (i : Fin 1) :
    (sphereSign b).val i = value b := by
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi, sphereSign]

private theorem sphereSign_bijective : Function.Bijective sphereSign := by
  constructor
  · intro a b hab
    have h := congrArg (fun u : Rotor.Spin 1 => u.val 0) hab
    simp only [sphereSign_apply] at h
    cases a <;> cases b
    · rfl
    · norm_num [value] at h
    · norm_num [value] at h
    · rfl
  · intro u
    have hq : (u.val 0)^2 = 1 := by
      simpa only [Fin.sum_univ_one, norm_eq_of_mem_sphere u, one_pow] using
        (EuclideanSpace.real_norm_sq_eq u.val).symm
    have go (b : Bool) (hb : u.val 0 = value b) : sphereSign b = u := by
      apply Subtype.ext
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      rw [sphereSign_apply, hi, hb]
    rcases sq_eq_one_iff.mp hq with h | h
    · exact ⟨true, go true h⟩
    · exact ⟨false, go false h⟩

private def sphereEquiv : Bool ≃ Rotor.Spin 1 :=
  Equiv.ofBijective sphereSign sphereSign_bijective

private theorem sphereSign_inner (a b : Bool) :
    ⟪(sphereSign a).val, (sphereSign b).val⟫_ℝ = value a * value b := by
  simp [PiLp.inner_apply, sphereSign_apply, mul_comm]

local instance sphereFintype : Fintype (Rotor.Spin 1) := Fintype.ofEquiv Bool sphereEquiv
local instance sphereInhabited : Nonempty (Rotor.Spin 1) := ⟨sphereSign true⟩

/-- The uniform probability measure on the actual zero-dimensional sphere. -/
def fairSphere : Measure (Rotor.Spin 1) := (PMF.uniformOfFintype (Rotor.Spin 1)).toMeasure

instance fairSphere_prob : IsProbabilityMeasure fairSphere := by
  unfold fairSphere
  infer_instance

theorem fairSphere_singleton (u : Rotor.Spin 1) : fairSphere {u} = (2 : ℝ≥0∞)⁻¹ := by
  have h : Fintype.card (Rotor.Spin 1) = 2 :=
    (Fintype.card_congr sphereEquiv.symm).trans Fintype.card_bool
  rw [fairSphere, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, h]
  norm_num

/-- The polar-area prior used in every rotor dimension agrees on the
zero-dimensional sphere with the two-point uniform probability. Coordinate
reflection interchanges its two atoms, which exhaust its total mass. -/
theorem surfacePrior_one_eq_fairSphere : Rotor.SiteReflection.surfacePrior 1 = fairSphere := by
  let m := Rotor.SiteReflection.surfacePrior 1
  have flip (b : Bool) : SphereSign.flipCoord 0 (sphereSign b) = sphereSign (!b) := by
    apply Subtype.ext
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [SphereSign.flipCoord_apply, sphereSign_apply, sphereSign_apply, hi, if_pos rfl]
    cases b <;> norm_num [value]
  have hinj := sphereSign_bijective.1
  let a := sphereSign false
  let b := sphereSign true
  have hab : a ≠ b := fun h => Bool.false_ne_true (hinj h)
  have hpre : SphereSign.flipCoord (0 : Fin 1) ⁻¹' ({b} : Set (Rotor.Spin 1)) = {a} := by
    ext s
    obtain ⟨q, rfl⟩ := sphereSign_bijective.2 s
    cases q <;> simp [a, b, flip, hinj.eq_iff]
  have he : m {a} = m {b} := by
    have hm := (SphereSign.flipCoord_preserving (0 : Fin 1)).measure_preimage_equiv ({b} : Set (Rotor.Spin 1))
    rwa [hpre] at hm
  have hall : ({a} : Set (Rotor.Spin 1)) ∪ {b} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    obtain ⟨q, rfl⟩ := sphereSign_bijective.2 s
    cases q <;> simp [a,b]
  have hadd : m {a} + m {b} = 1 := by
    rw [← measure_union (Set.disjoint_singleton.2 hab) (MeasurableSet.singleton _), hall]
    exact measure_univ
  have ha : m {a} = (2 : ℝ≥0∞)⁻¹ := by
    rw [← he, ← two_mul] at hadd
    calc
      _ = (2:ℝ≥0∞)⁻¹ * (2 * m {a}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ = _ := by rw [hadd, mul_one]
  apply Measure.ext_of_singleton
  intro s
  rw [fairSphere_singleton]
  obtain ⟨q, rfl⟩ := sphereSign_bijective.2 s
  cases q
  · exact ha
  · exact he.symm.trans ha

private def sphereConfig (L : ℕ) : IsingScaling.Spin L ≃ Rotor.SiteReflection.Config 1 L :=
  (Equiv.refl (BoxSite L)).arrowCongr sphereEquiv

private theorem sphereProductCount (L : ℕ) :
    Measure.pi (fun _ : BoxSite L => fairSphere) =
      ((2:ℝ≥0∞)⁻¹ ^ Fintype.card (BoxSite L)) • (Measure.count : Measure (Rotor.SiteReflection.Config 1 L)) := by
  apply Measure.ext_of_singleton
  intro σ
  simp only [Measure.pi_singleton, fairSphere_singleton, Finset.prod_const, Finset.card_univ,
    Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

private theorem sphereGibbs (β : ℝ) (L : ℕ) (σ : IsingScaling.Spin L) :
    Real.exp (β * energy (sphereConfig L σ)) = gibbsWeight β L σ := by
  unfold energy gibbsWeight interaction
  congr 3
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change (if _ then ⟪(sphereSign (σ x)).val, (sphereSign (σ y)).val⟫_ℝ else _) = _
  rw [sphereSign_inner]

theorem rotor_box_pair {L : ℕ} (β : ℝ) (x y : BoxSite L) :
    Rotor.SiteReflection.boxCorrelation fairSphere β x y = IsingScaling.boxCorrelation β L x y := by
  classical
  let E := sphereConfig L
  let W (σ : Rotor.SiteReflection.Config 1 L) := Real.exp (β * energy σ)
  let F (σ : Rotor.SiteReflection.Config 1 L) := W σ * ⟪(σ x).val, (σ y).val⟫_ℝ
  let c := ((2:ℝ≥0∞)⁻¹ ^ Fintype.card (BoxSite L)).toReal
  have hc : c ≠ 0 := by simp [c]
  have hn : (∑ σ, F σ) = ∑ τ : IsingScaling.Spin L, gibbsWeight β L τ * value (τ x) * value (τ y) := by
    rw [← Equiv.sum_comp E F]
    apply Finset.sum_congr rfl
    intro τ _
    dsimp only [F,W,E]
    rw [sphereGibbs]
    change _ * ⟪(sphereSign (τ x)).val, (sphereSign (τ y)).val⟫_ℝ = _
    rw [sphereSign_inner, mul_assoc]
  have hd : (∑ σ, W σ) = ∑ τ : IsingScaling.Spin L, gibbsWeight β L τ := by
    rw [← Equiv.sum_comp E W]
    exact Finset.sum_congr rfl (fun τ _ => sphereGibbs β L τ)
  unfold Rotor.SiteReflection.boxCorrelation Rotor.SiteReflection.partition IsingScaling.boxCorrelation
  change (∫ σ, F σ ∂Measure.pi (fun _ : BoxSite L => fairSphere)) /
    (∫ σ, W σ ∂Measure.pi (fun _ : BoxSite L => fairSphere)) = _
  simp only [sphereProductCount, integral_smul_measure, integral_count, smul_eq_mul, hn, hd]
  exact mul_div_mul_left _ _ hc

theorem rotor_lattice_pair (β : ℝ) (L : ℕ) (x y : Site) :
    Rotor.SiteReflection.freePair fairSphere β L x y = IsingScaling.freePair β L x y := by
  by_cases hx : x ∈ cube L
  · by_cases hy : y ∈ cube L
    · rw [Rotor.SiteReflection.freePair, dite_eq_left hx, dite_eq_left hy, rotor_box_pair, boxCorrelation_eq_freePair]
    · simp [Rotor.SiteReflection.freePair, hx, hy, IsingScaling.freePair, occupation]
  · simp [Rotor.SiteReflection.freePair, hx, IsingScaling.freePair, occupation]

theorem rotor_surface_lattice_pair (β : ℝ) (L : ℕ) (x y : Site) :
    Rotor.SiteReflection.freePair (Rotor.SiteReflection.surfacePrior 1) β L x y =
      IsingScaling.freePair β L x y := by
  rw [surfacePrior_one_eq_fairSphere, rotor_lattice_pair]

def rotorThermodynamic (β : ℝ) (x : Site) : ℝ :=
  ⨆ L : ℕ, Rotor.SiteReflection.freePair (Rotor.SiteReflection.surfacePrior 1) β L 0 x

theorem rotor_thermodynamic_eq (β : ℝ) :
    rotorThermodynamic β = thermodynamicTwoPoint β := by
  funext x
  simp only [rotorThermodynamic, thermodynamicTwoPoint, rotor_surface_lattice_pair, freePair_origin]

theorem rotor_thermodynamic_limit {β : ℝ} (hβ : 0 ≤ β) (x y : Site) :
    Tendsto (fun L : ℕ => Rotor.SiteReflection.freePair (Rotor.SiteReflection.surfacePrior 1) β L x y) atTop
      (𝓝 (rotorThermodynamic β (x-y))) := by
  simpa only [rotor_surface_lattice_pair, rotor_thermodynamic_eq] using (thermodynamicTwoPoint_stationary hβ x y)

theorem rotor_packet_spectrum {β : ℝ} (hβ : 0 ≤ β)
    (d : PacketNormal) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
      evenPacket c (fun m i j => rotorThermodynamic β
        (signedPerm p s (d.displacement m (x i-x j) (y i-y j)))) n := by
  rw [rotor_thermodynamic_eq]
  exact thermodynamic_packet_spectrum hβ d p s c x y

theorem rotor_tangent_rotation {β : ℝ} (hβ : 0 ≤ β) {μ : Measure Space}
    [IsLocallyFiniteMeasure μ] {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (hlim : ∀ f : C_c(Space, ℝ), Tendsto
      (fun j => ∫ x, f x ∂twoPointMeasure (rotorThermodynamic β) (R j))
      atTop (𝓝 (∫ x, f x ∂μ))) (O : Space ≃ₗᵢ[ℝ] Space) : μ.map O = μ := by
  have hg := thermodynamicTwoPoint_isLimit hβ
  obtain ⟨hn, hχ⟩ := hg.positive_cube_mass hβ
  have ht : IsTwoPointTangent β μ :=
    ⟨thermodynamicTwoPoint β, R, hg, hn, fun j => hχ (R j), hR,
      by simpa only [rotor_thermodynamic_eq] using hlim⟩
  exact ht.rotation_invariant hβ O

/-- Every diverging scale sequence for the physical free kernel has a nonzero
orthogonally invariant tangent along a subsequence. -/
theorem rotor_exists_invariant_tangent {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
      (∀ f : C_c(Space, ℝ), Tendsto (fun j => ∫ x, f x ∂twoPointMeasure
        (rotorThermodynamic β) (R (u j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧
      (∀ O : Space ≃ₗᵢ[ℝ] Space, μ.map O = μ) := by
  rw [rotor_thermodynamic_eq]
  exact exists_rotation_invariant_tangent hβ hR

theorem rotor_rotated_test_difference {β : ℝ} (hβ : 0 ≤ β)
    (f : C_c(Space, ℝ)) (O : Space ≃ₗᵢ[ℝ] Space) :
    Tendsto (fun r : ℕ => (∫ x, f (O x) ∂twoPointMeasure (rotorThermodynamic β) r) -
      (∫ x, f x ∂twoPointMeasure (rotorThermodynamic β) r)) atTop (𝓝 0) := by
  rw [rotor_thermodynamic_eq]
  exact thermodynamicTwoPoint_rotated_test_difference hβ f O

#print axioms surfacePrior_one_eq_fairSphere
#print axioms rotor_surface_lattice_pair
#print axioms fairSphere_singleton
#print axioms rotor_lattice_pair
#print axioms rotor_packet_spectrum
#print axioms rotor_tangent_rotation
#print axioms rotor_exists_invariant_tangent
#print axioms rotor_rotated_test_difference
end IsingScaling.BinarySpin

end
