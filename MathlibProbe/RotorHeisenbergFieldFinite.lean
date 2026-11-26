import MathlibProbe.RotorFreePairNonneg
import MathlibProbe.RotorInternalOrthogonal
import MathlibProbe.RotorStationaryRawAngular

/-! # Finite free Heisenberg pairs in a uniform external field

Tilting one normalized sphere law by `h s₀` inserts `exp (h ∑ₓ sₓ₀)`
in its finite product. To prove nonnegativity of the dot insertion, adjoin
one unit spin with a ferromagnetic edge of weight `h` to each old vertex.
At a fixed value of the added spin the numerator is independent of its
direction by a common orthogonal transformation of the old spins. Integrating
the added spin therefore gives the original numerator at direction `e₁`.
The zero-field ferromagnetic expansion applies on the enlarged graph.
-/

noncomputable section
open MeasureTheory Finset Filter
open scoped InnerProductSpace Topology
namespace IsingScaling.Rotor.HeisenbergField
open PressureSelection

private abbrev θ := SiteReflection.surfacePrior 3

/-- Dimensionless source along the first physical spin component. -/
def siteField (h : ℝ) (s : Spin 3) : ℝ := h * s.val 0

def fieldPrior (h : ℝ) : Measure (Spin 3) := θ.tilted (siteField h)

private theorem continuousSiteField (h : ℝ) : Continuous (siteField h) := by unfold siteField; fun_prop

instance (h : ℝ) : IsProbabilityMeasure (fieldPrior h) :=
  isProbabilityMeasure_tilted ((continuousSiteField h).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

/-- The product of the tilted single spins is the normalized joint
Boltzmann tilt of the original product surface measure. -/
theorem fieldPrior_product (V : Type*) [Fintype V] (h : ℝ) :
    Measure.pi (fun _ : V => fieldPrior h) =
      (Measure.pi fun _ : V => θ).tilted (fun s => ∑ x : V, siteField h (s x)) := by
  classical
  apply Measure.pi_eq
  intro S hS
  simp only [fieldPrior, tilted_apply_eq_ofReal_integral, integral_div, Real.exp_sum,
    Measure.restrict_pi_pi]
  have prodInt (μ : V → Measure (Spin 3)) [∀ i, SigmaFinite (μ i)] :
      (∫ s : V → Spin 3, ∏ i, Real.exp (siteField h (s i)) ∂Measure.pi μ) =
        ∏ i, ∫ u, Real.exp (siteField h u) ∂μ i :=
    integral_fintype_prod_eq_prod (fun (_ : V) (u : Spin 3) => Real.exp (siteField h u))
  rw [prodInt, prodInt, ← Finset.prod_div_distrib]
  apply ENNReal.ofReal_prod_of_nonneg
  intro i _
  exact div_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)
    (integral_nonneg fun _ => (Real.exp_pos _).le)

/-- Unit vector along the external field. -/
def firstSpin : Spin 3 := ⟨EuclideanSpace.single 0 1, by simp⟩

theorem abs_siteField_le (h : ℝ) (s : Spin 3) : |siteField h s| ≤ |h| := by
  rw [siteField, abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  have H := abs_real_inner_le_norm firstSpin.val s.val
  simpa [firstSpin, EuclideanSpace.inner_single_left, norm_eq_of_mem_sphere] using H

private abbrev Config (V : Type*) := V → Spin 3
private abbrev productPrior (V : Type*) [Fintype V] := Measure.pi (fun _ : V => θ)

private def interaction {V : Type*} [Fintype V] (J : V × V → ℝ) (s : Config V) : ℝ :=
  ∑ e : V × V, J e * ⟪(s e.1).val, (s e.2).val⟫_ℝ

private def insertion {V : Type*} [Fintype V] (J : V × V → ℝ) (h : ℝ) (p q : V)
    (u : Spin 3) (s : Config V) : ℝ :=
  Real.exp (interaction J s + ∑ i : V, h * ⟪u.val, (s i).val⟫_ℝ) * ⟪(s p).val,(s q).val⟫_ℝ

private theorem direction_independent {V : Type*} [Fintype V] (J : V × V → ℝ) (h : ℝ) (p q : V)
    (u : Spin 3) : (∫ s, insertion J h p q u s ∂productPrior V) =
      ∫ s, insertion J h p q firstSpin s ∂productPrior V := by
  let U := (Submodule.span ℝ ({firstSpin.val-u.val} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ.reflection
  have hU : U firstSpin.val = u.val := Submodule.reflection_sub (by simp [norm_eq_of_mem_sphere])
  let M := InternalOrthogonal.rotate (V := V) U
  have hm : MeasurePreserving M (productPrior V) (productPrior V) :=
    measurePreserving_pi (fun _ : V => θ) (fun _ : V => θ)
      (f := fun _ s => SiteReflection.SphereSign.sphereMap U s)
      (fun _ => SiteReflection.SphereSign.sphereMap_preserving U)
  have hc : Continuous (insertion J h p q u) := by unfold insertion interaction; fun_prop
  rw [← hm.hasLaw.integral_comp hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    simp only [Function.comp_apply, M, insertion, interaction, InternalOrthogonal.rotate_val, ← hU, U.inner_map_map]

private def enlarged {V : Type*} (J : V × V → ℝ) (h : ℝ) : (Unit ⊕ V) × (Unit ⊕ V) → ℝ
  | (.inr i, .inr j) => J (i,j)
  | (.inl _, .inr _) => h
  | _ => 0

private theorem ghost_read {V : Type*} [Fintype V] (J : V × V → ℝ) (h : ℝ) (p q : V)
    (u : Unit → Spin 3) (s : Config V) :
    Real.exp (interaction (enlarged J h) (Sum.elim u s)) *
      ⟪(Sum.elim u s (Sum.inr p)).val,(Sum.elim u s (Sum.inr q)).val⟫_ℝ =
      insertion J h p q (u ()) s := by
  simp [interaction, insertion, Fintype.sum_prod_type, Fintype.sum_sum_type, enlarged, add_comm]

set_option maxHeartbeats 1200000 in
private theorem insertion_nonneg {V : Type*} [Fintype V] (J : V × V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) {h : ℝ} (hh : 0 ≤ h) (p q : V) :
    0 ≤ ∫ s, insertion J h p q firstSpin s ∂productPrior V := by
  have he (e : (Unit ⊕ V) × (Unit ⊕ V)) : 0 ≤ enlarged J h e := by
    rcases e with ⟨i | i, j | j⟩ <;> simp only [enlarged] <;> first | exact hh | apply hJ | exact le_rfl
  have hz := surface_bond_dot_numerator_nonneg 3 (enlarged J h) he (.inr p) (.inr q)
  have hE := measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ V => θ)
  let A (s : Config (Unit ⊕ V)) := Real.exp (interaction (enlarged J h) s) *
    ⟪(s (.inr p)).val,(s (.inr q)).val⟫_ℝ
  change 0 ≤ ∫ s, A s ∂productPrior (Unit ⊕ V) at hz
  rw [← hE.integral_comp' A] at hz
  change 0 ≤ ∫ us : Config Unit × Config V, A (Sum.elim us.1 us.2)
    ∂(productPrior Unit).prod (productPrior V) at hz
  let B (us : Config Unit × Config V) := insertion J h p q (us.1 ()) us.2
  have hB : Continuous B := by unfold B insertion interaction; fun_prop
  have eq : (fun us : Config Unit × Config V => A (Sum.elim us.1 us.2)) = B :=
    funext fun us => ghost_read J h p q us.1 us.2
  rw [eq, integral_prod _ (hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hz
  simpa [B, direction_independent J h p q, measureReal_def] using hz

private def nearestBond {L : ℕ} (β : ℝ) (e : BoxSite L × BoxSite L) :=
  if latticeDistance e.1 e.2 = 1 then β/2 else 0

private theorem cube_interaction {L : ℕ} (β : ℝ) (s : Config (BoxSite L)) :
    interaction (nearestBond β) s = β * SiteReflection.energy s := by
  unfold interaction nearestBond
  rw [Fintype.sum_prod_type]
  change _ = β * ((∑ x : BoxSite L, ∑ y : BoxSite L, if latticeDistance x y = 1 then
    ⟪(s x).val,(s y).val⟫_ℝ else 0)/2)
  rw [show ∀ a : ℝ, β*(a/2) = (β/2)*a by intro a; ring]
  simp only [Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]

/-- Nonnegativity for the full dot product in the actual positive-field free cube. -/
theorem freePair_nonnegative {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (L : ℕ) (x y : Site) :
    0 ≤ SiteReflection.freePair (fieldPrior h) β L x y := by
  classical
  by_cases hx : x ∈ cube L
  case neg => simp [SiteReflection.freePair, hx]
  by_cases hy : y ∈ cube L
  case neg => simp [SiteReflection.freePair, hx, hy]
  let p : BoxSite L := ⟨x,hx⟩
  let q : BoxSite L := ⟨y,hy⟩
  change 0 ≤ SiteReflection.freePair (fieldPrior h) β L p q
  rw [SiteReflection.freePair_inside, SiteReflection.boxCorrelation]
  apply div_nonneg _ (SiteReflection.partition_pos _ _ _).le
  let logH (s : Config (BoxSite L)) := ∑ v : BoxSite L, siteField h (s v)
  let Z := ∫ s, Real.exp (logH s) ∂productPrior (BoxSite L)
  change 0 ≤ ∫ s : Config (BoxSite L), Real.exp (β * SiteReflection.energy s) *
    ⟪(s p).val,(s q).val⟫_ℝ ∂Measure.pi (fun _ => fieldPrior h)
  rw [fieldPrior_product, integral_tilted]
  have eq (s : Config (BoxSite L)) :
      (Real.exp (logH s) / Z) • (Real.exp (β * SiteReflection.energy s) *
        ⟪(s p).val,(s q).val⟫_ℝ) = insertion (nearestBond β) h p q firstSpin s / Z := by
    simp only [insertion, cube_interaction, firstSpin, EuclideanSpace.inner_single_left, map_one,
      one_mul, Real.exp_add, logH, siteField, smul_eq_mul]
    ring
  change 0 ≤ ∫ s : Config (BoxSite L), (Real.exp (logH s)/Z) •
    (Real.exp (β * SiteReflection.energy s) * ⟪(s p).val,(s q).val⟫_ℝ) ∂productPrior (BoxSite L)
  simp_rw [eq]
  rw [integral_div]
  apply div_nonneg _ (integral_nonneg fun _ => (Real.exp_pos _).le)
  exact insertion_nonneg _ (fun e => by simp only [nearestBond]; split <;> positivity) hh p q

#print axioms fieldPrior_product
#print axioms freePair_nonnegative

end IsingScaling.Rotor.HeisenbergField
