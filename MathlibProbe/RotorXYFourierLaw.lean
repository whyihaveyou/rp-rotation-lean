import MathlibProbe.RotorXYFreeFourierComparison
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-! # Fourier determination of the full planar-spin law

Each finitely supported integer charge gives a character of the product
of physical planar spin circles through the phase map. Their complex
integrals determine a Borel probability on a countable product and
characterize weak convergence. The topology on the space of moments is
pointwise convergence in the charge. The finite-volume Ginibre comparison
and spin reflection then select one nearest-neighbour Gibbs law along every
exhaustion, with arbitrary exterior fills.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace IsingScaling.Rotor.XY

variable {ι : Type*}

private def unitMonomial (k : ι →₀ ℤ) (s : ι → Spin 2) : Circle :=
  k.prod fun i n => phase (s i) ^ n

/-- The character of a finitely supported integer charge on the physical XY field. -/
def integerCharacter (k : ι →₀ ℤ) : (ι → Spin 2) →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun s => (unitMonomial k s : ℂ), continuous_subtype_val.comp
      (continuous_finsetProd _ fun i _ => (continuous_phase.comp (continuous_apply i)).zpow (k i))⟩

private lemma unitMonomial_add (k l : ι →₀ ℤ) (s : ι → Spin 2) :
    unitMonomial (k + l) s = unitMonomial k s * unitMonomial l s :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ => zpow_add _)

private lemma character_zero : integerCharacter (0 : ι →₀ ℤ) = 1 := by
  apply BoundedContinuousFunction.ext
  intro s
  change (unitMonomial (0 : ι →₀ ℤ) s : ℂ) = 1
  simp [unitMonomial]

private lemma character_add (k l : ι →₀ ℤ) :
    integerCharacter (k + l) = integerCharacter k * integerCharacter l := by
  apply BoundedContinuousFunction.ext
  intro s
  change (unitMonomial (k+l) s : ℂ) = (unitMonomial k s : ℂ) * unitMonomial l s
  rw [unitMonomial_add, Circle.coe_mul]

private lemma character_neg (k : ι →₀ ℤ) :
    integerCharacter (-k) = star (integerCharacter k) := by
  apply BoundedContinuousFunction.ext
  intro s
  have h : unitMonomial (-k) s = (unitMonomial k s)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← unitMonomial_add, neg_add_cancel]
    simp [unitMonomial]
  change (unitMonomial (-k) s : ℂ) = star (unitMonomial k s : ℂ)
  exact (congrArg ((↑) : Circle → ℂ) h).trans (Circle.coe_inv_eq_conj _)

private lemma character_single (i : ι) (s : ι → Spin 2) :
    integerCharacter (Finsupp.single i 1) s = (phase (s i) : ℂ) := by
  change (unitMonomial (Finsupp.single i 1) s : ℂ) = (phase (s i) : ℂ)
  apply congrArg ((↑) : Circle → ℂ)
  unfold unitMonomial
  rw [Finsupp.prod_single_index (by simp), zpow_one]

private lemma phase_injective : Function.Injective phase := by
  intro s t h
  exact Subtype.ext (Complex.orthonormalBasisOneI.repr.symm.injective (congrArg Subtype.val h))

private def characterAlgebra (ι : Type*) : StarSubalgebra ℂ ((ι → Spin 2) →ᵇ ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (integerCharacter (ι := ι)))
  star_mem' := by
    change Algebra.adjoin ℂ (range (integerCharacter (ι := ι))) ≤
      star (Algebra.adjoin ℂ (range (integerCharacter (ι := ι))))
    apply Algebra.adjoin_le
    rintro _ ⟨k, rfl⟩
    exact Algebra.subset_adjoin ⟨-k, character_neg k⟩

private lemma characterAlgebra_span :
    (characterAlgebra ι).toSubalgebra.toSubmodule =
      Submodule.span ℂ (range (integerCharacter (ι := ι))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0, character_zero⟩ ?_)
    Submodule.subset_span
  rintro _ _ _ _ ⟨k, rfl⟩ ⟨l, rfl⟩
  exact ⟨k + l, character_add k l⟩

private lemma characterAlgebra_separates :
    ((characterAlgebra ι).map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro s t hst
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
  let k := Finsupp.single i (1 : ℤ)
  use integerCharacter k
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  refine ⟨⟨integerCharacter k, Algebra.subset_adjoin ⟨k, rfl⟩, rfl⟩, ?_⟩
  change integerCharacter (Finsupp.single i 1) s ≠ integerCharacter (Finsupp.single i 1) t
  rw [character_single, character_single]
  exact fun h => hi (phase_injective (Circle.coe_injective h))

variable [Countable ι]

/-- The complete table of finite-charge Fourier integrals of a planar-spin probability. -/
def integerMoments (P : ProbabilityMeasure (ι → Spin 2)) (k : ι →₀ ℤ) : ℂ :=
  ∫ s, integerCharacter k s ∂(P : Measure _)

/-- Equality of all integer Fourier moments identifies the entire countable-product law. -/
theorem law_eq_of_integerMoments {P Q : ProbabilityMeasure (ι → Spin 2)}
    (h : ∀ k, integerMoments P k = integerMoments Q k) : P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish characterAlgebra_separates
  intro f hf
  change f ∈ (characterAlgebra ι).toSubalgebra.toSubmodule at hf
  rw [characterAlgebra_span] at hf
  induction hf using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨k, rfl⟩ := hx
    exact h k
  | zero => simp
  | add f g _ _ hf hg =>
    simp only [BoundedContinuousFunction.add_apply, integral_add (f.integrable _) (g.integrable _),
      hf, hg]
  | smul c f _ hf =>
    simp only [BoundedContinuousFunction.smul_apply, integral_smul, hf]

/-- The moment map identifies the weak probability space with a closed
subspace of the product of its complex moment coordinates. -/
theorem integerMoments_isClosedEmbedding :
    Topology.IsClosedEmbedding (integerMoments (ι := ι)) := by
  apply Continuous.isClosedEmbedding
  · apply continuous_pi
    intro k
    apply continuous_iff_continuousAt.mpr
    intro P
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
      (tendsto_id (x := 𝓝 P)) (integerCharacter k)
  · intro P Q h
    exact law_eq_of_integerMoments (congrFun h)

/-- For any filter, convergence of all charge integrals to those of a
given law is equivalent to weak convergence to that law. -/
theorem tendsto_iff_integerMoments {α : Type*} {l : Filter α}
    {P : α → ProbabilityMeasure (ι → Spin 2)} {Q : ProbabilityMeasure (ι → Spin 2)} :
    Tendsto P l (𝓝 Q) ↔ ∀ k, Tendsto (fun a => integerMoments (P a) k) l (𝓝 (integerMoments Q k)) :=
  integerMoments_isClosedEmbedding.tendsto_nhds_iff.trans tendsto_pi_nhds

/-- If each moment has a limit, there exists a unique law realizing all
these limits, and the whole family converges weakly to it. -/
theorem existsUnique_law_of_integerMoments_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    (P : α → ProbabilityMeasure (ι → Spin 2)) (m : (ι →₀ ℤ) → ℂ)
    (h : ∀ k, Tendsto (fun a => integerMoments (P a) k) l (𝓝 (m k))) :
    ∃! Q, integerMoments Q = m ∧ Tendsto P l (𝓝 Q) := by
  have hm : m ∈ range (integerMoments (ι := ι)) :=
    integerMoments_isClosedEmbedding.isClosed_range.mem_of_tendsto
      (tendsto_pi_nhds.mpr h) (Eventually.of_forall fun a => ⟨P a, rfl⟩)
  obtain ⟨Q, rfl⟩ := hm
  exact ⟨Q, ⟨rfl, tendsto_iff_integerMoments.mpr h⟩,
    fun R hR => law_eq_of_integerMoments (congrFun hR.1)⟩

open PressureSelection PressureSelection.FreeExhaustion PressureSelection.LocalGibbs

/-- The finite-volume input for the free XY state. The first assertion is
the domain form of Ginibre's inequality for every integer charge. Reflection
of all spins gives the second assertion. The exterior fills may differ. -/
structure FreeChargeComparison (β : ℝ) : Prop where
  re_mono (k : Site →₀ ℤ) {D E : Finset Site} (hk : k.support ⊆ D) (hDE : D ⊆ E)
      (u v : SpinField 2) :
      (integerMoments (freeDomainLaw 2 β D u) k).re ≤ (integerMoments (freeDomainLaw 2 β E v) k).re
  im_zero (k : Site →₀ ℤ) {D : Finset Site} (hk : k.support ⊆ D) (u : SpinField 2) :
      (integerMoments (freeDomainLaw 2 β D u) k).im = 0

private def referenceField : SpinField 2 :=
  fun _ => ⟨EuclideanSpace.single (0 : Fin 2) 1, by simp⟩

private def finiteRealMoment (β : ℝ) (k : Site →₀ ℤ) (D : Finset Site) : ℝ :=
  (integerMoments (freeDomainLaw 2 β (D ∪ k.support) referenceField) k).re

/-- Supremum over finite volumes containing the charge support. -/
def freeMomentSup (β : ℝ) (k : Site →₀ ℤ) : ℝ := ⨆ D, finiteRealMoment β k D

omit [Countable ι] in
private lemma re_moment_le_one (P : ProbabilityMeasure (ι → Spin 2)) (k : ι →₀ ℤ) :
    (integerMoments P k).re ≤ 1 := by
  refine (Complex.re_le_norm _).trans ?_
  have hb : ∀ s : ι → Spin 2, ‖integerCharacter k s‖ ≤ 1 :=
    fun s => (Circle.norm_coe (unitMonomial k s)).le
  simpa [integerMoments] using
    (norm_integral_le_of_norm_le_const (μ := (P : Measure _)) (Eventually.of_forall hb))

/-- Real Ginibre comparison on domains and vanishing imaginary moments suffice
for convergence of each charge along every exhaustion. -/
theorem free_integerMoments_tendsto {β : ℝ} (H : FreeChargeComparison β)
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n)
    (fill : ℕ → SpinField 2) (k : Site →₀ ℤ) :
    Tendsto (fun n => integerMoments (freeDomainLaw 2 β (D n) (fill n)) k) atTop
      (𝓝 (freeMomentSup β k : ℂ)) := by
  have hd : Tendsto D atTop atTop :=
    tendsto_atTop.mpr fun E => E.finite_toSet.eventually_all.mpr fun x _ => hex x
  have hmono : Monotone (finiteRealMoment β k) := fun _ _ h =>
    H.re_mono k Finset.subset_union_right (Finset.union_subset_union_left h) _ _
  have hb : BddAbove (range (finiteRealMoment β k)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨E, rfl⟩
    exact re_moment_le_one _ k
  have hlim : Tendsto (fun n => finiteRealMoment β k (D n)) atTop (𝓝 (freeMomentSup β k)) :=
    (tendsto_atTop_ciSup hmono hb).comp hd
  apply (Complex.continuous_ofReal.continuousAt.tendsto.comp hlim).congr'
  filter_upwards [hd.eventually (eventually_ge_atTop k.support)] with n hn
  change ((integerMoments (freeDomainLaw 2 β (D n ∪ k.support) referenceField) k).re : ℂ) = _
  rw [Finset.union_eq_left.mpr hn]
  apply Complex.ext
  · exact le_antisymm (H.re_mono k hn le_rfl _ _) (H.re_mono k hn le_rfl _ _)
  · exact (H.im_zero k hn _).symm

/-- The same complete XY law is selected by every exhausting sequence of
induced free domains, even with distinct exterior fills. It is a DLR state.
The sole physical inputs here are the explicit finite charge comparisons. -/
theorem existsUnique_free_gibbs_of_chargeComparison {β : ℝ} (H : FreeChargeComparison β) :
    ∃! Q : ProbabilityMeasure (SpinField 2), IsNearestGibbs 2 β Q ∧
      ∀ (D : ℕ → Finset Site), (∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) →
        ∀ fill : ℕ → SpinField 2, Tendsto (fun n => freeDomainLaw 2 β (D n) (fill n)) atTop (𝓝 Q) := by
  let P := fun n => freeDomainLaw 2 β (cube n) referenceField
  obtain ⟨Q, ⟨hm, hQ⟩, _⟩ := existsUnique_law_of_integerMoments_tendsto P
    (fun k => (freeMomentSup β k : ℂ))
    (free_integerMoments_tendsto H cube BondMirror.ev_cube (fun _ => referenceField))
  refine ⟨Q, ⟨gibbs_of_free_exhaustion BondMirror.ev_cube _ hQ, ?_⟩, ?_⟩
  · intro D hex fill
    apply tendsto_iff_integerMoments.mpr
    intro k
    rw [congrFun hm k]
    exact free_integerMoments_tendsto H D hex fill k
  · intro R hR
    exact tendsto_nhds_unique (hR.2 cube BondMirror.ev_cube (fun _ => referenceField)) hQ

private lemma listedCharacter_support (k : Site →₀ ℤ) (s : SpinField 2) :
    listedCharacter (fun i : k.support => i.val) (fun i => k i.val) s = integerCharacter k s := by
  exact congrArg ((↑) : Circle → ℂ)
    (Finset.prod_coe_sort k.support (fun i => phase (s i) ^ k i))

private lemma moment_re (P : ProbabilityMeasure (SpinField 2)) (k : Site →₀ ℤ) :
    (integerMoments P k).re = ∫ s, (integerCharacter k s).re ∂(P : Measure _) := by
  simpa only [integerMoments, RCLike.re_eq_complex_re] using
    (integral_re (𝕜 := ℂ) (μ := (P : Measure (SpinField 2)))
      ((integerCharacter k).integrable (P : Measure (SpinField 2)))).symm

private lemma moment_im (P : ProbabilityMeasure (SpinField 2)) (k : Site →₀ ℤ) :
    (integerMoments P k).im = ∫ s, (integerCharacter k s).im ∂(P : Measure _) := by
  simpa only [integerMoments, RCLike.im_eq_complex_im] using
    (integral_im (𝕜 := ℂ) (μ := (P : Measure (SpinField 2)))
      ((integerCharacter k).integrable (P : Measure (SpinField 2)))).symm

/-- The physical domain comparison and spin-reflection identity give both
inputs to the selection theorem with the actual free-domain integrals. -/
theorem freeChargeComparison {β : ℝ} (hβ : 0 ≤ β) : FreeChargeComparison β := by
  constructor
  · intro k D E hk hDE u v
    simp_rw [moment_re, ← listedCharacter_support]
    exact domainCharacter_real_mono hβ hDE (fun i : k.support => ⟨i.val, hk i.property⟩)
      (fun i => k i.val) u v
  · intro k D hk u
    simp_rw [moment_im, ← listedCharacter_support]
    exact domainCharacter_im_eq_zero β D (fun i : k.support => ⟨i.val, hk i.property⟩)
      (fun i => k i.val) u

/-- At any nonnegative inverse temperature one nearest-neighbour XY Gibbs
state is the weak limit of the actual free laws on every exhausting sequence.
The statement singles out the free state among possible Gibbs states. -/
theorem existsUnique_free_gibbs {β : ℝ} (hβ : 0 ≤ β) :
    ∃! Q : ProbabilityMeasure (SpinField 2), IsNearestGibbs 2 β Q ∧
      ∀ (D : ℕ → Finset Site), (∀ x : Site, ∀ᶠ n in atTop, x ∈ D n) →
        ∀ fill : ℕ → SpinField 2, Tendsto (fun n => freeDomainLaw 2 β (D n) (fill n)) atTop (𝓝 Q) :=
  existsUnique_free_gibbs_of_chargeComparison (freeChargeComparison hβ)

/-- The same Fourier limit is reached when the finite free domains exhaust
the lattice and their inverse temperatures approach the endpoint from below.
The domains, temperatures and exterior fills may vary independently. -/
theorem free_integerMoments_tendsto_fromBelow {β : ℝ} {γ : ℕ → ℝ}
    (hγ : ∀ n, 0 ≤ γ n) (hle : ∀ n, γ n ≤ β) (hlim : Tendsto γ atTop (𝓝 β))
    (D : ℕ → Finset Site) (hex : ∀ x : Site, ∀ᶠ n in atTop, x ∈ D n)
    (fill : ℕ → SpinField 2) (k : Site →₀ ℤ) :
    Tendsto (fun n => integerMoments (freeDomainLaw 2 (γ n) (D n) (fill n)) k) atTop
      (𝓝 (freeMomentSup β k : ℂ)) := by
  have hβ : 0 ≤ β := (hγ 0).trans (hle 0)
  have inside (E : Finset Site) : ∀ᶠ n in atTop, E ⊆ D n :=
    E.finite_toSet.eventually_all.mpr fun x _ => hex x
  let M (t : ℝ) (E : Finset Site) (u : SpinField 2) := (integerMoments (freeDomainLaw 2 t E u) k).re
  have temperature (E : Finset Site) (hk : k.support ⊆ E) (u : SpinField 2) :
      Continuous (fun t => M t E u) ∧ MonotoneOn (fun t => M t E u) (Ici 0) := by
    dsimp only [M]
    simp_rw [moment_re, ← listedCharacter_support]
    exact domainCharacter_real_temperature E (fun i : k.support => ⟨i.val, hk i.property⟩)
      (fun i => k i.val) u
  have fixed : Tendsto (fun n => M β (D n) (fill n)) atTop (𝓝 (freeMomentSup β k)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (free_integerMoments_tendsto (freeChargeComparison hβ) D hex fill k)
  have realLimit : Tendsto (fun n => M (γ n) (D n) (fill n)) atTop (𝓝 (freeMomentSup β k)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨j, hj, hja⟩ := ((inside k.support).and (fixed.eventually (lt_mem_nhds ha))).exists
      have competitor := (temperature (D j) hj (fill j)).1.continuousAt.tendsto.comp hlim
      filter_upwards [competitor.eventually (lt_mem_nhds hja), inside (D j)] with n hn hD
      exact hn.trans_le ((freeChargeComparison (hγ n)).re_mono k hj hD (fill j) (fill n))
    · intro b hb
      filter_upwards [inside k.support, fixed.eventually (gt_mem_nhds hb)] with n hn hnb
      exact ((temperature (D n) hn (fill n)).2 (hγ n) hβ (hle n)).trans_lt hnb
  apply realLimit.ofReal.congr'
  filter_upwards [inside k.support] with n hn
  exact Complex.ext rfl ((freeChargeComparison (hγ n)).im_zero k hn (fill n)).symm

#print axioms law_eq_of_integerMoments
#print axioms integerMoments_isClosedEmbedding
#print axioms tendsto_iff_integerMoments
#print axioms existsUnique_law_of_integerMoments_tendsto
#print axioms free_integerMoments_tendsto
#print axioms existsUnique_free_gibbs_of_chargeComparison
#print axioms freeChargeComparison
#print axioms existsUnique_free_gibbs
#print axioms free_integerMoments_tendsto_fromBelow

end IsingScaling.Rotor.XY
