import MathlibProbe.PottsPhysicalSiteReflection
import MathlibProbe.PottsEdwardsSokal

/-! The free Edwards–Sokal expansion for the very same Gibbs weight
used in the Potts site-reflection and packet theorems. -/

noncomputable section
open Finset Filter
open scoped BigOperators Classical Topology
namespace IsingScaling.Potts.SiteBox
open EdwardsSokal

private def earlier {L : ℕ} (x y : BoxSite L) : Prop :=
  Fintype.equivFin (BoxSite L) x < Fintype.equivFin (BoxSite L) y

/-- One representative of each unoriented nearest-neighbour bond. -/
def cubeBonds (L : ℕ) : Finset (BoxSite L × BoxSite L) :=
  univ.filter (fun e => earlier e.1 e.2 ∧ latticeDistance e.1 e.2 = 1)

private lemma distance_swap (x y : Site) : latticeDistance x y = latticeDistance y x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← neg_sub (y i) (x i), Int.natAbs_neg]

private theorem energy_eq_bond_sum {q L : ℕ} (σ : Config q L) :
    energy equalColour σ = ∑ e ∈ cubeBonds L, equalColour (σ e.1) (σ e.2) := by
  classical
  let A (x y : BoxSite L) : ℝ :=
    if earlier x y ∧ latticeDistance x y = 1 then equalColour (σ x) (σ y) else 0
  have splitBond (x y : BoxSite L) : bondTerm equalColour σ x y = A x y + A y x := by
    have hs := distance_swap x y
    by_cases he : latticeDistance x y = 1
    · have hn : x ≠ y := by
        rintro rfl
        simp [latticeDistance] at he
      have hd : latticeDistance y x = 1 := hs.symm.trans he
      have hne := (Fintype.equivFin (BoxSite L)).injective.ne hn
      rcases lt_or_gt_of_ne hne with h|h
      · simp [bondTerm, A, earlier, he, hd, h, not_lt.mpr h.le]
      · simp [bondTerm, A, earlier, he, hd, h, not_lt.mpr h.le, equalColour, eq_comm]
    · have hd : latticeDistance y x ≠ 1 := fun hy => he (hs.trans hy)
      simp [bondTerm, A, he, hd]
  have hs : (∑ x, ∑ y, A y x) = ∑ x, ∑ y, A x y := Finset.sum_comm
  unfold energy cubeBonds
  simp_rw [splitBond, Finset.sum_add_distrib]
  rw [hs, Finset.sum_filter, Fintype.sum_prod_type]
  change ((∑ x, ∑ y, A x y) + ∑ x, ∑ y, A x y) / 2 = ∑ x, ∑ y, A x y
  ring

theorem weight_eq_bond_product {q L : ℕ} (β : ℝ) (σ : Config q L) :
    weight equalColour β σ = spinWeight (cubeBonds L) (fun _ => β) σ := by
  unfold weight spinWeight
  rw [energy_eq_bond_sum, Finset.mul_sum, Real.exp_sum]
  apply prod_congr rfl
  intro e _
  by_cases h : σ e.1 = σ e.2 <;> simp [equalColour, edgeWeight, h]

private theorem simplex_eq_es {q : ℕ} (a b : Fin q) : simplex a b = simplexMark a b := by
  by_cases h : a = b <;> simp [simplex, simplexMark, equalColour, h]

def freeFKPair (q : ℕ) (β : ℝ) {L : ℕ} (x y : BoxSite L) : ℝ :=
  (∑ F ∈ (cubeBonds L).powerset, if port F x = port F y
    then fkWeight q (fun _ => β) F else 0) /
    ∑ F ∈ (cubeBonds L).powerset, fkWeight q (fun _ => β) F

/-- Equality of the Gibbs observable in the mirror theorem and the
free FK connectivity with single-bond odds exp(β) − 1. -/
theorem boxPair_eq_freeFKPair {q : ℕ} (hq : 2 ≤ q) (β : ℝ) {L : ℕ} (x y : BoxSite L) :
    boxPair q β x y = freeFKPair q β x y := by
  unfold boxPair freeFKPair
  simp_rw [weight_eq_bond_product, simplex_eq_es]
  have hes := simplex_correlation_eq_connectivity (V := BoxSite L) hq (cubeBonds L)
    (fun _ => β) x y
  -- The two finite sums enumerate the same colourings with different
  -- decidable-equality instances on the site type.
  with_reducible convert! hes using 5

theorem boxPair_nonneg {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {L : ℕ} (x y : BoxSite L) : 0 ≤ boxPair q β x y := by
  rw [boxPair_eq_freeFKPair hq]
  unfold freeFKPair
  refine div_nonneg (sum_nonneg fun F _ => ?_) (fkPartition_pos (by omega : 0 < q) _ _).le
  split
  · exact fkWeight_nonneg _ _ _ (fun _ _ => hβ)
  · exact le_rfl

theorem StationaryPairLimit.ferromagnetic_nonneg {q : ℕ} (hq : 2 ≤ q) {β : ℝ}
    (hβ : 0 ≤ β) {sizes g} (hg : StationaryPairLimit q β sizes g) (z : Site) :
    0 ≤ g z := by
  have hl := hg z 0
  rw [sub_zero] at hl
  apply ge_of_tendsto hl (Eventually.of_forall ?_)
  intro j
  unfold latticePair
  split
  · split
    · exact boxPair_nonneg hq hβ _ _
    · exact le_rfl
  · exact le_rfl

#print axioms boxPair_eq_freeFKPair
#print axioms StationaryPairLimit.ferromagnetic_nonneg
end IsingScaling.Potts.SiteBox
