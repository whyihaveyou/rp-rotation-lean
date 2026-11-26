import MathlibProbe.PottsEdwardsSokal
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-! Monotonicity under adding bonds of the finite free FK connectivity
whose equality with the Potts simplex insertion is proved in EdwardsSokal.
The proof uses the additive group of compatible colours at each bond set. -/
noncomputable section
open Finset
open scoped BigOperators

namespace IsingScaling.Potts.EdwardsSokal

variable {V : Type*} [Fintype V]
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

private def colourGroup (q : ℕ) [NeZero q] (A : Finset (V × V)) :
    AddSubgroup (V → Fin q) where
  carrier := {σ | Compatible A σ}
  zero_mem' _ _ := rfl
  add_mem' := by
    intro σ τ hσ hτ e he
    exact congrArg₂ (· + ·) (hσ e he) (hτ e he)
  neg_mem' := by
    intro σ hσ e he
    exact congrArg (fun a : Fin q => -a) (hσ e he)

private theorem card_colourGroup (q : ℕ) [NeZero q] (A : Finset (V × V)) :
    Nat.card (colourGroup q A) = q ^ Fintype.card (Component A) := by
  classical
  change Nat.card {σ : V → Fin q // Compatible A σ} = _
  rw [Nat.card_congr (componentColorEquiv A q), Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin]

private theorem colourGroup_antitone (q : ℕ) [NeZero q] {A B : Finset (V × V)} (h : A ⊆ B) :
    colourGroup q B ≤ colourGroup q A := fun _ hσ e he => hσ e (h he)

private theorem card_mul_relIndex_of_le {G : Type*} [AddCommGroup G]
    (H K : AddSubgroup G) (hHK : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  simpa only [AddSubgroup.relIndex_bot_left] using
    AddSubgroup.relIndex_mul_relIndex (⊥ : AddSubgroup G) H K bot_le hHK

private theorem card_mul_card_eq_inf_sup {G : Type*} [AddCommGroup G]
    (H K : AddSubgroup G) :
    Nat.card H * Nat.card K = Nat.card (H ⊓ K : AddSubgroup G) * Nat.card (H ⊔ K : AddSubgroup G) := by
  have hi := card_mul_relIndex_of_le (H ⊓ K) H inf_le_left
  rw [AddSubgroup.inf_relIndex_left] at hi
  have hs := card_mul_relIndex_of_le K (H ⊔ K) le_sup_right
  rw [AddSubgroup.relIndex_sup_right] at hs
  calc Nat.card H * Nat.card K = (Nat.card (H ⊓ K : AddSubgroup G) * K.relIndex H) * Nat.card K :=
        congrArg (fun n => n * Nat.card K) hi.symm
     _ = Nat.card (H ⊓ K : AddSubgroup G) * (Nat.card K * K.relIndex H) := by ac_rfl
     _ = _ := congrArg (fun n => Nat.card (H ⊓ K : AddSubgroup G) * n) hs

/-- Supermodularity of the number of compatible colours, including isolated
vertices. The equality on union is exact; on intersection the subgroup sum
only has to embed into the compatible colours. -/
theorem colour_count_lattice (q : ℕ) [NeZero q] (A B : Finset (V × V)) [DecidableEq V] :
    q ^ Fintype.card (Component A) * q ^ Fintype.card (Component B) ≤
      q ^ Fintype.card (Component (A ∩ B)) * q ^ Fintype.card (Component (A ∪ B)) := by
  classical
  simp only [← card_colourGroup]
  have hUnion : colourGroup q (A ∪ B) = colourGroup q A ⊓ colourGroup q B := by
    ext σ
    change (∀ e ∈ A ∪ B, σ e.1 = σ e.2) ↔
      (∀ e ∈ A, σ e.1 = σ e.2) ∧ (∀ e ∈ B, σ e.1 = σ e.2)
    constructor
    · exact fun h => ⟨fun e he => h e (mem_union_left _ he), fun e he => h e (mem_union_right _ he)⟩
    · exact fun ⟨h,k⟩ e he => (mem_union.mp he).elim (h e) (k e)
  have hIncl : colourGroup q A ⊔ colourGroup q B ≤ colourGroup q (A ∩ B) :=
    sup_le (colourGroup_antitone q inter_subset_left) (colourGroup_antitone q inter_subset_right)
  have hCard := Nat.card_le_card_of_injective
    (Set.inclusion (show (↑(colourGroup q A ⊔ colourGroup q B) : Set (V → Fin q)) ⊆ _ from hIncl))
    (Set.inclusion_injective _)
  rw [card_mul_card_eq_inf_sup, ← hUnion, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ hCard

private theorem activity_nonneg {β : V × V → ℝ} (hβ : ∀ e, 0 ≤ β e) (A : Finset (V × V)) :
    0 ≤ activity β A := Finset.prod_nonneg fun e _ => sub_nonneg.mpr (Real.one_le_exp (hβ e))

private theorem fk_nonneg (q : ℕ) {β : V × V → ℝ} (hβ : ∀ e, 0 ≤ β e) (A : Finset (V × V)) :
    0 ≤ fkWeight q β A := mul_nonneg (activity_nonneg hβ A) (by positivity)

theorem fkWeight_lattice (q : ℕ) [NeZero q] {β : V × V → ℝ} (hβ : ∀ e, 0 ≤ β e)
    (A B : Finset (V × V)) [DecidableEq V] :
    fkWeight q β A * fkWeight q β B ≤ fkWeight q β (A ∩ B) * fkWeight q β (A ∪ B) := by
  classical
  have hc : (q : ℝ) ^ Fintype.card (Component A) * (q : ℝ) ^ Fintype.card (Component B) ≤
      (q : ℝ) ^ Fintype.card (Component (A ∩ B)) * (q : ℝ) ^ Fintype.card (Component (A ∪ B)) := by
    exact_mod_cast colour_count_lattice q A B
  have ha : activity β A * activity β B = activity β (A ∩ B) * activity β (A ∪ B) := by
    rw [mul_comm (activity β (A ∩ B))]
    exact (Finset.prod_union_inter (f := fun e => Real.exp (β e) - 1)).symm
  unfold fkWeight
  rw [mul_mul_mul_comm (activity β A), mul_mul_mul_comm (activity β (A ∩ B)), ← ha]
  exact mul_le_mul_of_nonneg_left hc (mul_nonneg (activity_nonneg hβ A) (activity_nonneg hβ B))

private theorem sum_restrict {E : Type*} [Fintype E] [DecidableEq E]
    (K : Finset E) (f : Finset E → ℝ) :
    (∑ F : Finset E, if F ⊆ K then f F else 0) = ∑ F ∈ K.powerset, f F := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext F
  simp

theorem free_weighted_sum_mono {E : Type*} [Fintype E] [DecidableEq E]
    (w f : Finset E → ℝ) (h₀ : ∀ A, 0 ≤ w A) (hf₀ : ∀ A, 0 ≤ f A)
    (hLat : ∀ A B, w A * w B ≤ w (A ∩ B) * w (A ∪ B)) (hf : Monotone f)
    {J K : Finset E} (hJK : J ⊆ K) :
    (∑ A ∈ J.powerset, w A * f A) * (∑ A ∈ K.powerset, w A) ≤
    (∑ A ∈ J.powerset, w A) * ∑ A ∈ K.powerset, w A * f A := by
  classical
  let fw (S : Finset E) (A : Finset E) : ℝ := if A ⊆ S then w A else 0
  let ff (S : Finset E) (A : Finset E) : ℝ := if A ⊆ S then w A * f A else 0
  have hwS (S : Finset E) : 0 ≤ fw S := by
    intro A
    dsimp [fw]
    split <;> simp [h₀]
  have hfS (S : Finset E) : 0 ≤ ff S := by
    intro A
    dsimp [ff]
    split <;> simp [mul_nonneg (h₀ A) (hf₀ A)]
  have h := four_functions_theorem_univ (ff J) (fw K) (fw J) (ff K)
    (hfS _) (hwS _) (hwS _) (hfS _) (by
      intro A B
      change ff J A * fw K B ≤ fw J (A ∩ B) * ff K (A ∪ B)
      by_cases hA : A ⊆ J <;> by_cases hB : B ⊆ K
      · have hI : A ∩ B ⊆ J := inter_subset_left.trans hA
        have hU : A ∪ B ⊆ K := union_subset (hA.trans hJK) hB
        simp only [fw, ff, if_pos hA, if_pos hB, if_pos hI, if_pos hU]
        calc (w A * f A) * w B = (w A * w B) * f A := by ring
           _ ≤ (w (A ∩ B) * w (A ∪ B)) * f (A ∪ B) :=
             mul_le_mul (hLat _ _) (hf subset_union_left) (hf₀ _) (mul_nonneg (h₀ _) (h₀ _))
           _ = _ := by ring
      · rw [show fw K B = 0 by simp [fw, hB], mul_zero]
        exact mul_nonneg (hwS J _) (hfS K _)
      · rw [show ff J A = 0 by simp [ff, hA], zero_mul]
        exact mul_nonneg (hwS J _) (hfS K _)
      · rw [show ff J A = 0 by simp [ff, hA], zero_mul]
        exact mul_nonneg (hwS J _) (hfS K _))
  simpa only [fw, ff, sum_restrict] using h

/-- Adding free bonds increases pair connectivity, with precisely the FK
weight of the physical finite Potts expansion. -/
theorem free_connectivity_mono {q : ℕ} (hq : 2 ≤ q) {β : V × V → ℝ}
    (hβ : ∀ e, 0 ≤ β e) {J K : Finset (V × V)} (hJK : J ⊆ K) (x y : V) :
    (∑ A ∈ J.powerset, if port A x = port A y then fkWeight q β A else 0) /
      (∑ A ∈ J.powerset, fkWeight q β A) ≤
    (∑ A ∈ K.powerset, if port A x = port A y then fkWeight q β A else 0) /
      ∑ A ∈ K.powerset, fkWeight q β A := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let f (A : Finset (V × V)) : ℝ := if port A x = port A y then 1 else 0
  have hf0 (A : Finset (V × V)) : 0 ≤ f A := by dsimp [f]; split <;> norm_num
  have hf : Monotone f := by
    intro A B hAB
    by_cases heq : port A x = port A y
    · let j : Component A → Component B := Quot.lift (port B) (fun _ _ hab => Quot.sound (hAB hab))
      have hh : port B x = port B y := congrArg j heq
      simp [f, heq, hh]
    · simpa [f, heq] using hf0 B
  have hD (S : Finset (V × V)) : 0 < ∑ A ∈ S.powerset, fkWeight q β A := by
    apply Finset.sum_pos' (fun A _ => fk_nonneg q hβ A)
    refine ⟨∅, by simp, ?_⟩
    simp only [fkWeight, activity, prod_empty, one_mul]
    positivity
  apply (div_le_div_iff₀ (hD J) (hD K)).mpr
  have hLat : ∀ A B : Finset (V × V),
      fkWeight q β A * fkWeight q β B ≤
        fkWeight q β (A ∩ B) * fkWeight q β (A ∪ B) :=
    fun A B => fkWeight_lattice q hβ A B
  have h := free_weighted_sum_mono _ f (fk_nonneg q hβ) hf0 hLat hf hJK
  simpa only [f, mul_ite, mul_one, mul_zero, mul_comm (∑ A ∈ J.powerset, fkWeight q β A)] using h

#print axioms fkWeight_lattice
#print axioms free_connectivity_mono
end IsingScaling.Potts.EdwardsSokal
