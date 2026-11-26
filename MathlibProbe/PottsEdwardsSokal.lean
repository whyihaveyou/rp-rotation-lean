import MathlibProbe.PottsBondReflection
import Mathlib.Data.Fintype.Quotient
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The Edwards–Sokal identification on a finite labelled bond set with
free boundary. An open component includes an isolated vertex. Both the
spin partition function and its simplex-marked numerator are expanded. -/

noncomputable section
open Finset
open scoped BigOperators Classical

namespace IsingScaling.Potts.EdwardsSokal

variable {V : Type*} [Fintype V]

/-- A quotient by the open bonds automatically takes their reflexive,
symmetric, transitive closure. -/
def Component (F : Finset (V × V)) := Quot (fun a b : V => (a,b) ∈ F)

def port (F : Finset (V × V)) (v : V) : Component F := Quot.mk _ v

omit [Fintype V] in
theorem port_eq_iff_connected (F : Finset (V × V)) (u v : V) :
    port F u = port F v ↔ Relation.EqvGen (fun a b : V => (a,b) ∈ F) u v :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

instance (F : Finset (V × V)) : Finite (Component F) :=
  Finite.of_surjective (port F) Quot.mk_surjective

noncomputable instance (F : Finset (V × V)) : Fintype (Component F) :=
  Fintype.ofFinite _

def Compatible {q : ℕ} (F : Finset (V × V)) (σ : V → Fin q) : Prop :=
  ∀ e ∈ F, σ e.1 = σ e.2

/-- Free compatible spins and unrestricted component colours are in bijection. -/
def componentColorEquiv (F : Finset (V × V)) (q : ℕ) :
    {σ : V → Fin q // Compatible F σ} ≃ (Component F → Fin q) where
  toFun σ := Quot.lift σ.val (fun a b h => σ.property (a,b) h)
  invFun c := ⟨fun v => c (port F v), fun e he => congrArg c (Quot.sound he)⟩
  left_inv _ := rfl
  right_inv c := by
    funext v
    exact Quot.inductionOn v (fun _ => rfl)

def simplexMark {q : ℕ} (a b : Fin q) : ℝ :=
  ((if a = b then (q : ℝ) else 0) - 1) / ((q : ℝ) - 1)

private theorem mark_self {q : ℕ} (hq : 2 ≤ q) (a : Fin q) : simplexMark a a = 1 := by
  have : (q : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (q : ℤ) - 1 ≠ 0 by omega)
  simp [simplexMark, this]

private theorem sum_mark {q : ℕ} (b : Fin q) : (∑ a : Fin q, simplexMark a b) = 0 := by
  classical
  simp [simplexMark, ← Finset.sum_div, Finset.sum_sub_distrib]

private theorem sum_component_mark {C : Type*} [Fintype C] {q : ℕ} (hq : 2 ≤ q)
    (a b : C) :
    (∑ c : C → Fin q, simplexMark (c a) (c b)) =
      (if a = b then (q : ℝ) ^ Fintype.card C else 0) := by
  classical
  by_cases heq : a = b
  · subst b
    simp [mark_self hq]
  · rw [if_neg heq, ← Equiv.sum_comp (Equiv.funSplitAt a (Fin q)).symm
      (fun c => simplexMark (c a) (c b)), Fintype.sum_prod_type, Finset.sum_comm]
    simp [Equiv.funSplitAt_symm_apply, Ne.symm heq, sum_mark]

private theorem restrict_sum {q : ℕ} (F : Finset (V × V)) (f : (V → Fin q) → ℝ) :
    (∑ σ, (if Compatible F σ then f σ else 0)) =
      ∑ c : Component F → Fin q, f (fun x => c (port F x)) := by
  classical
  rw [← Finset.sum_filter]
  calc
    _ = ∑ σ : {s : V → Fin q // Compatible F s}, f σ.val :=
      Finset.sum_subtype _ (by simp) f
    _ = _ := Fintype.sum_equiv (componentColorEquiv F q)
      (fun σ => f σ.val) (fun c => f (fun x => c (port F x))) (fun _ => rfl)

def spinWeight {q : ℕ} (K : Finset (V × V)) (β : V × V → ℝ) (σ : V → Fin q) : ℝ :=
  ∏ e ∈ K, IsingScaling.Potts.edgeWeight (β e) (σ e.1) (σ e.2)

def activity (β : V × V → ℝ) (F : Finset (V × V)) : ℝ :=
  ∏ e ∈ F, (Real.exp (β e) - 1)

def fkWeight (q : ℕ) (β : V × V → ℝ) (F : Finset (V × V)) : ℝ :=
  activity β F * (q : ℝ) ^ Fintype.card (Component F)

private theorem expand_spin {q : ℕ} (K : Finset (V × V)) (β : V × V → ℝ) (σ : V → Fin q) :
    spinWeight K β σ = ∑ F ∈ K.powerset, if Compatible F σ then activity β F else 0 := by
  classical
  let d (e : V × V) : ℝ := if σ e.1 = σ e.2 then Real.exp (β e) - 1 else 0
  have hf (e : V × V) :
      IsingScaling.Potts.edgeWeight (β e) (σ e.1) (σ e.2) = 1 + d e := by
    by_cases h : σ e.1 = σ e.2 <;> simp [IsingScaling.Potts.edgeWeight, d, h]
  simp only [spinWeight, hf, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro F _
  by_cases h : Compatible F σ
  · rw [if_pos h]
    exact prod_congr rfl (fun e he => if_pos (h e he))
  · rw [if_neg h]
    unfold Compatible at h
    push_neg at h
    obtain ⟨e, he, hh⟩ := h
    exact Finset.prod_eq_zero he (if_neg hh)

private theorem expand_observable {q : ℕ} (K : Finset (V × V)) (β : V × V → ℝ)
    (f : (V → Fin q) → ℝ) :
    (∑ σ, spinWeight K β σ * f σ) =
      ∑ F ∈ K.powerset, activity β F *
        ∑ c : Component F → Fin q, f (fun v => c (port F v)) := by
  classical
  simp_rw [expand_spin, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F _
  rw [← restrict_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : Compatible F σ <;> simp [h]

theorem partition_eq (q : ℕ) (K : Finset (V × V)) (β : V × V → ℝ) :
    (∑ σ : V → Fin q, spinWeight K β σ) = ∑ F ∈ K.powerset, fkWeight q β F := by
  classical
  simpa [fkWeight, Fintype.card_fun] using expand_observable K β (fun _ : V → Fin q => (1 : ℝ))

theorem marked_partition_eq {q : ℕ} (hq : 2 ≤ q) (K : Finset (V × V)) (β : V × V → ℝ)
    (x y : V) :
    (∑ σ : V → Fin q, spinWeight K β σ * simplexMark (σ x) (σ y)) =
      ∑ F ∈ K.powerset, if port F x = port F y then fkWeight q β F else 0 := by
  classical
  rw [expand_observable K β (fun σ : V → Fin q => simplexMark (σ x) (σ y))]
  apply Finset.sum_congr rfl
  intro F _
  rw [sum_component_mark hq]
  by_cases h : port F x = port F y <;> simp [fkWeight, h]

/-- The normalized free Potts simplex insertion equals normalized FK connectivity. -/
theorem simplex_correlation_eq_connectivity {q : ℕ} (hq : 2 ≤ q) (K : Finset (V × V))
    (β : V × V → ℝ) (x y : V) :
    (∑ σ : V → Fin q, spinWeight K β σ * simplexMark (σ x) (σ y)) /
        (∑ σ : V → Fin q, spinWeight K β σ) =
      (∑ F ∈ K.powerset, if port F x = port F y then fkWeight q β F else 0) /
        ∑ F ∈ K.powerset, fkWeight q β F := by
  rw [marked_partition_eq hq, partition_eq]

theorem fkWeight_nonneg (q : ℕ) (F : Finset (V × V)) (β : V × V → ℝ)
    (hβ : ∀ e ∈ F, 0 ≤ β e) : 0 ≤ fkWeight q β F := by
  exact mul_nonneg (prod_nonneg (fun e he => sub_nonneg.mpr (Real.one_le_exp (hβ e he))))
    (pow_nonneg (Nat.cast_nonneg q) _)

theorem fkPartition_pos {q : ℕ} (hq : 0 < q) (K : Finset (V × V)) (β : V × V → ℝ) :
    0 < ∑ F ∈ K.powerset, fkWeight q β F := by
  classical
  haveI : NeZero q := ⟨hq.ne'⟩
  rw [← partition_eq q]
  exact Finset.sum_pos (fun σ _ => Finset.prod_pos (fun e _ => Real.exp_pos _) )
    Finset.univ_nonempty

#print axioms simplex_correlation_eq_connectivity

end IsingScaling.Potts.EdwardsSokal
