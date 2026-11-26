import MathlibProbe.PottsFreeFKLimit
import MathlibProbe.PottsBondDomainEmbedding
import Mathlib.Logic.Equiv.Set

/-! # Free FK comparison for increasing edge observables

The finite law has weights `(exp β − 1)^|F| q^k(F)` for a constant
coupling, with isolated vertices included in the component count. Adding
vertices disjoint from all available edges contributes the same factor to
every term. Representatives of unordered edges may be reversed separately
when embedding the graph into a larger one.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace IsingScaling.Potts.EdwardsSokal

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Expectation of an observable of the open edge set in the finite free law. -/
def freeFKExpectation (q : ℕ) (J : Finset (V × V)) (β : V × V → ℝ)
    (f : Finset (V × V) → ℝ) : ℝ :=
  (∑ F ∈ J.powerset, fkWeight q β F * f F) / ∑ F ∈ J.powerset, fkWeight q β F

/-- Domain monotonicity on a fixed finite vertex set. -/
theorem freeFKExpectation_mono {q : ℕ} (hq : 0 < q) {J K : Finset (V × V)}
    (hJK : J ⊆ K) {β : V × V → ℝ} (hβ : ∀ a, 0 ≤ β a)
    (f : Finset (V × V) → ℝ) (hf0 : ∀ F, 0 ≤ f F) (hf : Monotone f) :
    freeFKExpectation q J β f ≤ freeFKExpectation q K β f := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  apply (div_le_div_iff₀ (fkPartition_pos hq J β) (fkPartition_pos hq K β)).mpr
  simpa only [mul_comm (∑ F ∈ J.powerset, fkWeight q β F)] using
    free_weighted_sum_mono (fkWeight q β) f
      (fun F => fkWeight_nonneg q F β (fun a _ => hβ a)) hf0
      (fun A B => fkWeight_lattice q hβ A B) hf hJK

/-- The quotient by open edges of the enlarged graph is the old quotient
plus one singleton for each vertex outside the embedded vertex set. -/
def componentEquivEmbedding (e : V ↪ W) (ρ : (V × V) ↪ (W × W))
    (F : Finset (V × V))
    (hρ : ∀ a ∈ F, ρ a = (e a.1,e a.2) ∨ ρ a = (e a.2,e a.1)) :
    Component (F.map ρ) ≃ Component F ⊕ ↥((Set.range e)ᶜ : Set W) := by
  classical
  let D := ((Set.range e)ᶜ : Set W)
  let s : V ⊕ D ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl D)).trans
      (Equiv.Set.sumCompl (Set.range e))
  have sl (v : V) : s (Sum.inl v) = e v := rfl
  have sr (w : D) : s (Sum.inr w) = w.val := rfl
  let lift (w : W) : Component F ⊕ D := Sum.map (port F) id (s.symm w)
  have hl (v : V) : lift (e v) = Sum.inl (port F v) := by
    simp only [lift, ← sl, Equiv.symm_apply_apply, Sum.map_inl]
  have hr (w : D) : lift w.val = Sum.inr w := by
    simp only [lift, ← sr, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
  have hforward {u v : W} (h : (u,v) ∈ F.map ρ) : lift u = lift v := by
    obtain ⟨a,ha,h⟩ := mem_map.mp h
    have hport : port F a.1 = port F a.2 := Quot.sound ha
    rcases hρ a ha with hdir | hrev
    · rw [hdir] at h
      cases h
      simp only [hl, hport]
    · rw [hrev] at h
      cases h
      simp only [hl, hport]
  let forward : Component (F.map ρ) → Component F ⊕ D :=
    Quot.lift lift (fun _ _ h => hforward h)
  have hback {u v : V} (h : (u,v) ∈ F) :
      port (F.map ρ) (e u) = port (F.map ρ) (e v) := by
    have hm : ρ (u,v) ∈ F.map ρ := mem_map.mpr ⟨_,h,rfl⟩
    rcases hρ (u,v) h with hdir | hrev
    · exact Quot.sound (hdir ▸ hm)
    · exact (Quot.sound (hrev ▸ hm)).symm
  let backward : Component F ⊕ D → Component (F.map ρ) :=
    Sum.elim (Quot.lift (fun u => port (F.map ρ) (e u)) (fun _ _ h => hback h))
      (fun w => port (F.map ρ) w.val)
  refine ⟨forward, backward, ?_, ?_⟩
  · intro c
    induction c using Quot.inductionOn with
    | _ w =>
      change backward (lift w) = port _ w
      obtain ⟨v,rfl⟩ := s.surjective w
      rcases v with v | w
      · rw [sl, hl]
        rfl
      · rw [sr, hr]
        rfl
  · rintro (c | w)
    · induction c using Quot.inductionOn with
      | _ v => exact hl v
    · exact hr w

theorem card_component_map (e : V ↪ W) (ρ : (V × V) ↪ (W × W)) (F : Finset (V × V))
    (hρ : ∀ a ∈ F, ρ a = (e a.1,e a.2) ∨ ρ a = (e a.2,e a.1)) :
    Fintype.card (Component (F.map ρ)) =
      Fintype.card (Component F) + (Fintype.card W - Fintype.card V) := by
  classical
  rw [Fintype.card_congr (componentEquivEmbedding e ρ F hρ), Fintype.card_sum,
    Fintype.card_compl_set, Fintype.card_range e]

/-- The extra isolated vertices give a configuration-independent factor
in the unnormalized free weights, including at zero bond activity. -/
theorem fkWeight_map (q : ℕ) (e : V ↪ W) (ρ : (V × V) ↪ (W × W)) (β : W × W → ℝ)
    (F : Finset (V × V))
    (hρ : ∀ a ∈ F, ρ a = (e a.1,e a.2) ∨ ρ a = (e a.2,e a.1)) :
    fkWeight q β (F.map ρ) =
      (q : ℝ) ^ (Fintype.card W - Fintype.card V) * fkWeight q (β ∘ ρ) F := by
  simp only [fkWeight, activity, Finset.prod_map, Function.comp_apply,
    card_component_map e ρ F hρ, pow_add]
  ring

private theorem powerset_mapped {A B : Type*} (ρ : A ↪ B) (J : Finset A) :
    (J.map ρ).powerset = J.powerset.map (Finset.mapEmbedding ρ).toEmbedding := by
  classical
  apply Finset.eq_of_subset_of_card_le _ (by simp)
  intro S hS
  have hsub := mem_powerset.mp hS
  let F := J.filter fun a => ρ a ∈ S
  refine mem_map.mpr ⟨F, mem_powerset.mpr (filter_subset _ _), ?_⟩
  change F.map ρ = S
  ext b
  constructor
  · rintro hb
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hb
    exact (mem_filter.mp ha).2
  · intro hb
    obtain ⟨a,ha,rfl⟩ := mem_map.mp (hsub hb)
    exact mem_map.mpr ⟨a,mem_filter.mpr ⟨ha,hb⟩,rfl⟩

/-- Adding isolated sites and choosing representatives of the same unordered
bonds leaves every normalized edge observable unchanged. -/
theorem freeFKExpectation_map {q : ℕ} (hq : 0 < q) (e : V ↪ W)
    (ρ : (V × V) ↪ (W × W)) (J : Finset (V × V)) (β : W × W → ℝ)
    (hρ : ∀ a ∈ J, ρ a = (e a.1,e a.2) ∨ ρ a = (e a.2,e a.1))
    (f : Finset (W × W) → ℝ) :
    freeFKExpectation q (J.map ρ) β f =
      freeFKExpectation q J (β ∘ ρ) (fun F => f (F.map ρ)) := by
  classical
  let C := (q : ℝ) ^ (Fintype.card W - Fintype.card V)
  have hW {F : Finset (V × V)} (hF : F ∈ J.powerset) :
      fkWeight q β (F.map ρ) = C * fkWeight q (β ∘ ρ) F :=
    fkWeight_map q e ρ β F (fun a ha => hρ a ((mem_powerset.mp hF) ha))
  simp only [freeFKExpectation, powerset_mapped ρ J, Finset.sum_map,
    RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  have hnum : (∑ F ∈ J.powerset, fkWeight q β (F.map ρ) * f (F.map ρ)) =
      C * ∑ F ∈ J.powerset, fkWeight q (β ∘ ρ) F * f (F.map ρ) := by
    rw [Finset.mul_sum]
    exact sum_congr rfl (fun F hF => by rw [hW hF, mul_assoc])
  have hden : (∑ F ∈ J.powerset, fkWeight q β (F.map ρ)) =
      C * ∑ F ∈ J.powerset, fkWeight q (β ∘ ρ) F := by
    rw [Finset.mul_sum]
    exact sum_congr rfl (fun _ hF => hW hF)
  rw [hnum,hden,mul_div_mul_left _ _ (by exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne'))]

/-- Comparison of arbitrary nonnegative increasing observables when both
the finite vertex set and available free bonds grow. -/
theorem freeFKExpectation_mono_embedding {q : ℕ} (hq : 0 < q) (e : V ↪ W)
    (ρ : (V × V) ↪ (W × W)) {J : Finset (V × V)} {K : Finset (W × W)}
    (hρ : ∀ a ∈ J, ρ a = (e a.1,e a.2) ∨ ρ a = (e a.2,e a.1))
    (hJK : J.map ρ ⊆ K) {β : W × W → ℝ} (hβ : ∀ a, 0 ≤ β a)
    (f : Finset (W × W) → ℝ) (hf0 : ∀ F, 0 ≤ f F) (hf : Monotone f) :
    freeFKExpectation q J (β ∘ ρ) (fun F => f (F.map ρ)) ≤ freeFKExpectation q K β f := by
  rw [← freeFKExpectation_map hq e ρ J β hρ f]
  exact freeFKExpectation_mono hq hJK hβ f hf0 hf

#print axioms freeFKExpectation_mono_embedding

end IsingScaling.Potts.EdwardsSokal

namespace IsingScaling.Potts.SiteBox

/-- The actual representatives in `cubeBonds` depend on the finite cube's
ordering. On unordered bonds the vertex inclusion preserves each bond,
while on ordered pairs it may reverse the two endpoints. -/
theorem cubeBonds_mono_embedding {M N : ℕ} (hMN : M ≤ N) :
    ∃ (e : BoxSite M ↪ BoxSite N) (ρ : (BoxSite M × BoxSite M) ↪ (BoxSite N × BoxSite N)),
      (∀ x, (e x).val = x.val) ∧
      (∀ a ∈ cubeBonds M, ρ a = (e a.1,e a.2) ∨ ρ a = (e a.2,e a.1)) ∧
      (cubeBonds M).map ρ ⊆ cubeBonds N := by
  have h : cube M ⊆ cube N := by
    intro x hx
    simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
    intro i
    have hi := hx i
    omega
  simpa only [FreeBond.domainBonds_cube] using FreeBond.domainBonds_mono_embedding h

#print axioms cubeBonds_mono_embedding

end IsingScaling.Potts.SiteBox
