import MathlibProbe.PottsFreeCubeConnectivity

/-! A free graph on a finite set of lattice sites contains all induced
nearest-neighbour bonds. Each unordered edge has one oriented representative.
An inclusion of domains preserves the physical bonds even when their finite
enumerations choose opposite representatives. -/

noncomputable section
open Finset
open scoped Classical
namespace IsingScaling.Potts.FreeBond

def domainBonds (U : Finset Site) : Finset (↥U × ↥U) :=
  univ.filter fun e =>
    Fintype.equivFin (↥U) e.1 < Fintype.equivFin (↥U) e.2 ∧
      latticeDistance e.1.val e.2.val = 1

@[simp] theorem domainBonds_cube (L : ℕ) : domainBonds (cube L) = SiteBox.cubeBonds L := by
  ext a
  simp only [domainBonds, SiteBox.cubeBonds, mem_filter, mem_univ, true_and]
  rfl

theorem domainBonds_mono_embedding {U V : Finset Site} (hUV : U ⊆ V) :
    ∃ (e : ↥U ↪ ↥V) (ρ : (↥U × ↥U) ↪ (↥V × ↥V)),
      (∀ x, (e x).val = x.val) ∧
      (∀ a ∈ domainBonds U, ρ a = (e a.1, e a.2) ∨ ρ a = (e a.2, e a.1)) ∧
      (domainBonds U).map ρ ⊆ domainBonds V := by
  let e : ↥U ↪ ↥V := {
    toFun x := ⟨x.val, hUV x.property⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun w : ↥V => w.val) h) }
  let I := Fintype.equivFin (↥U)
  let J := Fintype.equivFin (↥V)
  let flip (a : ↥U × ↥U) : Prop :=
    (I a.1 < I a.2 ∧ J (e a.2) < J (e a.1)) ∨ (I a.2 < I a.1 ∧ J (e a.1) < J (e a.2))
  have flip_swap (a : ↥U × ↥U) : flip a.swap ↔ flip a := or_comm
  let turn (a : ↥U × ↥U) := if flip a then a.swap else a
  have hinv : Function.Involutive turn := by
    intro a
    by_cases h : flip a
    · have h' := (flip_swap a).mpr h
      simp [turn, h, h']
    · simp [turn, h]
  let ρ := (⟨turn, hinv.injective⟩ : (↥U × ↥U) ↪ _).trans (e.prodMap e)
  have forward (a : ↥U × ↥U) (h : ¬ flip a) : ρ a = (e a.1, e a.2) := by
    change (e (turn a).1, e (turn a).2) = _
    simp [turn, h]
  have reverse (a : ↥U × ↥U) (h : flip a) : ρ a = (e a.2, e a.1) := by
    change (e (turn a).1, e (turn a).2) = _
    simp [turn, h]
  refine ⟨e, ρ, fun _ => rfl, fun a _ => ?_, ?_⟩
  · by_cases h : flip a
    · exact Or.inr (reverse a h)
    · exact Or.inl (forward a h)
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
    have hsmall : I a.1 < I a.2 ∧ latticeDistance a.1.val a.2.val = 1 := (mem_filter.mp ha).2
    have hne : J (e a.1) ≠ J (e a.2) :=
      J.injective.ne (e.injective.ne (fun h => hsmall.1.ne (congrArg I h)))
    rcases lt_or_gt_of_ne hne with h | h
    · have hf : ¬ flip a := fun hf =>
        hf.elim (fun z => h.not_gt z.2) (fun z => hsmall.1.not_gt z.1)
      rw [forward a hf]
      exact mem_filter.mpr ⟨mem_univ _, h, hsmall.2⟩
    · rw [reverse a (Or.inl ⟨hsmall.1, h⟩)]
      have hd : latticeDistance a.2.val a.1.val = latticeDistance a.1.val a.2.val := by
        unfold latticeDistance
        apply sum_congr rfl
        intro i _
        rw [← neg_sub (a.1.val i) (a.2.val i), Int.natAbs_neg]
      exact mem_filter.mpr ⟨mem_univ _, h, hd.trans hsmall.2⟩

#print axioms domainBonds_mono_embedding
end IsingScaling.Potts.FreeBond
