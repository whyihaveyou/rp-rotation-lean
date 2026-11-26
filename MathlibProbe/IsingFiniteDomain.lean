import MathlibProbe.IsingFreePairLimit

/-! Free correlations on arbitrary induced finite subdomains. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators Topology
namespace IsingScaling

private lemma domain_sum_restrict_spin {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (e : V ↪ W) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : (V → Bool) → ℝ,
      (∑ σ : W → Bool, f (σ ∘ e)) = c * ∑ τ : V → Bool, f τ := by
  classical
  let D := {w : W // w ∉ Set.range e}
  let e' : V ⊕ D ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl D)).trans
      (Equiv.Set.sumCompl (Set.range e))
  let E : (W → Bool) ≃ ((V → Bool) × (D → Bool)) :=
    (e'.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  let : Fintype D := Fintype.ofFinite _
  refine ⟨Fintype.card (D → Bool), by exact_mod_cast Fintype.card_pos, ?_⟩
  intro f
  have he (σ : W → Bool) : (E σ).1 = σ ∘ e := rfl
  calc
    _ = ∑ σ : W → Bool, (fun k : (V → Bool) × (D → Bool) => f k.1) (E σ) := rfl
    _ = ∑ k : (V → Bool) × (D → Bool), f k.1 :=
      Equiv.sum_comp E (fun k : (V → Bool) × (D → Bool) => f k.1)
    _ = _ := by simp [Fintype.sum_prod_type, nsmul_eq_mul, Finset.mul_sum]

private def domainBoxBonds (L : ℕ) : Finset (BoxSite L × BoxSite L) :=
  Finset.univ.filter fun e => latticeDistance e.1 e.2 = 1

private lemma domainCubeWeight_eq (β L) (σ : Spin L) :
    bondWeight (domainBoxBonds L) (fun _ => β/2) σ = gibbsWeight β L σ := by
  unfold bondWeight gibbsWeight interaction domainBoxBonds bondScore
  apply congrArg Real.exp
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [← mul_div_assoc, ← div_mul_eq_mul_div]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro y _
  split <;> simp_all

private lemma domainBoxCorrelation_graphPair (β L) (x y : BoxSite L) :
    boxCorrelation β L x y = graphPair (domainBoxBonds L) (fun _ => β/2) (x,y) := by
  unfold boxCorrelation graphPair
  simp only [domainCubeWeight_eq, bondScore, mul_assoc]

/-- The free correlation on any finite list of distinct lattice vertices,
using the induced nearest-neighbor bonds. -/
def volumePair {V : Type*} [Fintype V] [DecidableEq V] (β : ℝ) (loc : V → Site) (x y : V) : ℝ :=
  graphPair (Finset.univ.filter (fun e : V×V => latticeDistance (loc e.1) (loc e.2) = 1))
    (fun _ => β/2) (x,y)

theorem volumePair_cube (β : ℝ) (L : ℕ) (x y : BoxSite L) :
    volumePair β Subtype.val x y = boxCorrelation β L x y := (domainBoxCorrelation_graphPair ..).symm

/-- Finite-volume comparison for an arbitrary induced subdomain; isolated
spins outside the embedded subgraph are summed in both normalizations. -/
theorem volumePair_embed {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (u : V → Site) (v : W → Site) (e : V ↪ W) (he : ∀ w, v (e w)=u w)
    {β : ℝ} (hβ : 0≤β) (x y : V) :
    volumePair β u x y ≤ volumePair β v (e x) (e y) := by
  classical
  let A := Finset.univ.filter (fun a : V×V => latticeDistance (u a.1) (u a.2) = 1)
  let B := Finset.univ.filter (fun a : W×W => latticeDistance (v a.1) (v a.2) = 1)
  let K := A.map (e.prodMap e)
  have hKB : K⊆B := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hq
    change (e a.1,e a.2) ∈ B
    simpa only [A,B,Finset.mem_filter,Finset.mem_univ,true_and,he] using ha
  have HW (σ : W → Bool) :
      bondWeight K (fun _ => β/2) σ = bondWeight A (fun _ => β/2) (σ ∘ e) := by
    unfold bondWeight
    rw [show K=A.map (e.prodMap e) from rfl, Finset.sum_map]; rfl
  have H : graphPair K (fun _ => β/2) (e x,e y) = graphPair A (fun _ => β/2) (x,y) := by
    obtain ⟨C,hC,hh⟩ := domain_sum_restrict_spin e
    unfold graphPair
    simp only [HW]
    have h1 := hh (fun τ => bondWeight A (fun _ => β/2) τ * bondScore (x,y) τ)
    have h2 := hh (bondWeight A (fun _ => β/2))
    change (∑ σ : W → Bool, bondWeight A _ (σ ∘ e) * bondScore (x,y) (σ ∘ e)) / _ = _
    rw [h2,h1]; field_simp
  change graphPair A _ _ ≤ graphPair B _ _
  rw [← H]
  exact graphPair_mono hKB _ (by intro; positivity) _

end IsingScaling
