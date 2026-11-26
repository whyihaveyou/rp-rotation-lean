import MathlibProbe.PottsFreeFKLimit
import MathlibProbe.PottsPhysicalSiteReflection
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod
import Mathlib.Topology.Order.MonotoneConvergence

/-! The canonical stationary scalar of the free integer Potts model.
An embedding of one cube into another preserves the spin pair before the
extra edges are inserted. Free FK comparison then gives the growing-box
inequality. Two translated cube inclusions identify the stationary limit. -/
noncomputable section
set_option maxHeartbeats 1000000
open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace IsingScaling.Potts.SiteBox
open EdwardsSokal

def directedBonds (L : ℕ) : Finset (BoxSite L × BoxSite L) :=
  univ.filter fun e => latticeDistance e.1 e.2 = 1

private theorem energy_directed {q L : ℕ} (σ : Config q L) :
    energy equalColour σ =
      (∑ e ∈ directedBonds L, equalColour (σ e.1) (σ e.2)) / 2 := by
  unfold energy bondTerm directedBonds
  rw [Finset.sum_filter, Fintype.sum_prod_type]

private theorem weight_directed {q L : ℕ} (β : ℝ) (σ : Config q L) :
    weight equalColour β σ = spinWeight (directedBonds L) (fun _ => β / 2) σ := by
  unfold weight
  rw [energy_directed, ← mul_div_assoc, ← div_mul_eq_mul_div, Finset.mul_sum, Real.exp_sum]
  apply prod_congr rfl
  intro e he
  by_cases h : σ e.1 = σ e.2 <;> simp [equalColour, edgeWeight, h]

def graphScalar {V : Type*} [Fintype V] (q : ℕ) (J : Finset (V × V))
    (β : V × V → ℝ) (x y : V) : ℝ :=
  (∑ σ : V → Fin q, spinWeight J β σ * simplexMark (σ x) (σ y)) /
    (∑ σ : V → Fin q, spinWeight J β σ)

theorem marks_eq {q : ℕ} (a b : Fin q) : simplex a b = simplexMark a b := by
  by_cases h : a = b <;> simp [simplex, simplexMark, equalColour, h]

theorem sum_same_finite_type {α : Type*} {I J : Fintype α} (f : α → ℝ) :
    (@Finset.univ α I).sum f = (@Finset.univ α J).sum f := by
  rw [Subsingleton.elim I J]

theorem boxPair_directed {q L : ℕ} (β : ℝ) (x y : BoxSite L) :
    boxPair q β x y = graphScalar q (directedBonds L) (fun _ => β / 2) x y := by
  unfold boxPair graphScalar
  simp_rw [weight_directed, marks_eq]
  exact congrArg₂ (· / ·) (sum_same_finite_type _) (sum_same_finite_type _)

theorem graphScalar_mono {V : Type*} [Fintype V] {q : ℕ} (hq : 2 ≤ q)
    {J K : Finset (V × V)} (h : J ⊆ K) {β : V × V → ℝ} (hβ : ∀ e, 0 ≤ β e)
    (x y : V) : graphScalar q J β x y ≤ graphScalar q K β x y := by
  unfold graphScalar
  rw [simplex_correlation_eq_connectivity hq, simplex_correlation_eq_connectivity hq]
  exact free_connectivity_mono hq hβ h x y

private theorem latticePair_nn_nonneg {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    (L : ℕ) (x y : Site) : 0 ≤ latticePair q β L x y := by
  unfold latticePair
  split <;> try exact le_rfl
  split <;> try exact le_rfl
  rw [boxPair_directed]
  unfold graphScalar
  rw [simplex_correlation_eq_connectivity hq]
  apply div_nonneg _ (fkPartition_pos (by omega : 0 < q) _ _).le
  apply sum_nonneg
  intro A _
  split
  · exact fkWeight_nonneg _ _ _ (fun _ _ => div_nonneg hβ (by norm_num))
  · exact le_rfl

/-- Every assignment on the embedded vertex set has the same number of
extensions. This constant cancels in normalized expectations. -/
private theorem sum_restrict_colour {V W : Type*} [Fintype V] [Fintype W]
    {q : ℕ} [NeZero q] (e : V ↪ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (V → Fin q) → ℝ,
      (∑ σ : W → Fin q, f (σ ∘ e)) = C * ∑ τ : V → Fin q, f τ := by
  classical
  let D := {w : W // w ∉ Set.range e}
  let e' : V ⊕ D ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl D)).trans
      (Equiv.Set.sumCompl (Set.range e))
  let E : (W → Fin q) ≃ ((V → Fin q) × (D → Fin q)) :=
    (e'.symm.arrowCongr (Equiv.refl (Fin q))).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  let : Fintype D := Fintype.ofFinite _
  refine ⟨Fintype.card (D → Fin q), by exact_mod_cast Fintype.card_pos, ?_⟩
  intro f
  calc
    _ = ∑ σ : W → Fin q, (fun k : (V → Fin q) × (D → Fin q) => f k.1) (E σ) := rfl
    _ = ∑ k : (V → Fin q) × (D → Fin q), f k.1 :=
      Equiv.sum_comp E (fun k : (V → Fin q) × (D → Fin q) => f k.1)
    _ = _ := by simp [Fintype.sum_prod_type, nsmul_eq_mul, Finset.mul_sum]

theorem normalized_restriction {V W : Type*} [Fintype V] [Fintype W]
    {q : ℕ} [NeZero q] (e : V ↪ W) (f g : (V → Fin q) → ℝ)
    (I : Fintype (W → Fin q)) (J : Fintype (V → Fin q)) :
    (@Finset.univ _ I).sum (fun σ => f (σ ∘ e)) /
      (@Finset.univ _ I).sum (fun σ => g (σ ∘ e)) =
      (@Finset.univ _ J).sum f / (@Finset.univ _ J).sum g := by
  classical
  obtain ⟨C,hC,h⟩ := sum_restrict_colour (q := q) e
  have hsum (k : (V → Fin q) → ℝ) :
      (@Finset.univ _ I).sum (fun σ => k (σ ∘ e)) = C * (@Finset.univ _ J).sum k :=
    (sum_same_finite_type _).trans
      ((h k).trans (congrArg (fun z : ℝ => C*z) (sum_same_finite_type k)))
  exact (congrArg₂ (· / ·) (hsum f) (hsum g)).trans (mul_div_mul_left _ _ hC.ne')

theorem boxPair_mono_of_isometric_embedding {q L N : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    (e : BoxSite L ↪ BoxSite N) (hd : ∀ x y, latticeDistance (e x) (e y) = latticeDistance x y)
    (x y : BoxSite L) : boxPair q β x y ≤ boxPair q β (e x) (e y) := by
  classical
  have : NeZero q := ⟨by omega⟩
  let emb := e.prodMap e
  let J := (directedBonds L).map emb
  have hJ : J ⊆ directedBonds N := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
    exact mem_filter.mpr ⟨mem_univ _, (hd a.1 a.2).trans (mem_filter.mp ha).2⟩
  have hw (σ : Config q N) : spinWeight J (fun _ => β/2) σ = weight equalColour β (σ ∘ e) := by
    rw [weight_directed]
    unfold spinWeight
    rw [show J = (directedBonds L).map emb from rfl, Finset.prod_map]
    rfl
  have hsmall : graphScalar q J (fun _ => β/2) (e x) (e y) = boxPair q β x y := by
    unfold graphScalar boxPair
    simp only [hw]
    simp_rw [marks_eq]
    exact normalized_restriction e
      (fun σ : Config q L => weight equalColour β σ * simplexMark (σ x) (σ y)) (weight equalColour β) _ _
  rw [← hsmall, boxPair_directed]
  exact graphScalar_mono hq hJ (fun _ => div_nonneg hβ (by norm_num)) _ _

private def shiftBox (L N d : ℕ) (a : Site) (ha : ∀ i, (a i).natAbs ≤ d)
    (hLN : L+d ≤ N) : BoxSite L ↪ BoxSite N where
  toFun w := ⟨w.val + a, by
    have hw := w.property
    simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hw ⊢
    intro i
    change -(N:ℤ) ≤ w.val i + a i ∧ w.val i + a i ≤ N
    have hh := hw i
    have ha' := ha i
    omega⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val huv)

private theorem shiftBox_distance {L N d : ℕ} (a : Site) (ha : ∀ i, (a i).natAbs ≤ d)
    (hLN : L+d ≤ N) (u v : BoxSite L) :
    latticeDistance (shiftBox L N d a ha hLN u) (shiftBox L N d a ha hLN v) =
      latticeDistance u v := by
  unfold latticeDistance
  apply sum_congr rfl
  intro i _
  change (u.val i + a i - (v.val i + a i)).natAbs = _
  rw [add_sub_add_right_eq_sub]

private theorem shiftBox_val {L N d : ℕ} {a : Site} {ha : ∀ i, (a i).natAbs ≤ d}
    {hLN : L+d ≤ N} (u : BoxSite L) : ((shiftBox L N d a ha hLN) u).val = u.val + a := rfl

private theorem eventually_box (x : Site) : ∀ᶠ L : ℕ in atTop, x ∈ cube L := by
  filter_upwards [eventually_ge_atTop (∑ i, (x i).natAbs)] with L hL
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  omega

/-- Supremum of rooted simplex correlations on the actual centered free
cubes; the same function is the translated pair limit below. -/
def canonicalFreePair (q : ℕ) (β : ℝ) (z : Site) : ℝ := ⨆ L : ℕ, latticePair q β L z 0

private theorem rooted_tendsto {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) (z : Site) :
    Tendsto (fun L => latticePair q β L z 0) atTop (𝓝 (canonicalFreePair q β z)) := by
  apply tendsto_atTop_ciSup
  · intro L N hLN
    by_cases hz : z ∈ cube L
    · have h0 : (0 : Site) ∈ cube L := by simp [cube, Fintype.mem_piFinset]
      let Z : BoxSite L := ⟨z,hz⟩
      let O : BoxSite L := ⟨0,h0⟩
      have h := boxPair_mono_of_isometric_embedding hq hβ (shiftBox L N 0 0 (by simp) (by omega))
        (shiftBox_distance 0 _ _) Z O
      simpa only [← latticePair_inside, Z, O, shiftBox_val, add_zero] using h
    · simpa [latticePair, hz] using latticePair_nn_nonneg hq hβ N z 0
  · refine ⟨1, ?_⟩
    rintro t ⟨k,rfl⟩
    change latticePair q β k z 0 ≤ 1
    unfold latticePair
    split <;> try norm_num
    split <;> try norm_num
    exact (le_abs_self _).trans (abs_boxPair_le_one hq _ _ _)

/-- Along every integer radius of the centered free cubes, the original
Potts simplex two-site Gibbs expectations converge to this same stationary
kernel. The comparison uses translated cubes of radii L−d, L+d. -/
theorem canonicalFreePair_stationary {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    StationaryPairLimit q β id (canonicalFreePair q β) := by
  intro x y
  let d := ∑ i, (y i).natAbs
  have hy (i) : (y i).natAbs ≤ d :=
    Finset.single_le_sum (f := fun j => (y j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  have hmy (i) : ((-y) i).natAbs ≤ d := by simpa using hy i
  have hm := (rooted_tendsto hq hβ (x-y)).comp (Filter.tendsto_sub_atTop_nat d)
  have hp := (Filter.tendsto_add_atTop_iff_nat d).mpr (rooted_tendsto hq hβ (x-y))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm hp
  · filter_upwards [eventually_ge_atTop d, (Filter.tendsto_sub_atTop_nat d).eventually
      (eventually_box (x-y))] with L hL hxy
    have h0 : (0 : Site) ∈ cube (L-d) := by simp [cube, Fintype.mem_piFinset]
    let z : BoxSite (L-d) := ⟨x-y,hxy⟩
    let o : BoxSite (L-d) := ⟨0,h0⟩
    have h := boxPair_mono_of_isometric_embedding hq hβ (shiftBox (L-d) L d y hy (by omega))
      (shiftBox_distance y hy _) z o
    change latticePair q β (L-d) (x-y) 0 ≤ latticePair q β L x y
    simpa only [← latticePair_inside, z, o, shiftBox_val, sub_add_cancel, zero_add] using h
  · filter_upwards [eventually_box x, eventually_box y] with L hx hyL
    let a : BoxSite L := ⟨x,hx⟩
    let b : BoxSite L := ⟨y,hyL⟩
    have h := boxPair_mono_of_isometric_embedding hq hβ (shiftBox L (L+d) d (-y) hmy le_rfl)
      (shiftBox_distance (-y) hmy _) a b
    change latticePair q β L x y ≤ latticePair q β (L+d) (x-y) 0
    simpa only [← latticePair_inside, a, b, shiftBox_val, add_neg_cancel, ← sub_eq_add_neg,
      sub_self] using h

/-- Physical even-layer spectra without assuming a thermodynamic pair
limit. Every packet uses the same canonical infinite-volume scalar. -/
theorem canonicalFreePair_gridPacket_spectrum {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (canonicalFreePair q β) c x y n :=
  (canonicalFreePair_stationary hq hβ).gridPacket_spectrum hq tendsto_id diagonal c x y

theorem StationaryPairLimit.eq_canonicalFreePair {q : ℕ} (hq : 2 ≤ q) {β : ℝ}
    (hβ : 0 ≤ β) {L : ℕ → ℕ} {g : Site → ℝ} (hg : StationaryPairLimit q β L g)
    (hL : Tendsto L atTop atTop) : g = canonicalFreePair q β := by
  funext z
  have a := hg z 0
  have b := (rooted_tendsto hq hβ z).comp hL
  rw [sub_zero] at a
  exact tendsto_nhds_unique a b

theorem canonicalFreePair_gridPacket_orbit_spectrum {q : ℕ} (hq : 2 ≤ q)
    {β : ℝ} (hβ : 0 ≤ β) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => canonicalFreePair q β (signedPerm p s z)) c x y n :=
  (canonicalFreePair_stationary hq hβ).gridPacket_signedPerm_spectrum hq tendsto_id p s diagonal c x y

#print axioms boxPair_mono_of_isometric_embedding
#print axioms canonicalFreePair_stationary
#print axioms canonicalFreePair_gridPacket_spectrum
#print axioms StationaryPairLimit.eq_canonicalFreePair
#print axioms canonicalFreePair_gridPacket_orbit_spectrum
end IsingScaling.Potts.SiteBox
