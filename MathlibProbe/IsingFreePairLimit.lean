import MathlibProbe.IsingSiteReflection
import MathlibProbe.IsingGibbsPositivity
import MathlibProbe.PacketHausdorff
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod
import Mathlib.Topology.Order.MonotoneConvergence

/-! A two-insertion correlation in a translated box is squeezed between
rooted correlations in smaller and larger centered boxes. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace IsingScaling

private lemma sum_restrict_spin {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
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

private def boxBonds (L : ℕ) : Finset (BoxSite L × BoxSite L) :=
  Finset.univ.filter fun e => latticeDistance e.1 e.2 = 1

private lemma cubeWeight_eq (β L) (σ : Spin L) :
    bondWeight (boxBonds L) (fun _ => β/2) σ = gibbsWeight β L σ := by
  unfold bondWeight gibbsWeight interaction boxBonds bondScore
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

private lemma boxCorrelation_graphPair (β L) (x y : BoxSite L) :
    boxCorrelation β L x y = graphPair (boxBonds L) (fun _ => β/2) (x,y) := by
  unfold boxCorrelation graphPair
  simp only [cubeWeight_eq, bondScore, mul_assoc]

private lemma boxCorrelation_embed {L N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (e : BoxSite L ↪ BoxSite N)
    (hd : ∀ x y, latticeDistance (e x) (e y) = latticeDistance x y)
    (x y : BoxSite L) :
    boxCorrelation β L x y ≤ boxCorrelation β N (e x) (e y) := by
  classical
  let emb := e.prodMap e
  let K := (boxBonds L).map emb
  let J (_ : BoxSite N × BoxSite N) : ℝ := β/2
  let p := (e x, e y)
  have hk : K ⊆ boxBonds N := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_filter.mpr ⟨mem_univ _, (hd q'.1 q'.2).trans (mem_filter.mp hq').2⟩
  have hw (σ : Spin N) : bondWeight K J σ = gibbsWeight β L (σ ∘ e) := by
    rw [← cubeWeight_eq]
    unfold bondWeight
    rw [show K = (boxBonds L).map emb from rfl, Finset.sum_map]
    rfl
  have hcalc : graphPair K J p = boxCorrelation β L x y := by
    obtain ⟨C,hC,heq⟩ := sum_restrict_spin e
    unfold graphPair boxCorrelation
    simp only [hw]
    have h1 := heq (fun τ => gibbsWeight β L τ * value (τ x) * value (τ y))
    simp only [Function.comp_apply] at h1
    have h2 := heq (gibbsWeight β L)
    rw [h2]
    change (∑ σ, gibbsWeight β L (σ ∘ e) * (value (σ (e x)) * value (σ (e y)))) / _ = _
    simp_rw [← mul_assoc]
    rw [h1]
    field_simp
  rw [← hcalc, boxCorrelation_graphPair]
  exact graphPair_mono hk J (fun _ => by dsimp [J]; positivity) p

private def shiftCube (L N d : ℕ) (a : Site) (ha : ∀ i, (a i).natAbs ≤ d)
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

private theorem shiftCube_distance {L N d : ℕ} (a : Site) (ha : ∀ i, (a i).natAbs ≤ d)
    (hLN : L+d ≤ N) (u v : BoxSite L) :
    latticeDistance (shiftCube L N d a ha hLN u) (shiftCube L N d a ha hLN v) =
      latticeDistance u v := by
  unfold latticeDistance
  apply sum_congr rfl
  intro i _
  change (u.val i + a i - (v.val i + a i)).natAbs = _
  rw [add_sub_add_right_eq_sub]

private theorem shiftCube_val {L N d : ℕ} {a : Site} {ha : ∀ i, (a i).natAbs ≤ d}
    {hLN : L+d ≤ N} (u : BoxSite L) :
    ((shiftCube L N d a ha hLN) u).val = u.val + a := rfl

private theorem cube_eventually (x : Site) : ∀ᶠ L : ℕ in atTop, x ∈ cube L := by
  filter_upwards [eventually_ge_atTop (∑ i, (x i).natAbs)] with L hL
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  omega

private theorem freePair_comm (β L) (x y : Site) : freePair β L x y = freePair β L y x := by
  unfold freePair
  congr 1
  exact sum_congr rfl fun _ _ => mul_right_comm ..

/-- Every rooted thermodynamic two-point limit of the ferromagnetic nearest-
neighbour model is also the translation-invariant two-insertion limit of the
same finite Gibbs measures. -/
theorem IsFreeTwoPoint.stationary_pair_limit {β g} (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    IsFreePairLimit β (fun x y => g (x-y)) := by
  have h (x y : Site) : Tendsto (fun L : ℕ => freePair β L x y) atTop (𝓝 (g (y-x))) := by
    let d := ∑ i, (x i).natAbs
    have hx (i) : (x i).natAbs ≤ d :=
      Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
    have hmx (i) : ((-x) i).natAbs ≤ d := by simpa using hx i
    have hm := (hg (y-x)).comp (Filter.tendsto_sub_atTop_nat d)
    have hp := (Filter.tendsto_add_atTop_iff_nat d).mpr (hg (y-x))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm hp
    · filter_upwards [eventually_ge_atTop d, (Filter.tendsto_sub_atTop_nat d).eventually
        (cube_eventually (y-x))] with L hL hxy
      have h0 : (0 : Site) ∈ cube (L-d) := by simp [cube, Fintype.mem_piFinset]
      let x0 : BoxSite (L-d) := ⟨0,h0⟩
      let x1 : BoxSite (L-d) := ⟨y-x,hxy⟩
      have hs := boxCorrelation_embed hβ (shiftCube (L-d) L d x hx (by omega))
        (shiftCube_distance x hx _) x0 x1
      change freeTwoPoint β (L-d) (y-x) ≤ freePair β L x y
      simpa only [boxCorrelation_eq_freePair, x0, x1, shiftCube_val,
        zero_add, sub_add_cancel, freePair_origin] using hs
    · filter_upwards [cube_eventually x, cube_eventually y] with L hxL hyL
      let x0 : BoxSite L := ⟨x,hxL⟩
      let x1 : BoxSite L := ⟨y,hyL⟩
      have hs := boxCorrelation_embed hβ (shiftCube L (L+d) d (-x) hmx le_rfl)
        (shiftCube_distance (-x) hmx _) x0 x1
      change freePair β L x y ≤ freeTwoPoint β (L+d) (y-x)
      simpa only [boxCorrelation_eq_freePair, x0, x1, shiftCube_val,
        add_neg_cancel, ← sub_eq_add_neg, sub_self, freePair_origin] using hs
  intro x y
  simpa only [freePair_comm β _ y x] using h y x

#print axioms IsFreeTwoPoint.stationary_pair_limit

private lemma monotone_rooted_box {β : ℝ} (hβ : 0 ≤ β) (x : Site) :
    Monotone (fun L : ℕ => freeTwoPoint β L x) := by
  intro L N hLN
  by_cases hL : x ∈ cube L
  · have h0 : (0 : Site) ∈ cube L := by simp [cube, Fintype.mem_piFinset]
    let s : BoxSite L := ⟨0,h0⟩
    let t : BoxSite L := ⟨x,hL⟩
    have hs := boxCorrelation_embed hβ (shiftCube L N 0 0 (by simp) (by omega))
      (shiftCube_distance 0 _ _) s t
    simpa only [boxCorrelation_eq_freePair, s, t, shiftCube_val,
      add_zero, freePair_origin] using hs
  · have hz : freeTwoPoint β L x = 0 := by simp [freeTwoPoint, occupation, hL]
    change freeTwoPoint β L x ≤ freeTwoPoint β N x
    rw [hz]
    exact freeTwoPoint_nonneg hβ _ _

/-- The canonical free-boundary thermodynamic two-point function. -/
def thermodynamicTwoPoint (β : ℝ) (x : Site) : ℝ := ⨆ L : ℕ, freeTwoPoint β L x

theorem thermodynamicTwoPoint_isLimit {β : ℝ} (hβ : 0 ≤ β) :
    IsFreeTwoPoint β (thermodynamicTwoPoint β) := by
  intro x
  apply tendsto_atTop_ciSup (monotone_rooted_box hβ x)
  refine ⟨1, ?_⟩
  rintro z ⟨L,rfl⟩
  exact (le_abs_self _).trans (abs_freePair_le_one β L 0 x)

theorem thermodynamicTwoPoint_stationary {β : ℝ} (hβ : 0 ≤ β) :
    IsFreePairLimit β (fun x y => thermodynamicTwoPoint β (x-y)) :=
  (thermodynamicTwoPoint_isLimit hβ).stationary_pair_limit hβ

theorem IsFreeTwoPoint.eq_thermodynamic {β g} (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    g = thermodynamicTwoPoint β :=
  funext fun x => tendsto_nhds_unique (hg x) (thermodynamicTwoPoint_isLimit hβ x)

/-- The susceptibility-normalized tangent uses exactly the physical g
whose time spectra are constructed below. -/
theorem IsTwoPointTangent.realizes_thermodynamic {β : ℝ} {μ : Measure Space}
    (hμ : IsTwoPointTangent β μ) (hβ : 0 ≤ β) :
    ∃ R : ℕ → ℕ, Tendsto R atTop atTop ∧
      ∀ f : CompactlySupportedContinuousMap Space ℝ,
        Tendsto (fun j => ∫ x, f x ∂twoPointMeasure (thermodynamicTwoPoint β) (R j))
          atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨g,R,hg,_,_,hr,hlim⟩ := hμ.realizes
  rw [hg.eq_thermodynamic hβ] at hlim
  exact ⟨R, hr, hlim⟩

/-- Positive face-diagonal spectral measure for the original thermodynamic
two-point function for every finite real packet. -/
theorem thermodynamic_diagonal_packet_spectrum {β : ℝ} (hβ : 0 ≤ β) {ι : Type} [Fintype ι]
    (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
      evenPacket c (fun m i j =>
        thermodynamicTwoPoint β ![x i-x j+(m:ℤ), x i-x j-(m:ℤ), y i-y j]) n :=
  Packet.diagonal_evenPacket_spectrum (thermodynamicTwoPoint_stationary hβ) c x y

#print axioms thermodynamic_diagonal_packet_spectrum

inductive PacketNormal | axis | faceDiagonal

def PacketNormal.displacement (d : PacketNormal) (m : ℕ) (x y : ℤ) : Site :=
  match d with
  | .axis => ![(m:ℤ), x, y]
  | .faceDiagonal => ![x+(m:ℤ), x-(m:ℤ), y]

/-- The three coordinate normals and six unoriented face diagonals are the
signed-coordinate-permutation orbits of the displayed two displacements.
This original-lattice result includes their physical mesh factors. -/
theorem thermodynamic_packet_spectrum {β : ℝ} (hβ : 0 ≤ β)
    (d : PacketNormal) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
      evenPacket c (fun m i j => thermodynamicTwoPoint β
        (signedPerm p s (d.displacement m (x i - x j) (y i - y j)))) n := by
  simp only [freeLimit_signedPerm (thermodynamicTwoPoint_isLimit hβ)]
  cases d with
  | axis => exact Packet.axis_evenPacket_spectrum (thermodynamicTwoPoint_stationary hβ) c x y
  | faceDiagonal => exact thermodynamic_diagonal_packet_spectrum hβ c x y

#print axioms thermodynamic_packet_spectrum

end IsingScaling
