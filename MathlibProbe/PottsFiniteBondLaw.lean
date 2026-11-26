import MathlibProbe.PottsBondStateSpace
import MathlibProbe.PottsFreeConnectivityRotation
import MathlibProbe.PottsFKEventComparison
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The physical finite random-cluster probability on the countable lattice
bond field. Bonds outside the free cube are closed. The law uses one
unoriented bond for each adjacent pair and the Bernoulli bond parameter. -/

noncomputable section
open Filter Finset MeasureTheory
open scoped Classical Topology ENNReal
namespace IsingScaling.Potts.FreeBond
open SiteBox EdwardsSokal

private def unordered {L : ℕ} (a : BoxSite L × BoxSite L) : Sym2 Site := s(a.1.val, a.2.val)

def record {L : ℕ} (F : Finset (BoxSite L × BoxSite L)) : Field :=
  fun e => decide (e.val ∈ F.image unordered)

theorem record_mono {L : ℕ} {F G : Finset (BoxSite L × BoxSite L)} (hFG : F ⊆ G)
    (e : Bond) : record F e = true → record G e = true := by
  simp only [record, decide_eq_true_eq]
  intro he
  obtain ⟨a, ha, heq⟩ := mem_image.mp he
  exact mem_image.mpr ⟨a, hFG ha, heq⟩

theorem record_map {M N : ℕ} (e : BoxSite M ↪ BoxSite N)
    (ρ : (BoxSite M × BoxSite M) ↪ (BoxSite N × BoxSite N))
    (he : ∀ x, (e x).val = x.val) {F : Finset (BoxSite M × BoxSite M)}
    (hρ : ∀ a ∈ F, ρ a = (e a.1, e a.2) ∨ ρ a = (e a.2, e a.1)) :
    record (F.map ρ) = record F := by
  have h (a) (ha : a ∈ F) : unordered (ρ a) = unordered a := by
    rcases hρ a ha with h|h
    · simp [unordered, h, he]
    · simpa only [unordered, h, he] using (Sym2.eq_swap (a := a.2.val) (b := a.1.val))
  have him : (F.map ρ).image unordered = F.image unordered := by
    ext b
    simp only [mem_image, Finset.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
      exact ⟨a, ha, (h a ha).symm.trans hb⟩
    · rintro ⟨a, ha, hb⟩
      exact ⟨ρ a, ⟨a, ha, rfl⟩, (h a ha).trans hb⟩
  funext b
  exact congrArg (fun S : Finset (Sym2 Site) => decide (b.val ∈ S)) him

theorem record_within_iff {L : ℕ} {F : Finset (BoxSite L × BoxSite L)}
    (hF : F ⊆ cubeBonds L) (x y : BoxSite L) :
    record F ∈ within L x.val y.val ↔ port F x = port F y := by
  let label (z : Site) : Option (Component F) :=
    if hz : z ∈ cube L then some (port F ⟨z, hz⟩) else none
  have hl (z : BoxSite L) : label z.val = some (port F z) := by simp [label, z.property]
  constructor
  · intro hw
    have collapse {u v : Site} (huv : record F ∈ within L u v) : label u = label v := by
      induction huv with
      | rel u v huv =>
        obtain ⟨e, _, hev, hope⟩ := huv
        obtain ⟨a, ha, hpair⟩ := mem_image.mp (of_decide_eq_true hope)
        rcases Sym2.eq_iff.mp (hpair.trans hev) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rw [hl, hl]
          exact congrArg some (Quot.sound ha)
        · rw [hl, hl]
          exact congrArg some (Quot.sound ha).symm
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih jh => exact ih.trans jh
    exact Option.some.inj (by simpa only [hl] using collapse hw)
  · intro hxy
    have lift {u v : BoxSite L}
        (h : Relation.EqvGen (fun a b : BoxSite L => (a,b) ∈ F) u v) :
        record F ∈ within L u.val v.val := by
      induction h with
      | rel a b hab =>
        have hd : latticeDistance a.val b.val = 1 := (mem_filter.mp (hF hab)).2.2
        let e : Bond := ⟨s(a.val, b.val), a.val, b.val, rfl, hd⟩
        have hm : e ∈ window L := mem_subtype.mpr
          (mem_image.mpr ⟨(a.val, b.val), mem_product.mpr ⟨a.property,b.property⟩, rfl⟩)
        exact .rel _ _ ⟨e, hm, rfl,
          decide_eq_true (mem_image.mpr ⟨(a,b), hab, rfl⟩ : e.val ∈ F.image unordered)⟩
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih jh => exact .trans _ _ _ ih jh
    exact lift ((port_eq_iff_connected F x y).mp hxy)

private theorem weight_nonneg (q : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) {L : ℕ}
    (F : Finset (BoxSite L × BoxSite L)) : 0 ≤ bondProbabilityWeight q p (cubeBonds L) F :=
  mul_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_pos.mpr h1).le _))
    (pow_nonneg (Nat.cast_nonneg q) _)

private theorem total_pos {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) (L : ℕ) :
    0 < ∑ F ∈ (cubeBonds L).powerset, bondProbabilityWeight q p (cubeBonds L) F := by
  apply sum_pos' (fun F _ => weight_nonneg q h0 h1 F)
  refine ⟨∅, by simp, ?_⟩
  simp only [bondProbabilityWeight, card_empty, pow_zero, one_mul, Nat.sub_zero]
  exact mul_pos (pow_pos (sub_pos.mpr h1) _) (pow_pos (by exact_mod_cast (show 0 < q by omega)) _)

def freeCubeLaw {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) (L : ℕ) :
    ProbabilityMeasure Field := by
  let w := bondProbabilityWeight q p (cubeBonds L)
  let Z := ∑ F ∈ (cubeBonds L).powerset, w F
  refine ⟨∑ F ∈ (cubeBonds L).powerset, ENNReal.ofReal (w F / Z) • Measure.dirac (record F), ⟨?_⟩⟩
  simp only [Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ =>
      div_nonneg (weight_nonneg q h0 h1 F) (total_pos hq h0 h1 L).le), ← Finset.sum_div]
  rw [div_self (total_pos hq h0 h1 L).ne', ENNReal.ofReal_one]

theorem freeCubeLaw_real {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (L : ℕ) (A : Set Field) :
    (freeCubeLaw hq h0 h1 L A : ℝ) =
      (∑ F ∈ (cubeBonds L).powerset, if record F ∈ A then bondProbabilityWeight q p (cubeBonds L) F else 0) /
      ∑ F ∈ (cubeBonds L).powerset, bondProbabilityWeight q p (cubeBonds L) F := by
  let w := bondProbabilityWeight q p (cubeBonds L)
  let Z := ∑ F ∈ (cubeBonds L).powerset, w F
  let m (F : Finset _) := ENNReal.ofReal (w F / Z) • Measure.dirac (record F)
  have hm (F : Finset _) : m F A =
      ENNReal.ofReal ((if record F ∈ A then w F else 0) / Z) := by
    by_cases h : record F ∈ A <;> simp [m, Measure.smul_apply, Measure.dirac_apply, h]
  have hn (F : Finset _) : 0 ≤ (if record F ∈ A then w F else 0) / Z := by
    apply div_nonneg _ (total_pos hq h0 h1 L).le
    split
    · exact weight_nonneg q h0 h1 F
    · exact le_rfl
  change ((∑ F ∈ (cubeBonds L).powerset, m F) A).toReal = _
  rw [Measure.finsetSum_apply]
  simp only [hm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ => hn F),
    ENNReal.toReal_ofReal (sum_nonneg (fun F _ => hn F)), ← Finset.sum_div]

/-- A path read from the full bond field in its generating cube has the
normalized finite FK connectivity used by the Potts simplex theorem. -/
theorem freeCubeLaw_within {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {L : ℕ} (x y : BoxSite L) :
    (freeCubeLaw hq h0 h1 L (within L x.val y.val) : ℝ) = boxConnectivity q p x y := by
  rw [freeCubeLaw_real, boxConnectivity]
  congr 1
  exact sum_congr rfl fun F hF => by rw [record_within_iff (mem_powerset.mp hF)]

/-- Normalized probabilities of arbitrary events in the physical free
cube agree with the activity weights used in domain monotonicity. -/
theorem freeCubeLaw_eq_expectation {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (L : ℕ) (A : Set Field) :
    (freeCubeLaw hq h0 h1 L A : ℝ) = freeFKExpectation q (cubeBonds L)
      (fun _ => -Real.log (1 - p)) (fun F => if record F ∈ A then 1 else 0) := by
  let β := -Real.log (1 - p)
  let K := cubeBonds L
  let c := Real.exp (-β) ^ K.card
  have hp : 1 - Real.exp (-β) = p := by
    simp only [β, neg_neg, Real.exp_log (sub_pos.mpr h1), sub_sub_cancel]
  have hw (F) (hF : F ∈ K.powerset) :
      bondProbabilityWeight q p K F = c * fkWeight q (fun _ => β) F := by
    simpa only [hp] using bondProbabilityWeight_eq_activity q β (mem_powerset.mp hF)
  rw [freeCubeLaw_real]
  refine (congrArg₂ (· / ·) (show (∑ F ∈ K.powerset,
      if record F ∈ A then bondProbabilityWeight q p K F else 0) =
      c * ∑ F ∈ K.powerset, fkWeight q (fun _ => β) F * (if record F ∈ A then 1 else 0) from ?_)
    (show (∑ F ∈ K.powerset, bondProbabilityWeight q p K F) =
      c * ∑ F ∈ K.powerset, fkWeight q (fun _ => β) F from ?_)).trans
    (mul_div_mul_left _ _ (pow_ne_zero _ (Real.exp_pos _).ne'))
  · rw [Finset.mul_sum]
    refine sum_congr rfl fun F hF => ?_
    by_cases h : record F ∈ A <;> simp [h, hw F hF]
  · rw [Finset.mul_sum]
    exact sum_congr rfl hw

/-- The zero extensions of the free bond laws increase on all increasing
events, including cylinders requiring an entire connecting path. -/
theorem freeCubeLaw_mono {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {M N : ℕ} (hMN : M ≤ N) (A : Set Field)
    (hA : ∀ {ω η : Field}, (∀ e, ω e = true → η e = true) → ω ∈ A → η ∈ A) :
    freeCubeLaw hq h0 h1 M A ≤ freeCubeLaw hq h0 h1 N A := by
  let β := -Real.log (1 - p)
  have hβ : 0 ≤ β := neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr h1).le (sub_le_self _ h0))
  let f (F : Finset (BoxSite N × BoxSite N)) : ℝ := if record F ∈ A then 1 else 0
  have hf0 (F) : 0 ≤ f F := by dsimp [f]; split <;> norm_num
  have hf : Monotone f := by
    intro F G hFG
    by_cases h : record F ∈ A
    · simp [f, h, hA (record_mono hFG) h]
    · simpa [f, h] using hf0 G
  obtain ⟨e, ρ, he, hρ, hK⟩ := cubeBonds_mono_embedding hMN
  have small : freeFKExpectation q (cubeBonds M) (fun _ => β)
      (fun F => if record F ∈ A then 1 else 0) =
      freeFKExpectation q (cubeBonds M) ((fun _ => β) ∘ ρ) (fun F => f (F.map ρ)) := by
    apply congrArg (fun t : ℝ => t /
      ∑ F ∈ (cubeBonds M).powerset, fkWeight q (fun _ => β) F)
    refine sum_congr rfl fun F hF => ?_
    change _ = fkWeight q (fun _ => β) F * (if record (F.map ρ) ∈ A then 1 else 0)
    rw [record_map e ρ he (fun a ha => hρ a ((mem_powerset.mp hF) ha))]
  apply NNReal.coe_le_coe.mp
  rw [freeCubeLaw_eq_expectation, freeCubeLaw_eq_expectation]
  exact small.trans_le (freeFKExpectation_mono_embedding (by omega : 0 < q) e ρ hρ hK
    (fun _ => hβ) f hf0 hf)

#print axioms freeCubeLaw_within
#print axioms freeCubeLaw_mono
end IsingScaling.Potts.FreeBond
