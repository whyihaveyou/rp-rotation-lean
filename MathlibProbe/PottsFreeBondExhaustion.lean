import MathlibProbe.PottsFreeBondState
import MathlibProbe.PottsBondDomainEmbedding

/-! # The free FK law for arbitrary finite-domain exhaustions

A finite vertex set carries its induced nearest-neighbour graph with one
representative of each unordered bond. Its free law is the normalized sum
of the Bernoulli weights times the cluster weights, including isolated
vertices, with every exterior bond closed. The laws increase on increasing
events under inclusion of vertex sets. The centered cubes are cofinal, so
every exhaustion that eventually contains each site has the same weak
limit and the same limit of open-path probabilities. -/

noncomputable section

open Filter Finset MeasureTheory
open scoped Classical ENNReal Topology

namespace IsingScaling.Potts.FreeBond
open SiteBox EdwardsSokal

private def edgeLabel {U : Finset Site} (a : ↥U × ↥U) : Sym2 Site := s(a.1.val, a.2.val)

/-- Extend the open bonds in the finite domain by closed exterior bonds. -/
def domainRecord {U : Finset Site} (F : Finset (↥U × ↥U)) : Field :=
  fun e => decide (e.val ∈ F.image edgeLabel)

private theorem domainRecord_mono {U : Finset Site} {F G : Finset (↥U × ↥U)}
    (hFG : F ⊆ G) (e : Bond) : domainRecord F e = true → domainRecord G e = true := by
  simp only [domainRecord, decide_eq_true_eq]
  exact fun he => Finset.image_subset_image hFG he

private theorem domainRecord_map {U V : Finset Site} (e : ↥U ↪ ↥V)
    (ρ : (↥U × ↥U) ↪ (↥V × ↥V)) (he : ∀ x, (e x).val = x.val) {F : Finset (↥U × ↥U)}
    (hρ : ∀ a ∈ F, ρ a = (e a.1, e a.2) ∨ ρ a = (e a.2, e a.1)) :
    domainRecord (F.map ρ) = domainRecord F := by
  have hl (a) (ha : a ∈ F) : edgeLabel (ρ a) = edgeLabel a := by
    rcases hρ a ha with h | h
    · simp [edgeLabel, h, he]
    · simpa only [edgeLabel, h, he] using (Sym2.eq_swap (a := a.2.val) (b := a.1.val))
  have him : (F.map ρ).image edgeLabel = F.image edgeLabel := by
    ext b
    simp only [mem_image, Finset.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
      exact ⟨a, ha, (hl a ha).symm.trans hb⟩
    · rintro ⟨a, ha, hb⟩
      exact ⟨ρ a, ⟨a, ha, rfl⟩, (hl a ha).trans hb⟩
  funext b
  exact congrArg (fun S : Finset (Sym2 Site) => decide (b.val ∈ S)) him

private theorem domainWeight_nonneg (q : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {U : Finset Site} (F : Finset (↥U × ↥U)) :
    0 ≤ bondProbabilityWeight q p (domainBonds U) F :=
  mul_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_pos.mpr h1).le _))
    (pow_nonneg (Nat.cast_nonneg q) _)

private theorem domainTotal_pos {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (U : Finset Site) :
    0 < ∑ F ∈ (domainBonds U).powerset, bondProbabilityWeight q p (domainBonds U) F := by
  apply sum_pos' (fun F _ => domainWeight_nonneg q h0 h1 F)
  refine ⟨∅, by simp, ?_⟩
  simp only [bondProbabilityWeight, card_empty, pow_zero, one_mul, Nat.sub_zero]
  exact mul_pos (pow_pos (sub_pos.mpr h1) _) (pow_pos (by exact_mod_cast (show 0 < q by omega)) _)

/-- The atomic free random-cluster measure on the induced graph with
vertex set `U`. In particular the empty edge configuration has positive
weight even when the domain is empty or the bond parameter vanishes. -/
def freeDomainLaw {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) (U : Finset Site) :
    ProbabilityMeasure Field := by
  let w := bondProbabilityWeight q p (domainBonds U)
  let Z := ∑ F ∈ (domainBonds U).powerset, w F
  refine ⟨∑ F ∈ (domainBonds U).powerset, ENNReal.ofReal (w F / Z) • Measure.dirac (domainRecord F),
    ⟨?_⟩⟩
  simp only [Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ =>
      div_nonneg (domainWeight_nonneg q h0 h1 F) (domainTotal_pos hq h0 h1 U).le), ← Finset.sum_div]
  rw [div_self (domainTotal_pos hq h0 h1 U).ne', ENNReal.ofReal_one]

theorem freeDomainLaw_cube {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) (L : ℕ) :
    freeDomainLaw hq h0 h1 (cube L) = freeCubeLaw hq h0 h1 L := by
  apply ProbabilityMeasure.toMeasure_injective
  dsimp only [freeDomainLaw, freeCubeLaw, ProbabilityMeasure.toMeasure]
  simp only [domainBonds_cube]
  rfl

theorem freeDomainLaw_real {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (U : Finset Site) (A : Set Field) :
    (freeDomainLaw hq h0 h1 U A : ℝ) =
      (∑ F ∈ (domainBonds U).powerset,
        if domainRecord F ∈ A then bondProbabilityWeight q p (domainBonds U) F else 0) /
      ∑ F ∈ (domainBonds U).powerset, bondProbabilityWeight q p (domainBonds U) F := by
  let w := bondProbabilityWeight q p (domainBonds U)
  let Z := ∑ F ∈ (domainBonds U).powerset, w F
  let m (F : Finset _) := ENNReal.ofReal (w F / Z) • Measure.dirac (domainRecord F)
  have hm (F : Finset _) : m F A =
      ENNReal.ofReal ((if domainRecord F ∈ A then w F else 0) / Z) := by
    by_cases h : domainRecord F ∈ A <;> simp [m, Measure.smul_apply, Measure.dirac_apply, h]
  have hn (F : Finset _) : 0 ≤ (if domainRecord F ∈ A then w F else 0) / Z := by
    apply div_nonneg _ (domainTotal_pos hq h0 h1 U).le
    split
    · exact domainWeight_nonneg q h0 h1 F
    · exact le_rfl
  change ((∑ F ∈ (domainBonds U).powerset, m F) A).toReal = _
  rw [Measure.finsetSum_apply]
  simp only [hm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun F _ => hn F),
    ENNReal.toReal_ofReal (sum_nonneg (fun F _ => hn F)), ← Finset.sum_div]

/-- A lattice path in a configuration extended by closed exterior bonds
joins precisely the two vertices in the same finite open cluster. -/
theorem domainRecord_connection_iff {U : Finset Site} {F : Finset (↥U × ↥U)}
    (hF : F ⊆ domainBonds U) (x y : ↥U) :
    domainRecord F ∈ connection x.val y.val ↔ port F x = port F y := by
  let label (z : Site) : Option (Component F) :=
    if hz : z ∈ U then some (port F ⟨z, hz⟩) else none
  have hl (z : ↥U) : label z.val = some (port F z) := by simp [label, z.property]
  constructor
  · intro hw
    have collapse {u v : Site} (h : domainRecord F ∈ connection u v) : label u = label v := by
      induction h with
      | rel u v huv =>
        obtain ⟨e, he, hopen⟩ := huv
        obtain ⟨a, ha, hab⟩ := mem_image.mp (of_decide_eq_true hopen)
        rcases Sym2.eq_iff.mp (hab.trans he) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hl, hl]
          exact congrArg some (Quot.sound ha)
        · rw [hl, hl]
          exact congrArg some (Quot.sound ha).symm
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih jh => exact ih.trans jh
    exact Option.some.inj (by simpa only [hl] using collapse hw)
  · intro hxy
    have lift {a b : ↥U} (h : Relation.EqvGen (fun u v : ↥U => (u, v) ∈ F) a b) :
        domainRecord F ∈ connection a.val b.val := by
      induction h with
      | rel u v huv =>
        have hd : latticeDistance u.val v.val = 1 := (mem_filter.mp (hF huv)).2.2
        let e : Bond := ⟨s(u.val, v.val), u.val, v.val, rfl, hd⟩
        exact .rel _ _ ⟨e, rfl, decide_eq_true
          (mem_image.mpr ⟨(u, v), huv, rfl⟩ : e.val ∈ F.image edgeLabel)⟩
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih jh => exact .trans _ _ _ ih jh
    exact lift ((port_eq_iff_connected F x y).mp hxy)

theorem freeDomainLaw_connection_eq_finite {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {U : Finset Site} (x y : ↥U) :
    (freeDomainLaw hq h0 h1 U (connection x.val y.val) : ℝ) =
      (∑ F ∈ (domainBonds U).powerset,
        if port F x = port F y then bondProbabilityWeight q p (domainBonds U) F else 0) /
      ∑ F ∈ (domainBonds U).powerset, bondProbabilityWeight q p (domainBonds U) F := by
  rw [freeDomainLaw_real]
  apply congrArg (fun t : ℝ => t /
    ∑ F ∈ (domainBonds U).powerset, bondProbabilityWeight q p (domainBonds U) F)
  exact sum_congr rfl fun F hF => by rw [domainRecord_connection_iff (mem_powerset.mp hF)]

private theorem freeDomainLaw_eq_expectation {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p < 1) (U : Finset Site) (A : Set Field) :
    (freeDomainLaw hq h0 h1 U A : ℝ) = freeFKExpectation q (domainBonds U)
      (fun _ => -Real.log (1 - p)) (fun F => if domainRecord F ∈ A then 1 else 0) := by
  let β := -Real.log (1 - p)
  let K := domainBonds U
  let c := Real.exp (-β) ^ K.card
  have hp : 1 - Real.exp (-β) = p := by
    simp only [β, neg_neg, Real.exp_log (sub_pos.mpr h1), sub_sub_cancel]
  have hw (F) (hF : F ∈ K.powerset) :
      bondProbabilityWeight q p K F = c * fkWeight q (fun _ => β) F := by
    simpa only [hp] using bondProbabilityWeight_eq_activity q β (mem_powerset.mp hF)
  rw [freeDomainLaw_real]
  have hnum : (∑ F ∈ K.powerset, if domainRecord F ∈ A then bondProbabilityWeight q p K F else 0) =
      c * ∑ F ∈ K.powerset, fkWeight q (fun _ => β) F * (if domainRecord F ∈ A then 1 else 0) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun F hF => ?_
    by_cases h : domainRecord F ∈ A <;> simp [h, hw F hF]
  have hden : (∑ F ∈ K.powerset, bondProbabilityWeight q p K F) =
      c * ∑ F ∈ K.powerset, fkWeight q (fun _ => β) F := by
    rw [Finset.mul_sum]
    exact sum_congr rfl hw
  exact (congrArg₂ (· / ·) hnum hden).trans (mul_div_mul_left _ _ (pow_ne_zero _ (Real.exp_pos _).ne'))

/-- Inclusion of arbitrary induced domains increases the probability
of any increasing event in the common, zero-extended bond field. -/
theorem freeDomainLaw_mono {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {U V : Finset Site} (hUV : U ⊆ V) (A : Set Field)
    (hA : ∀ {ω η : Field}, (∀ e, ω e = true → η e = true) → ω ∈ A → η ∈ A) :
    freeDomainLaw hq h0 h1 U A ≤ freeDomainLaw hq h0 h1 V A := by
  let β := -Real.log (1 - p)
  have hβ : 0 ≤ β := neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr h1).le (sub_le_self _ h0))
  let f (F : Finset (↥V × ↥V)) : ℝ := if domainRecord F ∈ A then 1 else 0
  have hf0 (F) : 0 ≤ f F := by dsimp [f]; split <;> norm_num
  have hf : Monotone f := by
    intro F G hFG
    by_cases h : domainRecord F ∈ A
    · simp [f, h, hA (domainRecord_mono hFG) h]
    · simpa [f, h] using hf0 G
  obtain ⟨e, ρ, he, hρ, hK⟩ := domainBonds_mono_embedding hUV
  have hsmall : freeFKExpectation q (domainBonds U) (fun _ => β)
      (fun F => if domainRecord F ∈ A then 1 else 0) =
      freeFKExpectation q (domainBonds U) ((fun _ => β) ∘ ρ) (fun F => f (F.map ρ)) := by
    apply congrArg (fun t : ℝ => t / ∑ F ∈ (domainBonds U).powerset, fkWeight q (fun _ => β) F)
    refine sum_congr rfl fun F hF => ?_
    change _ = fkWeight q (fun _ => β) F * (if domainRecord (F.map ρ) ∈ A then 1 else 0)
    rw [domainRecord_map e ρ he (fun a ha => hρ a ((mem_powerset.mp hF) ha))]
  apply NNReal.coe_le_coe.mp
  rw [freeDomainLaw_eq_expectation, freeDomainLaw_eq_expectation]
  exact hsmall.trans_le (freeFKExpectation_mono_embedding (by omega : 0 < q) e ρ hρ hK
    (fun _ => hβ) f hf0 hf)

/-- Pointwise eventual inclusion is cofinality for finite sets, even if
successive domains have no inclusion relation. -/
theorem tendsto_domains_atTop {ι : Type*} {l : Filter ι} {U : ι → Finset Site}
    (hU : ∀ x : Site, ∀ᶠ n in l, x ∈ U n) : Tendsto U l atTop := by
  refine Filter.tendsto_atTop.mpr (fun S => ?_)
  exact ((Filter.eventually_all_finset S).mpr fun x _ => hU x).mono (fun _ h _ hx => h _ hx)

private theorem tendsto_increasing_event {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    (A : Set Field) (hA : ∀ {ω η : Field}, (∀ e, ω e = true → η e = true) → ω ∈ A → η ∈ A)
    {a : NNReal} (hc : Tendsto (fun L => freeCubeLaw hq h0 h1 L A) atTop (𝓝 a)) :
    Tendsto (fun U => freeDomainLaw hq h0 h1 U A) atTop (𝓝 a) := by
  have hm : Monotone (fun U => freeDomainLaw hq h0 h1 U A) :=
    fun _ _ h => freeDomainLaw_mono hq h0 h1 h A hA
  apply (tendsto_iff_tendsto_subseq_of_monotone hm (tendsto_domains_atTop eventually_mem_cube)).mpr
  simpa only [Function.comp_def, freeDomainLaw_cube] using hc

/-- Weak convergence of the net of all finite free domains on the full
bond field. The same free law already realizes the Potts two-point theorem. -/
theorem tendsto_freeDomainLaw_atTop {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    Tendsto (freeDomainLaw hq h0 h1) atTop (𝓝 (freeLaw hq h0 h1)) := by
  have hr (F : Finset Bond) :
      Tendsto (fun U => freeDomainLaw hq h0 h1 U (allOpen F)) atTop
        (𝓝 (freeLaw hq h0 h1 (allOpen F))) :=
    tendsto_increasing_event hq h0 h1 (allOpen F) (fun h hω e he => h e (hω e he))
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto (tendsto_freeLaw hq h0 h1)
        (allOpen_isClopen F))
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν, k, hk, hν⟩ := CompactSpace.tendsto_subseq (freeDomainLaw hq h0 h1 ∘ ns)
  have heq : ν = freeLaw hq h0 h1 := probability_ext_allOpen fun F => tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν (allOpen_isClopen F))
    ((hr F).comp (hns.comp hk.tendsto_atTop))
  exact ⟨k, heq ▸ hν⟩

/-- No nesting, regularity or boundary-to-volume estimate is required. -/
theorem exhaustion_tendsto_freeLaw {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {ι : Type*} {l : Filter ι} {U : ι → Finset Site} (hU : ∀ x : Site, ∀ᶠ n in l, x ∈ U n) :
    Tendsto (fun n => freeDomainLaw hq h0 h1 (U n)) l (𝓝 (freeLaw hq h0 h1)) :=
  (tendsto_freeDomainLaw_atTop hq h0 h1).comp (tendsto_domains_atTop hU)

private theorem record_connection_iff_within {L : ℕ} (F : Finset (BoxSite L × BoxSite L))
    (x y : Site) : record F ∈ connection x y ↔ record F ∈ within L x y := by
  refine ⟨?_, fun h => within_subset_connection L x y h⟩
  apply Relation.EqvGen.mono
  rintro u v ⟨e, huv, hopen⟩
  obtain ⟨a, _, ha⟩ := mem_image.mp (of_decide_eq_true hopen)
  change s(a.1.val, a.2.val) = e.val at ha
  exact ⟨e, (mem_window_iff ha.symm).mpr ⟨a.1.property, a.2.property⟩, huv, hopen⟩

private theorem freeCubeLaw_connection_eq_within {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p < 1) (L : ℕ) (x y : Site) :
    freeCubeLaw hq h0 h1 L (connection x y) = freeCubeLaw hq h0 h1 L (within L x y) := by
  apply NNReal.coe_injective
  rw [freeCubeLaw_real, freeCubeLaw_real]
  apply congrArg (fun t : ℝ => t / ∑ F ∈ (cubeBonds L).powerset, bondProbabilityWeight q p (cubeBonds L) F)
  exact sum_congr rfl fun F _ => by rw [record_connection_iff_within F x y]

/-- Connection is an increasing open event that need not be clopen.
Cofinal comparison on finite induced domains identifies its probability
limit as well as the weak limit of the full laws. -/
theorem exhaustion_connection_tendsto {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1)
    {ι : Type*} {l : Filter ι} {U : ι → Finset Site} (hU : ∀ x : Site, ∀ᶠ n in l, x ∈ U n)
    (x y : Site) :
    Tendsto (fun n => (freeDomainLaw hq h0 h1 (U n) (connection x y) : ℝ)) l
      (𝓝 (freeConnectivity q p (x - y))) := by
  have hc : Tendsto (fun L => freeCubeLaw hq h0 h1 L (connection x y)) atTop
      (𝓝 (freeLaw hq h0 h1 (connection x y))) := by
    apply NNReal.tendsto_coe.mp
    rw [freeLaw_connection]
    refine (latticeConnectivity_tendsto hq h0 h1 x y).congr' ?_
    filter_upwards [eventually_mem_cube x, eventually_mem_cube y] with L hx hy
    rw [freeCubeLaw_connection_eq_within]
    simpa [latticeConnectivity, hx, hy] using
      (freeCubeLaw_within hq h0 h1 (⟨x,hx⟩ : BoxSite L) ⟨y,hy⟩).symm
  have hinc {ω η : Field} (h : ∀ e, ω e = true → η e = true) :
      ω ∈ connection x y → η ∈ connection x y :=
    Relation.EqvGen.mono (fun _ _ ⟨e, he, hopen⟩ => ⟨e, he, h e hopen⟩) _ _
  have hl := (tendsto_increasing_event hq h0 h1 (connection x y) hinc hc).comp (tendsto_domains_atTop hU)
  rw [← freeLaw_connection hq h0 h1 x y]
  exact NNReal.tendsto_coe.mpr hl

#print axioms freeDomainLaw_connection_eq_finite
#print axioms freeDomainLaw_mono
#print axioms exhaustion_tendsto_freeLaw
#print axioms exhaustion_connection_tendsto

end IsingScaling.Potts.FreeBond
