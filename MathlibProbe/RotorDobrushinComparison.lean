import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic

/-! Finite coordinate oscillation certificates and greedy single-site comparison.
The degree bound is on the neighbours affected by one update. -/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace IsingScaling.Rotor.DobrushinComparison

structure Certificate (ι : Type*) where
  sites : Finset ι
  populated : sites.Nonempty
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  zero_off : ∀ i, i ∉ sites → weight i = 0

namespace Certificate

variable {ι : Type*}

def total (p : Certificate ι) : ℝ := ∑ i ∈ p.sites, p.weight i

theorem total_nonneg (p : Certificate ι) : 0 ≤ p.total :=
  Finset.sum_nonneg fun i _ => p.nonneg i

noncomputable def largest (p : Certificate ι) : ι :=
  Classical.choose (p.sites.exists_max_image p.weight p.populated)

theorem largest_spec (p : Certificate ι) :
    p.largest ∈ p.sites ∧ ∀ i ∈ p.sites, p.weight i ≤ p.weight p.largest :=
  Classical.choose_spec (p.sites.exists_max_image p.weight p.populated)

theorem total_le_card_mul_largest (p : Certificate ι) :
    p.total ≤ (p.sites.card : ℝ) * p.weight p.largest := by
  calc
    p.total ≤ ∑ _i ∈ p.sites, p.weight p.largest :=
      Finset.sum_le_sum (p.largest_spec.2)
    _ = _ := by simp

variable [DecidableEq ι]

def update (p : Certificate ι) (i : ι) (neighbors : Finset ι)
    (d : ℝ) (hd : 0 ≤ d) : Certificate ι where
  sites := p.sites ∪ neighbors
  populated := p.populated.mono Finset.subset_union_left
  weight j := if j = i then 0 else p.weight j +
    (if j ∈ neighbors then d * p.weight i else 0)
  nonneg j := by
    split_ifs <;> positivity [p.nonneg j, p.nonneg i]
  zero_off j hj := by
    simp only [Finset.mem_union, not_or] at hj
    simp [p.zero_off j hj.1, hj.2]

theorem update_total (p : Certificate ι) {i : ι} (hi : i ∈ p.sites)
    (B : Finset ι) (d : ℝ) (hd : 0 ≤ d) :
    (p.update i B d hd).total ≤
      p.total - (1 - (B.card : ℝ) * d) * p.weight i := by
  let U := p.sites ∪ B
  have hiU : i ∈ U := Finset.mem_union_left B hi
  have hsum : ∑ j ∈ U, p.weight j = p.total :=
    (Finset.sum_subset (s₁ := p.sites) (s₂ := U) Finset.subset_union_left
      (fun j _ hj => p.zero_off j hj)).symm
  have hB : ∑ j ∈ U, (if j ∈ B then d * p.weight i else 0) =
      (B.card : ℝ) * (d * p.weight i) := by
    calc
      _ = ∑ j ∈ B, (if j ∈ B then d * p.weight i else 0) :=
        (Finset.sum_subset (s₁ := B) (s₂ := U) Finset.subset_union_right
          (fun j _ hj => by simp [hj])).symm
      _ = ∑ _j ∈ B, d * p.weight i := Finset.sum_congr rfl (by intro j hj; simp [hj])
      _ = _ := by simp
  calc
    (p.update i B d hd).total ≤ ∑ j ∈ U, ((p.weight j -
        (if j = i then p.weight i else 0)) + (if j ∈ B then d * p.weight i else 0)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases he : j = i
      · subst j
        by_cases hiB : i ∈ B <;> simp [update, hiB, mul_nonneg hd (p.nonneg i)]
      · simp [update, he]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hB]
      simp [hiU]
      ring

end Certificate

/-- A finite initial budget cannot sustain a positive limiting mass with harmonic cost. -/
theorem tendsto_zero_of_linear_cost (a : ℕ → ℝ) {m D c : ℝ}
    (hm : 0 < m) (hD : 0 ≤ D) (hc : 0 < c)
    (ha : ∀ n, 0 ≤ a n) (hdec : ∀ n, a (n+1) ≤ a n)
    (hcost : ∀ n : ℕ, c * a n ≤ (m + D * n) * (a n - a (n+1))) :
    Tendsto a atTop (𝓝 0) := by
  have hb : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact ha n⟩
  let L := ⨅ n, a n
  have hL : 0 ≤ L := le_ciInf ha
  have hLa (n : ℕ) : L ≤ a n := ciInf_le hb n
  have hzero : L = 0 := by
    by_contra hn
    have hpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hn)
    let v := c * L / (m + D)
    have hmd : 0 < m + D := by linarith
    have hv : 0 < v := div_pos (mul_pos hc hpos) hmd
    have hterm (n : ℕ) : v * (1 / ((n : ℝ) + 1)) ≤ a n - a (n+1) := by
      have hdiff := sub_nonneg.mpr (hdec n)
      have hmn : m + D * (n : ℝ) ≤ (m + D) * (n+1) := by
        nlinarith [mul_nonneg hm.le (Nat.cast_nonneg (α := ℝ) n)]
      have h := calc
        c * L ≤ c * a n := mul_le_mul_of_nonneg_left (hLa n) hc.le
        _ ≤ _ := hcost n
        _ ≤ ((m + D) * (n+1)) * (a n - a (n+1)) :=
          mul_le_mul_of_nonneg_right hmn hdiff
      change c * L / (m + D) * (1 / ((n : ℝ) + 1)) ≤ _
      rw [mul_one_div, div_div, div_le_iff₀ (mul_pos hmd (by positivity))]
      linarith only [h, mul_comm ((m + D) * (n+1)) (a n - a (n+1))]
    have htelescope (n : ℕ) : ∑ k ∈ Finset.range n, (a k - a (k+1)) = a 0 - a n := by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    obtain ⟨n, hn⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
      (a 0 / v)).exists
    have hs : v * (∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1))) ≤ a 0 := by
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ k ∈ Finset.range n, (a k - a (k+1)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
        _ = _ := htelescope n
        _ ≤ _ := sub_le_self _ (ha n)
    exact (not_lt_of_ge hs) (by simpa [mul_comm] using (div_lt_iff₀ hv).mp hn)
  simpa only [← hzero] using tendsto_atTop_ciInf (antitone_nat_of_succ_le hdec) hb

/-- The finite budgets obtained by repeatedly updating a site of largest weight. -/
noncomputable def Certificate.greedy {ι : Type*} [DecidableEq ι] (p : Certificate ι)
    (neighbors : ι → Finset ι) (d : ℝ) (hd : 0 ≤ d) : ℕ → Certificate ι :=
  Nat.rec p fun _ q => q.update q.largest (neighbors q.largest) d hd

/-- The total weight along the greedy orbit tends to zero whenever the sum of
the one-site influences is smaller than one. -/
theorem Certificate.tendsto_greedy_total {ι : Type*} [DecidableEq ι] (p : Certificate ι)
    (neighbors : ι → Finset ι) (degree : ℕ) (hdegree : ∀ i, (neighbors i).card ≤ degree)
    (d : ℝ) (hd : 0 ≤ d) (hsmall : (degree : ℝ) * d < 1) :
    Tendsto (fun n => (p.greedy neighbors d hd n).total) atTop (𝓝 0) := by
  let st := p.greedy neighbors d hd
  have hcard (n : ℕ) : (st n).sites.card ≤ p.sites.card + degree*n := by
    induction n with
    | zero => simp [st, Certificate.greedy]
    | succ n ih =>
      calc
        _ ≤ (st n).sites.card + (neighbors (st n).largest).card := Finset.card_union_le ..
        _ ≤ (p.sites.card + degree*n) + degree := Nat.add_le_add ih (hdegree _)
        _ = _ := by rw [Nat.mul_succ]; omega
  let a (n : ℕ) := (st n).total
  let c := 1 - (degree : ℝ)*d
  have hc : 0 < c := sub_pos.mpr hsmall
  have hdrop (n : ℕ) : c * (st n).weight (st n).largest ≤ a n - a (n+1) := by
    let q := st n
    have he := q.update_total q.largest_spec.1 (neighbors q.largest) d hd
    have hdg : ((neighbors q.largest).card : ℝ) ≤ degree := by exact_mod_cast hdegree _
    have hcoef : c ≤ 1 - ((neighbors q.largest).card : ℝ)*d := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_right hdg hd) 1
    change c * q.weight q.largest ≤ q.total - (q.update q.largest (neighbors q.largest) d hd).total
    linarith only [he, mul_le_mul_of_nonneg_right hcoef (q.nonneg q.largest)]
  have hdec (n : ℕ) : a (n+1) ≤ a n := by
    have h := hdrop n
    linarith only [h, mul_nonneg hc.le ((st n).nonneg (st n).largest)]
  have hcost (n : ℕ) :
      c * a n ≤ ((p.sites.card : ℝ) + degree * (n : ℝ)) * (a n - a (n+1)) := by
    let q := st n
    have hmul : (q.sites.card : ℝ) ≤ (p.sites.card : ℝ) + degree * (n : ℝ) := by
      exact_mod_cast hcard n
    calc
      _ ≤ c * ((q.sites.card : ℝ) * q.weight q.largest) :=
        mul_le_mul_of_nonneg_left q.total_le_card_mul_largest hc.le
      _ = (q.sites.card : ℝ) * (c * q.weight q.largest) := by ring
      _ ≤ (q.sites.card : ℝ) * (a n - a (n+1)) :=
        mul_le_mul_of_nonneg_left (hdrop n) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hmul (sub_nonneg.mpr (hdec n))
  exact tendsto_zero_of_linear_cost a (Nat.cast_pos.mpr (Finset.card_pos.mpr p.populated))
    (Nat.cast_nonneg (α := ℝ) degree) hc (fun n => (st n).total_nonneg) hdec hcost

/-- Greedy propagation of certified one-site bounds, including construction of
the full sequence of updated tests from the one-step rule. -/
theorem expectation_eq_of_updates {ι Test : Type*} [DecidableEq ι]
    (neighbors : ι → Finset ι) (degree : ℕ) (hdegree : ∀ i, (neighbors i).card ≤ degree)
    (d : ℝ) (hd : 0 ≤ d) (hsmall : (degree : ℝ) * d < 1)
    (K : ι → Test → Test) (valid : Test → Certificate ι → Prop)
    (hK : ∀ f p i, valid f p → valid (K i f) (p.update i (neighbors i) d hd))
    (P Q : Test → ℝ) (hP : ∀ i f, P (K i f) = P f) (hQ : ∀ i f, Q (K i f) = Q f)
    (hbound : ∀ f p, valid f p → |P f - Q f| ≤ p.total)
    {f : Test} {p : Certificate ι} (hf : valid f p) : P f = Q f := by
  let budget := p.greedy neighbors d hd
  let test : ℕ → Test := Nat.rec f (fun n g => K (budget n).largest g)
  have hvalid (n : ℕ) : valid (test n) (budget n) := by
    induction n with
    | zero => exact hf
    | succ n ih => exact hK _ _ _ ih
  have hinv (n : ℕ) : P (test n) = P f ∧ Q (test n) = Q f := by
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih => exact ⟨(hP _ _).trans ih.1, (hQ _ _).trans ih.2⟩
  have hall (n : ℕ) : |P f - Q f| ≤ (budget n).total := by
    simpa only [(hinv n).1, (hinv n).2] using hbound _ _ (hvalid n)
  have hlim := p.tendsto_greedy_total neighbors degree hdegree d hd hsmall
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (ge_of_tendsto hlim (Filter.Eventually.of_forall hall)))

section Configurations

variable {ι α : Type*} [DecidableEq ι]

/-- A pointwise single-coordinate oscillation bound, allowing upper certificates. -/
def CoordBound (f : (ι → α) → ℝ) (i : ι) (w : ℝ) : Prop :=
  ∀ x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ w

def Bounds (f : (ι → α) → ℝ) (p : Certificate ι) : Prop :=
  ∀ i, CoordBound f i (p.weight i)

/-- A continuous test can be compared at arbitrary configurations by first
patching finitely many coordinates and then taking the product-topology limit. -/
theorem abs_sub_le_total [TopologicalSpace α] (f : C(ι → α, ℝ)) (p : Certificate ι)
    (hf : Bounds f p) (x y : ι → α) : |f x - f y| ≤ p.total := by
  let patch (u : Finset ι) (j : ι) := if j ∈ u then y j else x j
  have hpatch (u : Finset ι) : |f x - f (patch u)| ≤ ∑ j ∈ u, p.weight j := by
    induction u using Finset.induction_on with
    | empty => simp [patch]
    | @insert i u hi ih =>
      have hone : |f (patch u) - f (patch (insert i u))| ≤ p.weight i := by
        apply hf i
        intro j hji
        simp [patch, hji]
      calc
        _ ≤ |f x - f (patch u)| + |f (patch u) - f (patch (insert i u))| :=
          abs_sub_le _ _ _
        _ ≤ (∑ j ∈ u, p.weight j) + p.weight i := add_le_add ih hone
        _ = _ := by simp [hi, add_comm]
  have hsum (u : Finset ι) : ∑ j ∈ u, p.weight j ≤ p.total := by
    calc
      _ ≤ ∑ j ∈ u ∪ p.sites, p.weight j :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun j _ _ => p.nonneg j)
      _ = _ := (Finset.sum_subset (s₁ := p.sites) (s₂ := u ∪ p.sites)
        Finset.subset_union_right (fun j _ hj => p.zero_off j hj)).symm
  have ht : Tendsto patch atTop (𝓝 y) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply (tendsto_const_nhds : Tendsto (fun _ : Finset ι => y i) atTop (𝓝 (y i))).congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with u hu
    simp [patch, hu (Finset.mem_singleton_self i)]
  have hlim : Tendsto (fun u => |f x - f (patch u)|) atTop (𝓝 |f x - f y|) :=
    (tendsto_const_nhds.sub ((f.continuous.tendsto y).comp ht)).abs
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun u => (hpatch u).trans (hsum u))

def uniformCertificate (u : Finset ι) (hu : u.Nonempty) (b : ℝ) (hb : 0 ≤ b) :
    Certificate ι where
  sites := u
  populated := hu
  weight i := if i ∈ u then b else 0
  nonneg i := by split_ifs <;> positivity
  zero_off i hi := by simp [hi]

/-- Any bounded cylinder yields an initial finite certificate. -/
theorem bounds_of_depends (f : (ι → α) → ℝ) (u : Finset ι) (hu : u.Nonempty)
    (b : ℝ) (hb : 0 ≤ b)
    (hcyl : ∀ x y, (∀ j ∈ u, x j = y j) → f x = f y)
    (hbound : ∀ x y, |f x - f y| ≤ b) :
    Bounds f (uniformCertificate u hu b hb) := by
  intro i x y hxy
  by_cases hi : i ∈ u
  · simpa [uniformCertificate, hi] using hbound x y
  · have he : f x = f y := hcyl x y fun j hj => hxy j (fun h => hi (h ▸ hj))
    simp [uniformCertificate, hi, he]

variable [TopologicalSpace α] [MeasurableSpace (ι → α)]

omit [DecidableEq ι] [TopologicalSpace α] in
private theorem integral_le_integral_add (f : (ι → α) → ℝ) {b : ℝ}
    (h : ∀ x y, |f x - f y| ≤ b)
    (P Q : Measure (ι → α)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable f P) (hQ : Integrable f Q) :
    (∫ x, f x ∂P) ≤ (∫ x, f x ∂Q) + b := by
  have hpoint (x : ι → α) : f x ≤ (∫ y, f y ∂Q) + b := by
    have hmono := integral_mono (μ := Q) (integrable_const (f x))
      (hQ.add (integrable_const b)) (fun y => (sub_le_iff_le_add.mp
        ((le_abs_self (f x - f y)).trans (h x y))).trans_eq (add_comm _ _))
    simpa [integral_add hQ (integrable_const b)] using hmono
  simpa using integral_mono (μ := P) hP (integrable_const ((∫ x, f x ∂Q) + b)) hpoint

theorem abs_integral_sub_integral_le_total (f : C(ι → α, ℝ)) (p : Certificate ι)
    (hf : Bounds f p)
    (P Q : Measure (ι → α)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x => f x) P) (hQ : Integrable (fun x => f x) Q) :
    |(∫ x, f x ∂P) - (∫ x, f x ∂Q)| ≤ p.total := by
  have h := abs_sub_le_total f p hf
  exact abs_sub_le_iff.mpr ⟨sub_le_iff_le_add'.mpr (integral_le_integral_add f h P Q hP hQ),
    sub_le_iff_le_add'.mpr (integral_le_integral_add f h Q P hQ hP)⟩

/-- Gibbs specialization interface. All work after the physical single-site
bounds uses the product topology and the original two probability measures. -/
theorem integral_eq_of_site_bounds (neighbors : ι → Finset ι) (degree : ℕ)
    (hdegree : ∀ i, (neighbors i).card ≤ degree) (d : ℝ) (hd : 0 ≤ d)
    (hsmall : (degree : ℝ) * d < 1)
    (K : ι → C(ι → α, ℝ) → C(ι → α, ℝ))
    (hself : ∀ i f, CoordBound (K i f) i 0)
    (hother : ∀ (i j : ι) (f : C(ι → α, ℝ)) (ai aj : ℝ), j ≠ i →
      CoordBound f i ai → CoordBound f j aj →
      CoordBound (K i f) j (aj + if j ∈ neighbors i then d*ai else 0))
    (P Q : Measure (ι → α)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (intP : ∀ f : C(ι → α, ℝ), Integrable (fun x => f x) P)
    (intQ : ∀ f : C(ι → α, ℝ), Integrable (fun x => f x) Q)
    (invP : ∀ i f, (∫ x, K i f x ∂P) = ∫ x, f x ∂P)
    (invQ : ∀ i f, (∫ x, K i f x ∂Q) = ∫ x, f x ∂Q)
    {f : C(ι → α, ℝ)} {p : Certificate ι} (hf : Bounds f p) :
    (∫ x, f x ∂P) = ∫ x, f x ∂Q := by
  refine expectation_eq_of_updates neighbors degree hdegree d hd hsmall K
    (fun g a => Bounds g a) ?_ (fun g => ∫ x, g x ∂P) (fun g => ∫ x, g x ∂Q)
    invP invQ (fun g a hg => abs_integral_sub_integral_le_total g a hg P Q (intP g) (intQ g)) hf
  intro g a i hg j
  by_cases he : j = i
  · subst j
    simpa [Certificate.update] using hself i g
  · simpa [Certificate.update, he] using hother i j g _ _ he (hg i) (hg j)

end Configurations

/-- Single-site-invariant probabilities on a countable product of compact metric
spin spaces agree as measures, by comparison on each finite cylinder. -/
theorem measure_eq_of_site_bounds {ι α : Type*} [DecidableEq ι] [Nonempty ι] [Countable ι]
    [PseudoMetricSpace α] [CompactSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (neighbors : ι → Finset ι) (degree : ℕ) (hdegree : ∀ i, (neighbors i).card ≤ degree)
    (d : ℝ) (hd : 0 ≤ d) (hsmall : (degree : ℝ) * d < 1)
    (K : ι → C(ι → α, ℝ) → C(ι → α, ℝ))
    (hself : ∀ i f, CoordBound (K i f) i 0)
    (hother : ∀ (i j : ι) (f : C(ι → α, ℝ)) (ai aj : ℝ), j ≠ i →
      CoordBound f i ai → CoordBound f j aj →
      CoordBound (K i f) j (aj + if j ∈ neighbors i then d*ai else 0))
    (P Q : Measure (ι → α)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (invP : ∀ i f, (∫ x, K i f x ∂P) = ∫ x, f x ∂P)
    (invQ : ∀ i f, (∫ x, K i f x ∂Q) = ∫ x, f x ∂Q) : P = Q := by
  apply IsProjectiveLimit.unique (P := fun u : Finset ι => Measure.map u.restrict Q)
  · intro u
    have hr : Continuous (u.restrict : (ι → α) → (u → α)) :=
      continuous_pi fun i => continuous_apply i.val
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    rw [integral_map hr.measurable.aemeasurable g.continuous.aestronglyMeasurable,
        integral_map hr.measurable.aemeasurable g.continuous.aestronglyMeasurable]
    let f : C(ι → α, ℝ) := g.toContinuousMap.comp ⟨u.restrict, hr⟩
    let v := insert (Classical.arbitrary ι) u
    have hv : v.Nonempty := Finset.insert_nonempty _ _
    have hdep (x y : ι → α) (h : ∀ j ∈ v, x j = y j) : f x = f y := by
      change g (u.restrict x) = g (u.restrict y)
      exact congrArg g (funext fun j => h j (Finset.mem_insert_of_mem j.property))
    have hbound (x y : ι → α) : |f x - f y| ≤ ‖g‖ + ‖g‖ := by
      change |g (u.restrict x) - g (u.restrict y)| ≤ ‖g‖ + ‖g‖
      simpa only [Real.norm_eq_abs] using
        (norm_sub_le (g (u.restrict x)) (g (u.restrict y))).trans
          (add_le_add (g.norm_coe_le_norm _) (g.norm_coe_le_norm _))
    have hint (R : Measure (ι → α)) [IsProbabilityMeasure R] (w : C(ι → α, ℝ)) :
        Integrable (fun x => w x) R :=
      w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact integral_eq_of_site_bounds neighbors degree hdegree d hd hsmall K hself hother
      P Q (hint P) (hint Q) invP invQ
      (bounds_of_depends f v hv _ (add_nonneg (norm_nonneg _) (norm_nonneg _)) hdep hbound)
  · intro u
    rfl

end IsingScaling.Rotor.DobrushinComparison
