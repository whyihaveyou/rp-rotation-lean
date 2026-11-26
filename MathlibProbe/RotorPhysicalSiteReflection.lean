import MathlibProbe.RotorBondReflection
import MathlibProbe.IsingSiteReflection
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Site reflections of the free cubic sphere-spin Gibbs law

Give each vertex of the cube the same independent unit-sphere probability
law before inserting the Boltzmann density. An axial site mirror or a
face-diagonal site mirror has a common wall and two isomorphic open sides.
Nearest-neighbour edges never join the two open sides. Split the pair
interaction between these sides, with half of every wall edge in each piece.
In the coordinates (wall, positive side, reflected negative side) the Gibbs
weight is exactly the product of the two equal half-weight functions.
Reindexing the independent site coordinates preserves their product measure.
For a signed test of the closed half-box the two inner integrals hence give
the square of the same real integral. Summing this inequality over the
coordinate tests of the sphere spins gives the reflected dot-product
two-point form, including repeated sites and sites on the wall.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology InnerProductSpace BigOperators
namespace IsingScaling.Rotor.SiteReflection

variable {N L : ℕ}

abbrev Config (N L : ℕ) := BoxSite L → Rotor.Spin N

/-- The normalized area measure on the unit sphere of the actual rotor.
The polar measure before normalization is induced by Euclidean Lebesgue measure. -/
def surfacePrior (N : ℕ) : Measure (Rotor.Spin N) :=
  let m := (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
  (m Set.univ)⁻¹ • m

instance surfacePrior_probability (N : ℕ) [NeZero N] : IsProbabilityMeasure (surfacePrior N) where
  measure_univ := by
    let m := (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
    have hm : m Set.univ ≠ 0 :=
      fun hz => Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.mp hz)
    change ((m Set.univ)⁻¹ • m) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm (measure_ne_top _ _)]

private abbrev Wall (M : BoxSiteMirror L) := {x : BoxSite L // M.tip x = 0}
private abbrev Half (M : BoxSiteMirror L) := {x : BoxSite L // 0 < M.tip x}
private abbrev Record (N : ℕ) (M : BoxSiteMirror L) :=
  (Wall M → Rotor.Spin N) × (Half M → Rotor.Spin N) × (Half M → Rotor.Spin N)

private def index (M : BoxSiteMirror L) : BoxSite L ≃ Wall M ⊕ (Half M ⊕ Half M) where
  toFun x := if h : M.tip x = 0 then .inl ⟨x,h⟩ else
    if hp : 0 < M.tip x then .inr (.inl ⟨x,hp⟩) else
      .inr (.inr ⟨M.refl x, by rw [M.neg]; omega⟩)
  invFun := Sum.elim Subtype.val (Sum.elim Subtype.val (fun x => M.refl x.val))
  left_inv x := by
    by_cases hw : M.tip x = 0
    · simp [hw]
    · by_cases hp : 0 < M.tip x
      · simp [hw, hp]
      · simp [hw, hp, M.invol]
  right_inv k := by
    rcases k with w | ⟨p | n⟩
    · simp [w.property]
    · simp [p.property, p.property.ne']
    · have hn := n.property
      simp [M.neg, M.invol, hn.ne', not_lt.mpr hn.le]

private def paste (M : BoxSiteMirror L) (k : Record N M) : Config N L :=
  fun x => Sum.elim k.1 (Sum.elim k.2.1 k.2.2) (index M x)

private lemma paste_eq (M : BoxSiteMirror L) (k : Record N M) (x : BoxSite L) :
    paste M k x = (if h : M.tip x = 0 then k.1 ⟨x,h⟩ else
      if hp : 0 < M.tip x then k.2.1 ⟨x,hp⟩ else k.2.2 ⟨M.refl x, by rw [M.neg]; omega⟩) := by
  by_cases hw : M.tip x = 0
  · simp [paste, index, hw]
  · by_cases hp : 0 < M.tip x <;> simp [paste, index, hw, hp]

private lemma paste_continuous (M : BoxSiteMirror L) : Continuous (paste (N := N) M) := by
  apply continuous_pi
  intro x
  simp only [paste]
  cases index M x with
  | inl _ => simp only [Sum.elim_inl]; fun_prop
  | inr j => cases j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

private abbrev siteLaw {T : Type*} [Fintype T] (θ : Measure (Rotor.Spin N)) :
    Measure (T → Rotor.Spin N) := Measure.pi (fun _ => θ)

private lemma paste_preserving (M : BoxSiteMirror L) (θ : Measure (Rotor.Spin N))
    [IsProbabilityMeasure θ] :
    MeasurePreserving (paste M)
      ((siteLaw (T := Wall M) θ).prod
        ((siteLaw (T := Half M) θ).prod (siteLaw (T := Half M) θ)))
      (siteLaw (T := BoxSite L) θ) := by
  let e := index M
  have h1 := measurePreserving_sumPiEquivProdPi_symm (fun _ : Half M ⊕ Half M => θ)
  have h2 := measurePreserving_sumPiEquivProdPi_symm (fun _ : Wall M ⊕ (Half M ⊕ Half M) => θ)
  have h3 := (measurePreserving_piCongrLeft (fun _ : Wall M ⊕ (Half M ⊕ Half M) => θ) e).symm
  have h := h3.comp (h2.comp ((MeasurePreserving.id (siteLaw (T := Wall M) θ)).prod h1))
  convert h using 1
  funext k x
  change Sum.elim k.1 (Sum.elim k.2.1 k.2.2) (index M x) =
    (MeasurableEquiv.piCongrLeft (fun _ => Rotor.Spin N) e).symm
      ((MeasurableEquiv.sumPiEquivProdPi _).symm (k.1,
        (MeasurableEquiv.sumPiEquivProdPi _).symm (k.2.1, k.2.2))) x
  change Sum.elim _ _ (e x) =
    (Equiv.piCongrLeft (fun _ => Rotor.Spin N) e).symm _ x
  rw [Equiv.piCongrLeft_symm_apply]
  cases e x with
  | inl _ => rfl
  | inr j => cases j <;> rfl

private def term (σ : Config N L) (x y : BoxSite L) : ℝ :=
  if latticeDistance x y = 1 then ⟪(σ x).val, (σ y).val⟫_ℝ else 0

/-- Every nearest-neighbour edge in the free cube contributes once. -/
def energy (σ : Config N L) : ℝ := (∑ x, ∑ y, term σ x y) / 2

private def halfTerm (M : BoxSiteMirror L) (σ : Config N L) (x y : BoxSite L) : ℝ :=
  if 0 ≤ M.tip x ∧ 0 ≤ M.tip y then
    if M.tip x = 0 ∧ M.tip y = 0 then term σ x y / 2 else term σ x y
  else 0

private def halfEnergy (M : BoxSiteMirror L) (σ : Config N L) : ℝ :=
  (∑ x, ∑ y, halfTerm M σ x y) / 2

private lemma term_split (M : BoxSiteMirror L) (σ : Config N L) (x y : BoxSite L) :
    term σ x y = halfTerm M σ x y + halfTerm M (σ ∘ M.refl) (M.refl x) (M.refl y) := by
  unfold halfTerm term
  simp only [M.neg, M.dist, Function.comp_apply, M.invol]
  by_cases he : latticeDistance x y = 1
  · have hn := M.separated x y
    have hn' := M.separated y x
    have hs : latticeDistance y x = latticeDistance x y := by
      unfold latticeDistance
      apply sum_congr rfl
      intro i _
      rw [show (y.val i - x.val i) = -(x.val i - y.val i) by omega, Int.natAbs_neg]
    rw [hs] at hn'
    simp only [he, ite_true]
    split_ifs <;> first | (exfalso; omega) | ring
  · simp [he]

private lemma energy_split (M : BoxSiteMirror L) (σ : Config N L) :
    energy σ = halfEnergy M σ + halfEnergy M (σ ∘ M.refl) := by
  unfold energy
  simp_rw [term_split M σ]
  simp only [sum_add_distrib]
  simp_rw [fun x => Equiv.sum_comp M.refl (halfTerm M (σ ∘ M.refl) (M.refl x))]
  rw [Equiv.sum_comp M.refl (fun x => ∑ y, halfTerm M (σ ∘ M.refl) x y), add_div]
  rfl

private lemma halfEnergy_congr (M : BoxSiteMirror L) {σ τ : Config N L}
    (h : ∀ x, 0 ≤ M.tip x → σ x = τ x) : halfEnergy M σ = halfEnergy M τ := by
  unfold halfEnergy
  congr 1
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases he : 0 ≤ M.tip x ∧ 0 ≤ M.tip y
  · simp [halfTerm, term, he, h x he.1, h y he.2]
  · simp [halfTerm, he]

private lemma paste_left (M : BoxSiteMirror L) (k : Record N M)
    (x : BoxSite L) (hx : 0 ≤ M.tip x) :
    paste M k x = paste M (k.1,k.2.1,k.2.1) x := by
  rw [paste_eq, paste_eq]
  by_cases hz : M.tip x = 0
  · simp [hz]
  · simp [hz, lt_of_le_of_ne hx (Ne.symm hz)]

private lemma paste_right (M : BoxSiteMirror L) (k : Record N M)
    (x : BoxSite L) (hx : 0 ≤ M.tip x) :
    paste M k (M.refl x) = paste M (k.1,k.2.2,k.2.2) x := by
  rw [paste_eq, paste_eq]
  by_cases hz : M.tip x = 0
  · simp [M.wall x hz, hz]
  · have hp : 0 < M.tip x := by omega
    simp [M.neg, M.invol, hz, hp, not_lt.mpr hx]

private lemma energy_continuous : Continuous (energy (N := N) (L := L)) := by
  have ht (x y : BoxSite L) : Continuous (fun σ : Config N L => term σ x y) := by
    unfold term
    by_cases he : latticeDistance x y = 1 <;> simp only [he, ite_true, ite_false] <;> fun_prop
  exact (continuous_finsetSum _ (fun x _ => continuous_finsetSum _ (fun y _ => ht x y))).div_const _

/-- The expectation of the reflected product of any continuous closed-half
observable is nonnegative before division by the positive partition function. -/
theorem site_reflection_positive (M : BoxSiteMirror L) (θ : Measure (Rotor.Spin N))
    [IsProbabilityMeasure θ] (β : ℝ) (F : Config N L → ℝ) (hF : Continuous F)
    (hside : ∀ σ τ : Config N L, (∀ x, 0 ≤ M.tip x → σ x = τ x) → F σ = F τ) :
    0 ≤ ∫ σ, Real.exp (β * energy σ) * F σ * F (σ ∘ M.refl) ∂siteLaw θ := by
  let G := fun σ : Config N L => Real.exp (β * energy σ) * F σ * F (σ ∘ M.refl)
  have hG : Continuous G := by
    dsimp [G]
    have hr : Continuous (fun σ : Config N L => σ ∘ M.refl) :=
      continuous_pi fun x => continuous_apply _
    exact ((continuous_const.mul energy_continuous).rexp.mul hF).mul (hF.comp hr)
  let a := fun (b : Wall M → Rotor.Spin N) (u : Half M → Rotor.Spin N) =>
    let σ := paste M (b,u,u)
    Real.exp (β * halfEnergy M σ) * F σ
  have splitG (k : Record N M) : G (paste M k) = a k.1 k.2.1 * a k.1 k.2.2 := by
    have hl := paste_left M k
    have hr : ∀ x, 0 ≤ M.tip x → (paste M k ∘ M.refl) x = paste M (k.1,k.2.2,k.2.2) x :=
      paste_right M k
    simp only [G, a, energy_split M (paste M k), mul_add, Real.exp_add,
      halfEnergy_congr M hl, halfEnergy_congr M hr, hside _ _ hl, hside _ _ hr]
    ring
  change 0 ≤ ∫ σ, G σ ∂siteLaw θ
  rw [← (paste_preserving M θ).hasLaw.integral_comp hG.aestronglyMeasurable]
  have hI := (hG.comp (paste_continuous (N := N) M)).integrable_of_hasCompactSupport
    (μ := (siteLaw (T := Wall M) θ).prod ((siteLaw (T := Half M) θ).prod
      (siteLaw (T := Half M) θ))) (HasCompactSupport.of_compactSpace _)
  rw [integral_prod _ hI]
  apply integral_nonneg
  intro b
  simp only [Function.comp_apply, splitG, integral_prod_mul]
  exact mul_self_nonneg _

/-- The physical full-cube partition function for the product spin prior. -/
def partition (θ : Measure (Rotor.Spin N)) (β : ℝ) (L : ℕ) : ℝ :=
  ∫ σ : Config N L, Real.exp (β * energy σ) ∂siteLaw θ

theorem partition_pos (θ : Measure (Rotor.Spin N)) [IsProbabilityMeasure θ] (β : ℝ) (L : ℕ) :
    0 < partition θ β L := by
  apply integral_exp_pos
  exact (continuous_const.mul energy_continuous).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual dot-product Gibbs two-point moment on a free cube. -/
def boxCorrelation (θ : Measure (Rotor.Spin N)) (β : ℝ) (x y : BoxSite L) : ℝ :=
  (∫ σ : Config N L, Real.exp (β * energy σ) * ⟪(σ x).val,(σ y).val⟫_ℝ ∂siteLaw θ) /
    partition θ β L

/-- Extend the finite free-box two-point function by zero at exterior sites. -/
def freePair (θ : Measure (Rotor.Spin N)) (β : ℝ) (L : ℕ) (x y : Site) : ℝ :=
  if hx : x ∈ cube L then
    if hy : y ∈ cube L then boxCorrelation θ β ⟨x,hx⟩ ⟨y,hy⟩ else 0
  else 0

@[simp] theorem freePair_inside (θ : Measure (Rotor.Spin N)) (β : ℝ) (x y : BoxSite L) :
    freePair θ β L x y = boxCorrelation θ β x y := by simp [freePair, x.property, y.property]

theorem freePair_comm (θ : Measure (Rotor.Spin N)) (β : ℝ) (L : ℕ) (x y : Site) :
    freePair θ β L x y = freePair θ β L y x := by
  by_cases hx : x ∈ cube L <;> by_cases hy : y ∈ cube L <;>
    simp only [freePair, hx, hy, ↓reduceDIte]
  unfold boxCorrelation
  congr 1
  apply integral_congr_ae
  filter_upwards [] with σ
  rw [real_inner_comm]

theorem freePair_same (θ : Measure (Rotor.Spin N)) [IsProbabilityMeasure θ] (β : ℝ)
    (x : BoxSite L) : freePair θ β L x x = 1 := by
  rw [freePair_inside, boxCorrelation]
  simp only [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow, mul_one]
  exact div_self (partition_pos θ β L).ne'

private lemma pair_continuous (β : ℝ) (x y : BoxSite L) :
    Continuous (fun σ : Config N L => Real.exp (β * energy σ) * ⟪(σ x).val,(σ y).val⟫_ℝ) := by
  have hW : Continuous (fun σ : Config N L => Real.exp (β * energy σ)) :=
    (continuous_const.mul energy_continuous).rexp
  exact hW.mul (by fun_prop)

theorem abs_freePair_le_one (θ : Measure (Rotor.Spin N)) [IsProbabilityMeasure θ]
    (β : ℝ) (L : ℕ) (x y : Site) : |freePair θ β L x y| ≤ 1 := by
  by_cases hx : x ∈ cube L
  case neg => simp [freePair, hx]
  by_cases hy : y ∈ cube L
  case neg => simp [freePair, hy]
  simp only [freePair, hx, hy, ↓reduceDIte]
  let a : BoxSite L := ⟨x,hx⟩
  let b : BoxSite L := ⟨y,hy⟩
  change |boxCorrelation θ β a b| ≤ 1
  rw [boxCorrelation, abs_div, abs_of_pos (partition_pos θ β L), div_le_one (partition_pos θ β L)]
  calc
    _ ≤ ∫ σ : Config N L, ‖Real.exp (β * energy σ) * ⟪(σ a).val,(σ b).val⟫_ℝ‖ ∂siteLaw θ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono
      · exact ((pair_continuous β a b).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).norm
      · exact (continuous_const.mul energy_continuous).rexp.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro σ
        change ‖Real.exp (β * energy σ) * ⟪(σ a).val,(σ b).val⟫_ℝ‖ ≤ Real.exp (β * energy σ)
        rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
        apply mul_le_of_le_one_right (Real.exp_pos _).le
        simpa [norm_eq_of_mem_sphere (σ a), norm_eq_of_mem_sphere (σ b)] using
          (norm_inner_le_norm (𝕜 := ℝ) (σ a).val (σ b).val)

private lemma sum_integral (θ : Measure (Rotor.Spin N)) [IsProbabilityMeasure θ]
    {T : Type*} [Fintype T] (B : T → Config N L → ℝ) (hc : ∀ i, Continuous (B i)) :
    (∫ σ, ∑ i, B i σ ∂siteLaw θ) = ∑ i, ∫ σ, B i σ ∂siteLaw θ :=
  integral_finsetSum _ (fun i _ => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- The normalized dot product has a nonnegative reflected matrix, for both
wall and open-side sites and all real signed coefficient vectors. -/
theorem freePair_reflection_positive (θ : Measure (Rotor.Spin N)) [IsProbabilityMeasure θ]
    (β : ℝ) {L : ℕ} (M : BoxSiteMirror L) {ι : Type*} [Fintype ι]
    (x : ι → BoxSite L) (hx : ∀ i, 0 ≤ M.tip (x i)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * freePair θ β L (x i) (M.refl (x j)) := by
  classical
  let U (σ : Config N L) := ∑ i, c i • (σ (x i)).val
  let W (σ : Config N L) := Real.exp (β * energy σ)
  have hcU : Continuous U := by unfold U; fun_prop
  have hcW : Continuous W := (continuous_const.mul energy_continuous).rexp
  have hr : Continuous (fun σ : Config N L => σ ∘ M.refl) := continuous_pi fun _ => continuous_apply _
  have hcUk (k : Fin N) : Continuous (fun σ => U σ k) := by fun_prop
  have hk (k : Fin N) : 0 ≤ ∫ σ : Config N L, W σ * U σ k * U (σ ∘ M.refl) k ∂siteLaw θ := by
    apply site_reflection_positive M θ β _ (hcUk k)
    intro σ τ h
    have he : U σ = U τ := Finset.sum_congr rfl fun i _ => by rw [h (x i) (hx i)]
    rw [he]
  have hdot : 0 ≤ ∫ σ : Config N L, W σ * ⟪U σ,U (σ ∘ M.refl)⟫_ℝ ∂siteLaw θ := by
    simp only [PiLp.inner_apply, Real.inner_apply, Finset.mul_sum, ← mul_assoc]
    rw [sum_integral θ (fun k σ => W σ * U σ k * U (σ ∘ M.refl) k)
      (fun k => (hcW.mul (hcUk k)).mul ((hcUk k).comp hr))]
    exact sum_nonneg fun k _ => hk k
  let H (i j : ι) (σ : Config N L) := c i * c j *
    (W σ * ⟪(σ (x i)).val,(σ (M.refl (x j))).val⟫_ℝ)
  have hH (i j : ι) : Continuous (H i j) :=
    continuous_const.mul (pair_continuous β (x i) (M.refl (x j)))
  have expand (σ : Config N L) : W σ * ⟪U σ, U (σ ∘ M.refl)⟫_ℝ = ∑ i, ∑ j, H i j σ := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [U, H, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Finset.mul_sum, Function.comp_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  simp_rw [expand] at hdot
  rw [sum_integral θ (fun i σ => ∑ j, H i j σ) (fun i => continuous_finsetSum _ (fun j _ => hH i j))] at hdot
  simp_rw [sum_integral θ (H _) (hH _)] at hdot
  simp only [H, integral_const_mul] at hdot
  simp only [freePair_inside, boxCorrelation, ← mul_div_assoc, ← Finset.sum_div]
  exact div_nonneg hdot (partition_pos θ β L).le

#print axioms freePair_reflection_positive
#print axioms abs_freePair_le_one

end IsingScaling.Rotor.SiteReflection

