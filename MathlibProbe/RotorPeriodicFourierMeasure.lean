import MathlibProbe.RotorPeriodicSpinState
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # The positive momentum measure of a periodic sphere-spin ensemble

On the actual finite displacement group, characters are orthogonal.
The Fourier weight of the dot covariance is nonnegative by applying
the real Gram inequality to the real and imaginary parts of a character.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology ComplexConjugate
namespace IsingScaling.Rotor.PressureSelection

section FiniteFourier
variable {G : Type*} [AddCommGroup G] [Fintype G]

private def weight (b : G → ℝ) (ψ : AddChar G ℂ) : ℝ :=
  (∑ a, b a * (ψ a).re) / Fintype.card G

private theorem character_diff_re (ψ : AddChar G ℂ) (a b : G) :
    (ψ (a-b)).re = (ψ a).re * (ψ b).re + (ψ a).im * (ψ b).im := by
  rw [ψ.map_sub_eq_div, div_eq_mul_inv, ψ.inv_apply_eq_conj, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem weight_nonneg (b : G → ℝ)
    (h : ∀ c : G → ℝ, 0 ≤ ∑ a, ∑ a', c a*c a'*b (a-a')) (ψ : AddChar G ℂ) :
    0 ≤ weight b ψ := by
  have hpos : 0 ≤ ∑ a, ∑ a', b (a-a')*(ψ (a-a')).re := by
    have he : (∑ a, ∑ a', b (a-a')*(ψ (a-a')).re) =
        (∑ a, ∑ a', (ψ a).re*(ψ a').re*b (a-a')) +
        (∑ a, ∑ a', (ψ a).im*(ψ a').im*b (a-a')) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a' _
      rw [character_diff_re]
      ring
    rw [he]
    exact add_nonneg (h (fun a => (ψ a).re)) (h (fun a => (ψ a).im))
  have hrow (a : G) :
      (∑ a', b (a-a')*(ψ (a-a')).re) = ∑ z, b z*(ψ z).re :=
    Equiv.sum_comp (Equiv.subLeft a) (fun z => b z*(ψ z).re)
  simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hpos
  have hcard : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  exact div_nonneg (nonneg_of_mul_nonneg_right hpos hcard) hcard.le

private theorem dual_real_sum [DecidableEq G] (z : G) :
    (∑ ψ : AddChar G ℂ, (ψ z).re) = if z = 0 then (Fintype.card G : ℝ) else 0 := by
  rw [← Complex.re_sum, AddChar.sum_apply_eq_ite]
  split_ifs <;> simp

private theorem dual_real_product [DecidableEq G] (z a : G) :
    (∑ ψ : AddChar G ℂ, 2*(ψ z).re*(ψ a).re) =
      (if z = -a then (Fintype.card G : ℝ) else 0) +
        (if z = a then (Fintype.card G : ℝ) else 0) := by
  calc
    _ = ∑ ψ : AddChar G ℂ, ((ψ (z+a)).re + (ψ (z-a)).re) := by
      apply Finset.sum_congr rfl
      intro ψ _
      rw [ψ.map_add_eq_mul, Complex.mul_re, character_diff_re]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, dual_real_sum, sub_eq_zero, add_eq_zero_iff_eq_neg]

private theorem fourier_recover (b : G → ℝ) (heven : ∀ z, b (-z) = b z) (a : G) :
    (∑ ψ : AddChar G ℂ, weight b ψ*(ψ a).re) = b a := by
  classical
  have hcard : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have he (z : G) : (∑ ψ : AddChar G ℂ, b z*(2*(ψ z).re*(ψ a).re)) =
      (if z = -a then b z*(Fintype.card G) else 0) +
      (if z = a then b z*(Fintype.card G) else 0) := by
    rw [← Finset.mul_sum, dual_real_product, mul_add]
    split_ifs <;> simp
  have htotal :
      (∑ ψ : AddChar G ℂ, ∑ z : G, b z*(2*(ψ z).re*(ψ a).re)) =
        2*(b a*(Fintype.card G)) := by
    rw [Finset.sum_comm]
    simp only [he, Finset.sum_add_distrib]
    simp [heven, two_mul]
  have hunit (ψ : AddChar G ℂ) :
      (2*(Fintype.card G : ℝ))*(weight b ψ*(ψ a).re) =
        ∑ z, b z*(2*(ψ z).re*(ψ a).re) := by
    unfold weight
    calc
      _ = (∑ z, b z*(ψ z).re)*(2*(ψ a).re) := by field_simp
      _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
  have hh : (2*(Fintype.card G : ℝ))*(∑ ψ : AddChar G ℂ, weight b ψ*(ψ a).re) =
      2*(b a*(Fintype.card G)) := by
    rw [Finset.mul_sum]
    simpa only [hunit] using htotal
  nlinarith [hcard]

private def basisSite (i : Fin 3) : Site := Pi.single i (1 : ℤ)

private def characterMomentum (π : Site →+ G) (ψ : AddChar G ℂ) : Momentum :=
  fun i => ⟨ψ (π (basisSite i)), mem_sphere_zero_iff_norm.2 (ψ.norm_apply _)⟩

private theorem characterMomentum_value (π : Site →+ G) (ψ : AddChar G ℂ) (z : Site) :
    realCharacter z (characterMomentum π ψ) = (ψ (π z)).re := by
  have hz : z = z 0 • basisSite 0 + z 1 • basisSite 1 + z 2 • basisSite 2 := by
    ext i
    fin_cases i <;> simp [basisSite]
  conv_rhs => rw [hz]
  simp only [map_add, map_zsmul, ψ.map_add_eq_mul, ψ.map_zsmul_eq_zpow]
  unfold realCharacter
  simp [characterMomentum, Fin.prod_univ_three, mul_assoc]

/-- The normalized character masses of a finite stationary real Gram kernel
give the three-dimensional momentum measure of its lattice pullback. -/
theorem finite_gram_momentum (π : Site →+ G) (b : G → ℝ) (h0 : b 0 = 1)
    (heven : ∀ z, b (-z) = b z)
    (hgram : ∀ c : G → ℝ, 0 ≤ ∑ a, ∑ a', c a*c a'*b (a-a')) :
    ∃ μ : ProbabilityMeasure Momentum, ∀ z, spectralPair (μ : Measure Momentum) z = b (π z) := by
  classical
  let w (ψ : AddChar G ℂ) := weight b ψ
  have hw (ψ : AddChar G ℂ) : 0 ≤ w ψ := weight_nonneg b hgram ψ
  have hsum : ∑ ψ, w ψ = 1 := by simpa [w, h0] using fourier_recover b heven 0
  let atom (ψ : AddChar G ℂ) : Measure Momentum :=
    ENNReal.ofReal (w ψ) • Measure.dirac (characterMomentum π ψ)
  have hi (ψ : AddChar G ℂ) : IsFiniteMeasure (atom ψ) :=
    (Measure.dirac (characterMomentum π ψ)).smul_finite ENNReal.ofReal_ne_top
  let μ : Measure Momentum := ∑ ψ, atom ψ
  have hμ : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.finsetSum_apply, atom, Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum, ENNReal.ofReal_one]
  refine ⟨⟨μ,hμ⟩, fun z => ?_⟩
  change (∫ k, realCharacter z k ∂(∑ ψ, atom ψ)) = _
  rw [integral_finsetSum_measure (fun ψ _ => by
    let : IsFiniteMeasure (atom ψ) := hi ψ
    exact (realCharacter z).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [atom, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _),
    smul_eq_mul, characterMomentum_value]
  exact fourier_recover b heven (π z)

end FiniteFourier

section Fields

theorem stationary_dot_integral {N : ℕ} {P : ProbabilityMeasure (SpinField N)}
    (hP : ShiftInvariant P) (x y : Site) :
    (∫ s, fieldDot N x y s ∂(P : Measure _)) = fieldPair P (x-y) := by
  unfold fieldPair
  conv_rhs => rw [← (hP y).map_eq]
  rw [integral_map (hP y).measurable.aemeasurable (fieldDot N 0 (x-y)).continuous.aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun s => by
    change ⟪(s x).val,(s y).val⟫_ℝ = ⟪(s (0+y)).val,(s ((x-y)+y)).val⟫_ℝ
    rw [zero_add, sub_add_cancel, real_inner_comm])

theorem fieldPair_even {N : ℕ} {P : ProbabilityMeasure (SpinField N)} (hP : ShiftInvariant P)
    (z : Site) : fieldPair P (-z) = fieldPair P z := by
  have h := (stationary_dot_integral hP 0 z).symm
  rw [zero_sub] at h
  exact h

theorem fieldPair_zero {N : ℕ} (P : ProbabilityMeasure (SpinField N)) : fieldPair P 0 = 1 := by
  unfold fieldPair
  have he (s : SpinField N) : fieldDot N 0 0 s = 1 := by
    change ⟪(s 0).val,(s 0).val⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp (s 0).property, one_pow]
  simp [he]

theorem fieldPair_gram {N : ℕ} {P : ProbabilityMeasure (SpinField N)} (hP : ShiftInvariant P)
    {ι : Type*} [Fintype ι] (x : ι → Site) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair P (x i - x j) := by
  classical
  let v (s : SpinField N) := ∑ i, c i • (s (x i)).val
  let F (i j : ι) (s : SpinField N) := c i*c j * fieldDot N (x i) (x j) s
  have hf (i j : ι) : Continuous (F i j) := continuous_const.mul (fieldDot N (x i) (x j)).continuous
  have hpos (s : SpinField N) : 0 ≤ ∑ i, ∑ j, F i j s := by
    calc
      0 ≤ ⟪v s, v s⟫_ℝ := real_inner_self_nonneg
      _ = _ := by
        simp only [v, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [F, fieldDot]
        rw [real_inner_comm (s (x j)).val (s (x i)).val]
        ring
  have key : 0 ≤ ∫ s, ∑ i, ∑ j, F i j s ∂(P : Measure _) := integral_nonneg hpos
  rw [integral_finsetSum _ (fun i _ =>
    (continuous_finsetSum _ (fun j _ => hf i j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))] at key
  simp_rw [integral_finsetSum _ (fun j _ => (hf _ j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))] at key
  simpa only [F, integral_const_mul, stationary_dot_integral hP] using key

def DisplacementAction.hom {V : Type*} {D : Site → V → V} (h : DisplacementAction D) :
    Site →+ Additive (Equiv.Perm V) where
  toFun z := Additive.ofMul (h.shiftEquiv z)
  map_zero' := by
    change h.shiftEquiv 0 = Equiv.refl V
    exact Equiv.ext h.zero
  map_add' x y := by
    change h.shiftEquiv (x+y) = h.shiftEquiv x * h.shiftEquiv y
    exact Equiv.ext (h.add x y)

/-- The actual averaged dot pair on every finite displacement action is
the complete Fourier moment profile of a single probability measure. -/
theorem periodic_gram_spectrum (N : ℕ) [NeZero N] {V : Type*} [Fintype V] [Nonempty V]
    (D : Site → V → V) (hD : DisplacementAction D) (H : V → V → ℝ) :
    ∃ μ : ProbabilityMeasure Momentum, ∀ z,
      spectralPair (μ : Measure Momentum) z = averagedDot N D H z := by
  classical
  let A := Site ⧸ hD.hom.ker
  let π : Site →+ A := QuotientAddGroup.mk' _
  let : Finite A := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange hD.hom).symm.toEquiv
  letI : Fintype A := Fintype.ofFinite A
  choose r hr using (QuotientAddGroup.mk'_surjective hD.hom.ker)
  let P := rootedLaw N D H
  have hP := rootedLaw_invariant N D hD H
  let b (a : A) := fieldPair P (r a)
  have respects (z w : Site) (h : π z = π w) : fieldPair P z = fieldPair P w := by
    obtain ⟨u,hu,hzu⟩ := (QuotientAddGroup.mk'_eq_mk' hD.hom.ker).mp h
    have hu' : hD.hom u = 0 := hu
    have he : hD.hom z = hD.hom w := by rw [← hzu, map_add, hu', add_zero]
    simp only [P, fieldPair_rootedLaw N D hD.zero, averagedDot]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    exact congrArg (dotPair N H v) (congrArg (fun e : Additive (Equiv.Perm V) => e.toMul v) he)
  have hb (z : Site) : b (π z) = fieldPair P z := respects (r (π z)) z (hr _)
  have h0 : b 0 = 1 := by simpa only [map_zero, fieldPair_zero] using hb 0
  have heven (a : A) : b (-a) = b a := by
    have he := hb (-(r a))
    simp only [map_neg, show π (r a) = a from hr a] at he
    exact he.trans (fieldPair_even (P := P) hP (r a))
  have hg (c : A → ℝ) : 0 ≤ ∑ a, ∑ a', c a*c a'*b (a-a') := by
    have h := fieldPair_gram hP r c
    have he (a a' : A) : b (a-a') = fieldPair P (r a-r a') := by
      simpa only [map_sub, show ∀ v : A, π (r v) = v from hr] using hb (r a-r a')
    simpa only [he] using h
  obtain ⟨μ,hμ⟩ := finite_gram_momentum π b h0 heven hg
  exact ⟨μ, fun z => (hμ z).trans ((hb z).trans (fieldPair_rootedLaw N D hD.zero H z))⟩

end Fields

def HasMomentumLaw (g : Site → ℝ) : Prop :=
  ∃ μ : ProbabilityMeasure Momentum, ∀ z, spectralPair (μ : Measure Momentum) z = g z

theorem HasMomentumLaw.of_pointwise_limit {g : ℕ → Site → ℝ} {b : Site → ℝ}
    (hm : ∀ n, HasMomentumLaw (g n)) (hb : ∀ z, Tendsto (fun n => g n z) atTop (𝓝 (b z))) :
    HasMomentumLaw b := by
  choose μ hμ using hm
  obtain ⟨ν,l,hl,hν⟩ := CompactSpace.tendsto_subseq μ
  refine ⟨ν, fun z => ?_⟩
  have h := (ProbabilityMeasure.continuous_integral_continuousMap (realCharacter z)).continuousAt.tendsto.comp hν
  change Tendsto (fun n => spectralPair ((μ (l n)) : Measure Momentum) z) atTop
    (𝓝 (spectralPair (ν : Measure Momentum) z)) at h
  simp only [hμ] at h
  exact tendsto_nhds_unique h ((hb z).comp hl.tendsto_atTop)

/-- Every pointwise limit of the true cubic periodic pair averages carries
a probability spectral measure; it does not require an assumed Fourier law. -/
theorem cubic_limit_momentum (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : ℕ → Site → ℝ) {g : Site → ℝ}
    (hg : ∀ z, Tendsto (fun n => cubicPair N (sides n) (J n) z) atTop (𝓝 (g z))) :
    HasMomentumLaw g :=
  HasMomentumLaw.of_pointwise_limit (fun n => periodic_gram_spectrum N Seam.baseMove
    (Seam.cubic_displacement_action (sides n)) (Seam.ordinarySeries (sides n) (J n))) hg

theorem diagonal_limit_momentum (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : ℕ → Site → ℝ) {g : Site → ℝ}
    (hg : ∀ z, Tendsto (fun n => diagonalPair N (sides n) (J n) z) atTop (𝓝 (g z))) :
    HasMomentumLaw g :=
  HasMomentumLaw.of_pointwise_limit (fun n => periodic_gram_spectrum N Seam.adaptedDestination
    (Seam.adapted_displacement_action (sides n)) (Seam.adaptedSeries (sides n) (J n))) hg

/-- One full stationary sphere-spin state and its three-dimensional momentum
probability describe the same physical cubic subsequence. -/
theorem cubic_spin_and_momentum_limit (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : ℕ → Site → ℝ) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ μ : ProbabilityMeasure Momentum, ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant Q ∧
      Tendsto (fun j => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides (l j)) (J (l j))))
        atTop (𝓝 Q) ∧ (∀ z, spectralPair (μ : Measure Momentum) z = fieldPair Q z) ∧
      ∀ z, Tendsto (fun j => cubicPair N (sides (l j)) (J (l j)) z) atTop (𝓝 (fieldPair Q z)) := by
  obtain ⟨Q,l,hl,hQ,hconv,hg⟩ := cubic_spin_limit N sides J
  obtain ⟨μ,hμ⟩ := cubic_limit_momentum N (fun j => sides (l j)) (fun j => J (l j)) hg
  exact ⟨Q,μ,l,hl,hQ,hconv,hμ,hg⟩

theorem diagonal_spin_and_momentum_limit (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (J : ℕ → Site → ℝ) :
    ∃ Q : ProbabilityMeasure (SpinField N), ∃ μ : ProbabilityMeasure Momentum, ∃ l : ℕ → ℕ,
      StrictMono l ∧ ShiftInvariant Q ∧
      Tendsto (fun j => rootedLaw N Seam.adaptedDestination
        (Seam.adaptedSeries (sides (l j)) (J (l j)))) atTop (𝓝 Q) ∧
      (∀ z, spectralPair (μ : Measure Momentum) z = fieldPair Q z) ∧
      ∀ z, Tendsto (fun j => diagonalPair N (sides (l j)) (J (l j)) z) atTop (𝓝 (fieldPair Q z)) := by
  obtain ⟨Q,l,hl,hQ,hconv,hg⟩ := diagonal_spin_limit N sides J
  obtain ⟨μ,hμ⟩ := diagonal_limit_momentum N (fun j => sides (l j)) (fun j => J (l j)) hg
  exact ⟨Q,μ,l,hl,hQ,hconv,hμ,hg⟩

end IsingScaling.Rotor.PressureSelection

#print axioms IsingScaling.Rotor.PressureSelection.finite_gram_momentum
#print axioms IsingScaling.Rotor.PressureSelection.periodic_gram_spectrum
#print axioms IsingScaling.Rotor.PressureSelection.cubic_spin_and_momentum_limit
#print axioms IsingScaling.Rotor.PressureSelection.diagonal_spin_and_momentum_limit
