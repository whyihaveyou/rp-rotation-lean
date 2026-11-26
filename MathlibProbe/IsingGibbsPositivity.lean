import MathlibProbe.IsingTwoPointTangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! First Griffiths inequality for the finite Gibbs sums used by the
tangent definition. This also certifies positivity of the susceptibility
denominators for limits of these actual sums. -/
open Finset Filter MeasureTheory
open scoped Topology BigOperators CompactlySupported
noncomputable section
namespace IsingScaling

private def spinFlip {V : Type*} (η σ : V → Bool) : V → Bool :=
  fun i => if η i then σ i else !(σ i)

private def flipPerm {V : Type*} (η : V → Bool) : Equiv.Perm (V → Bool) where
  toFun := spinFlip η
  invFun := spinFlip η
  left_inv σ := by funext i; cases h : η i <;> simp [spinFlip, h]
  right_inv σ := by funext i; cases h : η i <;> simp [spinFlip, h]

private structure SpinMonomial {V : Type*} (F : (V → Bool) → ℝ) : Prop where
  sign : ∀ σ, F σ = 1 ∨ F σ = -1
  flip : ∀ η σ, F (spinFlip η σ) = F η * F σ

private theorem site_monomial {V : Type*} (i : V) :
    SpinMonomial (fun σ => value (σ i)) where
  sign σ := by cases σ i <;> simp [value]
  flip η σ := by cases h : η i <;> cases h' : σ i <;> simp [spinFlip, value, h, h']

private theorem SpinMonomial.mul {V : Type*} {F G : (V → Bool) → ℝ}
    (hF : SpinMonomial F) (hG : SpinMonomial G) :
    SpinMonomial (fun σ => F σ * G σ) where
  sign σ := by rcases hF.sign σ with h|h <;> rcases hG.sign σ with h'|h' <;> simp [h,h']
  flip η σ := by rw [hF.flip, hG.flip]; ring

private theorem sum_character_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {F : (V → Bool) → ℝ} (hF : SpinMonomial F) : 0 ≤ ∑ σ, F σ := by
  classical
  by_cases h : ∀ σ, F σ = 1
  · exact Finset.sum_nonneg fun σ _ => by rw [h]; norm_num
  · push Not at h
    obtain ⟨η,hη⟩ := h
    have hm := (hF.sign η).resolve_left hη
    have eq := Equiv.sum_comp (flipPerm η) F
    have he (σ : V → Bool) : F (flipPerm η σ) = -F σ := by
      change F (spinFlip η σ) = _
      rw [hF.flip, hm, neg_one_mul]
    simp only [he, Finset.sum_neg_distrib] at eq
    linarith

private theorem gibbs_monomial_nonneg {V E : Type*} [Fintype V] [DecidableEq V]
    (K : Finset E) (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (B : E → (V → Bool) → ℝ) (hB : ∀ e, SpinMonomial (B e))
    (F : (V → Bool) → ℝ) (hF : SpinMonomial F) :
    0 ≤ ∑ σ, F σ * Real.exp (∑ e ∈ K, J e * B e σ) := by
  classical
  induction K using Finset.induction_on generalizing F with
  | empty => simpa using sum_character_nonneg hF
  | @insert e S he ih =>
    let W (σ : V → Bool) := Real.exp (∑ j ∈ S, J j * B j σ)
    have exp_term (σ : V → Bool) :
        Real.exp (J e * B e σ) = Real.cosh (J e) + B e σ * Real.sinh (J e) := by
      rcases (hB e).sign σ with h|h <;> simp [h, Real.cosh_eq, Real.sinh_eq] <;> ring
    have hex (σ : V → Bool) :
        F σ * Real.exp (∑ j ∈ insert e S, J j * B j σ) =
        Real.cosh (J e) * (F σ * W σ) + Real.sinh (J e) * ((F σ * B e σ) * W σ) := by
      rw [sum_insert he, Real.exp_add, exp_term]
      dsimp [W]
      ring
    simp only [hex, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_nonneg (mul_nonneg (Real.cosh_pos _).le (ih F hF))
      (mul_nonneg (Real.sinh_nonneg_iff.mpr (hJ e)) (ih _ (hF.mul (hB e))))

private theorem freePartition_pos (β : ℝ) (L : ℕ) : 0 < ∑ σ : Spin L, gibbsWeight β L σ :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private theorem spinFlip_comm {V : Type*} (η σ : V → Bool) : spinFlip η σ = spinFlip σ η := by
  funext i
  cases h : η i <;> cases h' : σ i <;> simp [spinFlip,h,h']

/-- The replica change of variables gives the second Griffiths inequality.
Each fixed relative spin configuration leaves ferromagnetic couplings. -/
private theorem gibbs_covariance_nonneg {V E : Type*} [Fintype V] [DecidableEq V]
    (K : Finset E) (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (B : E → (V → Bool) → ℝ) (hB : ∀ e, SpinMonomial (B e))
    (F G : (V → Bool) → ℝ) (hF : SpinMonomial F) (hG : SpinMonomial G) :
    let W (σ : V → Bool) := Real.exp (∑ e ∈ K, J e * B e σ)
    (∑ σ, W σ * F σ) * (∑ σ, W σ * G σ) ≤
      (∑ σ, W σ * F σ * G σ) * ∑ σ, W σ := by
  classical
  dsimp only
  let W (σ : V → Bool) := Real.exp (∑ e ∈ K, J e * B e σ)
  let f (σ τ : V → Bool) := W σ * W τ * (F σ-F τ) * (G σ-G τ)
  have hprod (η σ : V → Bool) : W σ * W (spinFlip η σ) =
      Real.exp (∑ e ∈ K, (J e * (1+B e η)) * B e σ) := by
    unfold W
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [(hB e).flip]
    ring
  have hη (η : V → Bool) : 0 ≤ ∑ σ, f σ (spinFlip η σ) := by
    have hplus (e : E) : 0 ≤ J e * (1+B e η) := by
      apply mul_nonneg (hJ e)
      rcases (hB e).sign η with h|h <;> rw [h] <;> norm_num
    have ht := gibbs_monomial_nonneg K _ hplus B hB _ (hF.mul hG)
    have nonneg_of_sign (A : (V → Bool) → ℝ) (hA : SpinMonomial A) : 0 ≤ 1 - A η := by
      rcases hA.sign η with h|h <;> rw [h] <;> norm_num
    apply (mul_nonneg (mul_nonneg (nonneg_of_sign F hF) (nonneg_of_sign G hG)) ht).trans_eq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [f]
    rw [hprod, hF.flip, hG.flip]
    ring
  have htotal : 0 ≤ ∑ σ, ∑ τ, f σ τ := by
    have hpos := Finset.sum_nonneg (s := Finset.univ) fun η _ => hη η
    rw [Finset.sum_comm] at hpos
    apply hpos.trans_eq
    apply Finset.sum_congr rfl
    intro σ _
    calc
      _ = ∑ η, f σ (flipPerm σ η) := Finset.sum_congr rfl fun η _ =>
        congrArg (f σ) (spinFlip_comm η σ)
      _ = _ := Equiv.sum_comp (flipPerm σ) (f σ)
  have hex (σ τ : V → Bool) : f σ τ =
      (W σ*F σ*G σ)*W τ + W σ*(W τ*F τ*G τ) -
      (W σ*F σ)*(W τ*G τ) - (W σ*G σ)*(W τ*F τ) := by dsimp only [f]; ring
  simp only [hex, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at htotal
  change (∑ σ, W σ * F σ) * (∑ σ, W σ * G σ) ≤ (∑ σ, W σ * F σ * G σ) * ∑ σ, W σ
  linarith only [htotal]

/-- Unnormalized Griffiths covariance for two spin pairs on any finite
ferromagnetic graph, with arbitrary inhomogeneous bond weights. -/
theorem finite_pair_covariance_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (K : Finset (V × V)) (J : V × V → ℝ) (hJ : ∀ e, 0 ≤ J e) (a b c d : V) :
    let pair (i j : V) (σ : V → Bool) := value (σ i)*value (σ j)
    let W (σ : V → Bool) := Real.exp (∑ e ∈ K, J e * pair e.1 e.2 σ)
    (∑ σ, W σ * pair a b σ) * (∑ σ, W σ * pair c d σ) ≤
       (∑ σ, W σ * pair a b σ * pair c d σ) * ∑ σ, W σ :=
  gibbs_covariance_nonneg K J hJ _ (fun e => (site_monomial e.1).mul (site_monomial e.2))
    _ _ ((site_monomial a).mul (site_monomial b)) ((site_monomial c).mul (site_monomial d))

def bondScore {V : Type*} (e : V × V) (σ : V → Bool) : ℝ :=
  value (σ e.1) * value (σ e.2)

def bondWeight {V : Type*} (K : Finset (V × V)) (J : V × V → ℝ) (σ : V → Bool) : ℝ :=
  Real.exp (∑ e ∈ K, J e * bondScore e σ)

def graphPair {V : Type*} [Fintype V] [DecidableEq V]
    (K : Finset (V × V)) (J : V × V → ℝ) (p : V × V) : ℝ :=
  (∑ σ : V → Bool, bondWeight K J σ * bondScore p σ) / ∑ σ : V → Bool, bondWeight K J σ

private theorem graphPair_insert {V : Type*} [Fintype V] [DecidableEq V]
    (K : Finset (V × V)) (J : V × V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (p e : V × V) (he : e ∉ K) : graphPair K J p ≤ graphPair (insert e K) J p := by
  classical
  let W := bondWeight K J
  let Z := ∑ σ : V → Bool, W σ
  let N (p : V × V) := ∑ σ : V → Bool, W σ * bondScore p σ
  let T := ∑ σ : V → Bool, W σ * bondScore p σ * bondScore e σ
  let c := Real.cosh (J e)
  let s := Real.sinh (J e)
  have hinc (σ : V → Bool) : bondWeight (insert e K) J σ = W σ * (c + s * bondScore e σ) := by
    rw [bondWeight, sum_insert he, Real.exp_add, mul_comm]
    apply congrArg (W σ * ·)
    rcases ((site_monomial e.1).mul (site_monomial e.2)).sign σ with h|h <;>
      change bondScore e σ = _ at h <;> simp [h,c,s,Real.cosh_eq,Real.sinh_eq] <;> ring
  have hZ (S : Finset (V × V)) : 0 < ∑ σ : V → Bool, bondWeight S J σ :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold graphPair
  rw [div_le_div_iff₀ (hZ K) (hZ _)]
  have h1 : (∑ σ : V → Bool, bondWeight (insert e K) J σ) = c*Z+s*N e := by
    dsimp only [Z,N]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => (hinc σ).trans (by ring)
  have h2 : (∑ σ : V → Bool, bondWeight (insert e K) J σ * bondScore p σ) =
      c*N p+s*T := by
    dsimp only [N,T]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hinc]
    ring
  rw [h1,h2]
  have hcov : N p * N e ≤ T*Z := finite_pair_covariance_nonneg K J hJ p.1 p.2 e.1 e.2
  have hs : 0 ≤ s := Real.sinh_nonneg_iff.mpr (hJ e)
  change N p * (c*Z + s*N e) ≤ (c*N p+s*T)*Z
  linarith only [mul_le_mul_of_nonneg_left hcov hs]

/-- Free spin correlations increase under any enlargement of the edge set
on a fixed finite vertex space. -/
theorem graphPair_mono {V : Type*} [Fintype V] [DecidableEq V] {K K' : Finset (V × V)}
    (h : K ⊆ K') (J : V × V → ℝ) (hJ : ∀ e, 0 ≤ J e) (p : V × V) :
    graphPair K J p ≤ graphPair K' J p := by
  have extend (S : Finset (V × V)) : graphPair K J p ≤ graphPair (S ∪ K) J p := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert e S _ ih =>
      rw [Finset.insert_union]
      by_cases he : e ∈ S ∪ K
      · simpa [Finset.insert_eq_of_mem he] using ih
      · exact ih.trans (graphPair_insert _ J hJ p e he)
  simpa only [Finset.union_eq_left.mpr h] using extend K'

@[simp] private theorem zero_mem_cube (L : ℕ) : (0 : Site) ∈ cube L := by
  simp [cube, Fintype.mem_piFinset]

theorem freeTwoPoint_zero (β : ℝ) (L : ℕ) : freeTwoPoint β L 0 = 1 := by
  have hh (σ : Spin L) : gibbsWeight β L σ * occupation L σ 0 * occupation L σ 0 =
      gibbsWeight β L σ := by
    simp only [occupation, dite_eq_left (zero_mem_cube L), value]
    split <;> ring
  simp only [freeTwoPoint, hh, div_self (freePartition_pos β L).ne']

theorem freeTwoPoint_nonneg {β : ℝ} (hβ : 0 ≤ β) (L : ℕ) (x : Site) :
    0 ≤ freeTwoPoint β L x := by
  classical
  unfold freeTwoPoint
  apply div_nonneg _ (freePartition_pos _ _).le
  by_cases hx : x ∈ cube L
  · let V := ↥(cube L)
    let J (e : V × V) : ℝ := if latticeDistance e.1 e.2 = 1 then β/2 else 0
    let B (e : V × V) (σ : V → Bool) := value (σ e.1) * value (σ e.2)
    have hW (σ : Spin L) :
        Real.exp (∑ e : V × V, J e * B e σ) = gibbsWeight β L σ := by
      congr 1
      rw [Fintype.sum_prod_type]
      unfold interaction
      rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [J,B]
      split <;> ring
    have h := gibbs_monomial_nonneg (V:=V) Finset.univ J
      (fun e => by dsimp [J]; split <;> positivity) B
      (fun e => (site_monomial e.1).mul (site_monomial e.2))
      _ ((site_monomial (⟨0,zero_mem_cube L⟩ : V)).mul (site_monomial (⟨x,hx⟩ : V)))
    apply h.trans_eq
    apply Finset.sum_congr rfl
    intro σ _
    rw [hW]
    simp only [occupation, dite_eq_left (zero_mem_cube L), dite_eq_left hx]
    ring
  · simp [occupation,hx]

theorem IsFreeTwoPoint.positive_cube_mass {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    (∀ x, 0 ≤ g x) ∧ ∀ R, 0 < susceptibility g R := by
  have hp (x) : 0 ≤ g x :=
    ge_of_tendsto (hg x) (Eventually.of_forall fun L => freeTwoPoint_nonneg hβ L x)
  have h0 : g 0 = 1 := tendsto_nhds_unique (hg 0) (by
    simp only [freeTwoPoint_zero]
    exact tendsto_const_nhds)
  exact ⟨hp, fun R => lt_of_lt_of_le (by rw [h0]; norm_num : 0 < g 0)
    (Finset.single_le_sum (fun x _ => hp x) (zero_mem_cube R))⟩

/-- For ferromagnetic inverse temperature, every locally vague limit of the
normalized free correlations is a tangent in the sense used by AS-7. -/
theorem IsTwoPointTangent.of_free_vagueLimit {β : ℝ} (hβ : 0 ≤ β)
    {g : Site → ℝ} (hg : IsFreeTwoPoint β g) (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    {μ : Measure Space} (hlim : ∀ f : C_c(Space, ℝ),
      Tendsto (fun j => ∫ x, f x ∂twoPointMeasure g (R j)) atTop (𝓝 (∫ x, f x ∂μ))) :
    IsTwoPointTangent β μ := by
  obtain ⟨hp, hχ⟩ := hg.positive_cube_mass hβ
  exact ⟨g, R, hg, hp, fun j => hχ (R j), hR, hlim⟩

/-- The pair numerator stays nonnegative when labelled ferromagnetic bonds share
endpoints, as happens after folding a site mirror. -/
theorem finite_pair_bond_sum_nonneg {V E : Type*} [Fintype V] [DecidableEq V]
    (K : Finset E) (edge : E → V × V) (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (a b : V) :
    0 ≤ ∑ σ : V → Bool, (value (σ a) * value (σ b)) *
      Real.exp (∑ e ∈ K, J e * (value (σ (edge e).1) * value (σ (edge e).2))) :=
  gibbs_monomial_nonneg K J hJ
    _ (fun e => (site_monomial (edge e).1).mul (site_monomial (edge e).2))
    _ ((site_monomial a).mul (site_monomial b))

end IsingScaling
