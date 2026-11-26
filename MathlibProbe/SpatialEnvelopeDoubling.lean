import MathlibProbe.IsingTwoPointTangent

/-!
# Susceptibility bound for a scalar pair function on the cubic lattice

Let g be a nonnegative even stationary covariance with g(0) = 1 and g ≤ 1.
Write U(r) for its supremum outside the open cube of radius r. Assume the
local oscillation estimate (4.2) above an integer threshold r₀. Choose an
integer M ≥ 80 so large that 4 C D³ ≤ M. At scale r put m = ⌊r/M⌋ and
S = Λ_m. For p,q in S, (4.2) applies to the displacement p-q, of size at
most 2m. Stationary covariance positivity, tested on the difference of two
translated block sums, gives

  ∑_{p,q ∈ S} g(x + p - q) ≤ ∑_{p,q ∈ S} g(p - q) ≤ |S| χ_r.

The second inequality follows by summing each row over its distinct
displacements, all in Λ_r. Averaging (4.2) over p,q therefore bounds
U(r) by χ_r/|S| + (2C/M) U(⌊r/D⌋). Use r+1 as the scale factor:
|S| ≥ (m+1)³, r+1 ≤ M(m+1) and r+1 ≤ D(⌊r/D⌋+1). Since χ is
nondecreasing, strong induction absorbs the second coefficient, at most
1/2. Boundedness of g and χ ≥ g(0) handle every initial radius. This
argument uses no doubling or decay assumption on χ.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace IsingScaling.SpatialEnvelope

/-- The boundary of the radius-r cube is included in the supremum. -/
def outside (r : ℕ) (x : Site) : Prop := ∃ i, r ≤ (x i).natAbs

/-- Adjoining zero makes the supremum nonempty and preserves its value for
a nonnegative kernel. -/
def tail (g : Site → ℝ) (r : ℕ) : ℝ :=
  sSup (insert 0 (g '' {x | outside r x}))

private theorem bounded_tailSet {g : Site → ℝ} (hg : ∀ x, g x ≤ 1) (r : ℕ) :
    BddAbove (insert 0 (g '' {x | outside r x})) := by
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with h | ⟨x, _, rfl⟩
  · simp [h]
  · exact hg x

theorem tail_nonneg {g : Site → ℝ} (hg : ∀ x, g x ≤ 1) (r : ℕ) :
    0 ≤ tail g r :=
  le_csSup (bounded_tailSet hg r) (Set.mem_insert _ _)

theorem le_tail {g : Site → ℝ} (hg : ∀ x, g x ≤ 1) {r : ℕ} {x : Site}
    (hx : outside r x) : g x ≤ tail g r :=
  le_csSup (bounded_tailSet hg r) (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)

theorem tail_le {g : Site → ℝ} {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x, outside r x → g x ≤ b) : tail g r ≤ b := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro y (rfl | ⟨x, hx, rfl⟩)
  · exact hb
  · exact h x hx

/-- Finite stationary covariance quadratic forms, including lists with
coincident sites. -/
def StationaryPositive (g : Site → ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → Site) (c : ι → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * g (x i - x j)

/-- The translated block covariance bound (4.3), before normalizing by
the block size. -/
theorem translated_block_le_center {g : Site → ℝ}
    (hsym : ∀ z, g (-z) = g z) (hpos : StationaryPositive g)
    (S : Finset Site) (x : Site) :
    (∑ p ∈ S, ∑ q ∈ S, g (x + (p - q))) ≤
      ∑ p ∈ S, ∑ q ∈ S, g (p - q) := by
  classical
  let X : (↥S ⊕ ↥S) → Site := Sum.elim (fun p => x + p.val) Subtype.val
  let c : (↥S ⊕ ↥S) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have H := hpos X c
  have hdiag (p q : ↥S) : x + p.val - (x + q.val) = p.val - q.val := by abel
  have hforward (p q : ↥S) : x + p.val - q.val = x + (p.val - q.val) := by abel
  have hback (p q : ↥S) : g (p.val - (x + q.val)) = g (x + (q.val - p.val)) := by
    rw [← hsym (x + (q.val - p.val))]
    congr 1
    abel
  simp only [Fintype.sum_sum_type, X, c, Sum.elim_inl, Sum.elim_inr, one_mul,
    neg_one_mul, neg_neg, hdiag, hforward, hback, Finset.sum_neg_distrib,
    Finset.sum_add_distrib] at H
  have hswap : (∑ p : ↥S, ∑ q : ↥S, g (x + (q.val - p.val))) =
      ∑ p : ↥S, ∑ q : ↥S, g (x + (p.val - q.val)) := Finset.sum_comm
  rw [hswap] at H
  have hco (F : Site → Site → ℝ) :
      (∑ p : ↥S, ∑ q : ↥S, F p.val q.val) = ∑ p ∈ S, ∑ q ∈ S, F p q := calc
    _ = ∑ p : ↥S, ∑ q ∈ S, F p.val q := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_coe_sort S (F p.val)
    _ = _ := Finset.sum_coe_sort S (fun p => ∑ q ∈ S, F p q)
  rw [← hco (fun p q => g (x+(p-q))), ← hco (fun p q => g (p-q))]
  linarith

/-- A singleton translated block gives the zero-displacement maximum,
including for unnormalized marks of variance smaller than one. -/
theorem le_origin_of_stationary {g : Site → ℝ} (hsym : ∀ z, g (-z) = g z)
    (hpos : StationaryPositive g) (x : Site) : g x ≤ g 0 := by
  simpa using translated_block_le_center hsym hpos ({0} : Finset Site) x

private theorem sub_mem_cube {m : ℕ} {p q : Site} (hp : p ∈ cube m) (hq : q ∈ cube m) :
    p - q ∈ cube (2*m) := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hp hq ⊢
  intro i
  simp only [Pi.sub_apply]
  have := hp i
  have := hq i
  omega

private theorem cube_subset {m r : ℕ} (h : m ≤ r) : cube m ⊆ cube r := by
  intro x hx
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  intro i
  have := hx i
  omega

private theorem cube_mass_mono {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    {m r : ℕ} (h : m ≤ r) : susceptibility g m ≤ susceptibility g r :=
  Finset.sum_le_sum_of_subset_of_nonneg (cube_subset h) (fun x _ _ => hn x)

private theorem one_le_cube_mass {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (h0 : g 0 = 1) (r : ℕ) : 1 ≤ susceptibility g r := by
  rw [← h0]
  apply Finset.single_le_sum (f := g) (fun x _ => hn x)
  simp [cube, Fintype.mem_piFinset]

private theorem cubeCard (m : ℕ) : (cube m).card = (2*m+1)^3 := by
  rw [cube, Fintype.card_piFinset_const, Int.card_Icc]
  have h : ((m:ℤ)+1 - (-(m:ℤ))).toNat = 2*m+1 := by omega
  rw [h]

/-- Every ordered difference of two points in the centered cube of radius
m belongs to the cube of radius 2m. Each row charges a displacement once. -/
theorem center_block_le_susceptibility {g : Site → ℝ} (hn : ∀ x, 0 ≤ g x)
    (m : ℕ) :
    (∑ p ∈ cube m, ∑ q ∈ cube m, g (p - q)) ≤
      ((cube m).card : ℝ) * susceptibility g (2*m) := by
  classical
  calc
    _ ≤ ∑ p ∈ cube m, susceptibility g (2*m) := by
      apply Finset.sum_le_sum
      intro p hp
      let f : Site → Site := fun q => p - q
      have hsub : (cube m).image f ⊆ cube (2*m) := by
        rintro z hz
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        exact sub_mem_cube hp hq
      calc
        _ = ∑ z ∈ (cube m).image f, g z := by
          symm
          apply Finset.sum_image
          intro a _ b _ hab
          exact sub_right_injective hab
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hn z)
    _ = _ := by simp

/-- Integer-radius version of (4.2), with a ball containing every allowed
displacement of coordinate size at most k. -/
def LocalOscillation (g : Site → ℝ) (C : ℝ) (D r₀ : ℕ) : Prop :=
  ∀ r, r₀ ≤ r → 0 < r → ∀ x, outside r x → ∀ k, 40*k ≤ r →
    ∀ z ∈ cube k, |g (x+z) - g x| ≤ C * (k:ℝ) / r * tail g (r/D)

private theorem radius_rounding (r M : ℕ) (hM : 0 < M) :
    (r:ℝ) + 1 ≤ (M:ℝ) * ((r/M:ℕ) + 1 : ℝ) := by
  have h : r < (r/M+1)*M :=
    (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  have h' : r+1 ≤ M*(r/M+1) := by simpa [Nat.mul_comm] using h
  exact_mod_cast h'

theorem tail_block_recurrence {g : Site → ℝ} {C : ℝ} {D r₀ : ℕ}
    (hn : ∀ x, 0 ≤ g x) (hb : ∀ x, g x ≤ 1) (hsym : ∀ z, g (-z) = g z)
    (hpos : StationaryPositive g) (hC : 0 ≤ C) (hosc : LocalOscillation g C D r₀)
    {M r : ℕ} (hM : 80 ≤ M) (hr₀ : r₀ ≤ r) (hr : 0 < r) :
    tail g r ≤ susceptibility g r / ((cube (r/M)).card : ℝ) +
      (2*C / M) * tail g (r/D) := by
  classical
  let m := r/M
  let A : ℝ := (cube m).card
  let e : ℝ := (2*C/M) * tail g (r/D)
  have hA : 0 < A := by
    dsimp [A]
    rw [cubeCard]
    positivity
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hM' : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hm : m*M ≤ r := Nat.div_mul_le_self r M
  have hk : 40*(2*m) ≤ r := calc
    _ = m*80 := by ring
    _ ≤ m*M := Nat.mul_le_mul_left m hM
    _ ≤ _ := hm
  have hmn : (m:ℝ)*M ≤ r := by exact_mod_cast hm
  have hfrac : C * ((2*m:ℕ):ℝ) / r ≤ 2*C/M := by
    apply (div_le_div_iff₀ hr' hM').mpr
    push_cast
    linarith [mul_le_mul_of_nonneg_left hmn (mul_nonneg (by norm_num : (0:ℝ)≤2) hC)]
  have he : 0 ≤ e := mul_nonneg (by positivity) (tail_nonneg hb _)
  have hχ : 0 ≤ susceptibility g r := Finset.sum_nonneg (fun z _ => hn z)
  change tail g r ≤ susceptibility g r / A + e
  apply tail_le (add_nonneg (div_nonneg hχ hA.le) he)
  intro x hx
  have hterm (p q : Site) (hp : p ∈ cube m) (hq : q ∈ cube m) :
      g x - e ≤ g (x + (p-q)) := by
    have h := hosc r hr₀ hr x hx (2*m) hk (p-q) (sub_mem_cube hp hq)
    have hv := (abs_le.mp (h.trans (mul_le_mul_of_nonneg_right hfrac
      (tail_nonneg hb (r/D))))).1
    linarith
  have havg : A * (A * (g x - e)) ≤ A * susceptibility g r := calc
    _ = ∑ p ∈ cube m, ∑ q ∈ cube m, (g x - e) := by simp [A, mul_sub]
    _ ≤ ∑ p ∈ cube m, ∑ q ∈ cube m, g (x+(p-q)) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hterm p q hp hq
    _ ≤ ∑ p ∈ cube m, ∑ q ∈ cube m, g (p-q) :=
      translated_block_le_center hsym hpos _ _
    _ ≤ A * susceptibility g (2*m) := center_block_le_susceptibility hn m
    _ ≤ _ := mul_le_mul_of_nonneg_left (cube_mass_mono hn (by omega)) hA.le
  have hrow := (mul_le_mul_iff_right₀ hA).mp havg
  have hpoint : g x - e ≤ susceptibility g r / A :=
    (le_div_iff₀ hA).mpr (by simpa [mul_comm] using hrow)
  linarith

/-- Estimate (4.4) at every integer radius. The implicit constant is uniform
in the radius and the kernel once C, D and the initial threshold are fixed. -/
theorem norm_bound_explicit_of_stationary {g : Site → ℝ} {C : ℝ} {D r₀ M : ℕ}
    (hn : ∀ x, 0 ≤ g x) (hb : ∀ x, g x ≤ 1)
    (hsym : ∀ z, g (-z) = g z) (hpos : StationaryPositive g)
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀)
    (hM : 80 ≤ M) (htune : 4*C*(D:ℝ)^3 ≤ M) (r : ℕ) :
    ((r:ℝ)+1)^3 * tail g r ≤
      (2*(M:ℝ)^3 + ((r₀:ℝ)+1)^3) * susceptibility g r := by
  let B : ℝ := 2*(M:ℝ)^3 + ((r₀:ℝ)+1)^3
  change _ ≤ B * _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmpos : 0 < M := by omega
  have hM' : 0 < (M:ℝ) := by exact_mod_cast hmpos
  have hcoeff : (2*C/M) * (D:ℝ)^3 ≤ 1/2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hM']
    linarith
  have hmul : 0 ≤ 2*C/(M:ℝ) := by positivity
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hχ₀ : g 0 ≤ susceptibility g r := Finset.single_le_sum
      (f:=g) (fun x _ => hn x) (by simp [cube,Fintype.mem_piFinset])
    have hχ : 0 ≤ susceptibility g r := (hn 0).trans hχ₀
    by_cases hr : r₀ ≤ r ∧ 0 < r
    · let s := r/D
      let m := r/M
      let A : ℝ := (cube m).card
      have hA : 0 < A := by
        dsimp [A]
        rw [cubeCard]
        positivity
      have hs : s < r := Nat.div_lt_self hr.2 (by omega)
      have hstep : tail g r ≤ susceptibility g r / A + (2*C/M) * tail g s :=
        tail_block_recurrence hn hb hsym hpos hC hosc hM hr.1 hr.2
      have hscaleM : ((r:ℝ)+1)^3 ≤ (M:ℝ)^3 * A := calc
        _ ≤ ((M:ℝ) * ((m:ℝ)+1))^3 := by
          gcongr
          exact radius_rounding r M hmpos
        _ = (M:ℝ)^3 * ((m:ℝ)+1)^3 := mul_pow _ _ _
        _ ≤ _ := by
          dsimp [A]
          rw [cubeCard]
          push_cast
          gcongr
          linarith [Nat.cast_nonneg (α:=ℝ) m]
      have hscaleD : ((r:ℝ)+1)^3 ≤ (D:ℝ)^3 * ((s:ℝ)+1)^3 := by
        rw [← mul_pow]
        gcongr
        exact radius_rounding r D (by omega)
      have hfirst : ((r:ℝ)+1)^3 * (susceptibility g r / A) ≤
          (M:ℝ)^3 * susceptibility g r := calc
        _ ≤ ((M:ℝ)^3*A) * (susceptibility g r/A) :=
          mul_le_mul_of_nonneg_right hscaleM (div_nonneg hχ hA.le)
        _ = _ := by field_simp
      have hsecond : ((r:ℝ)+1)^3 * ((2*C/M) * tail g s) ≤
          (1/2:ℝ) * (B * susceptibility g r) := calc
        _ ≤ ((D:ℝ)^3*((s:ℝ)+1)^3) * ((2*C/M) * tail g s) :=
          mul_le_mul_of_nonneg_right hscaleD (mul_nonneg hmul (tail_nonneg hb s))
        _ = ((2*C/M)*(D:ℝ)^3)*(((s:ℝ)+1)^3*tail g s) := by ring
        _ ≤ (1/2:ℝ) * (B*susceptibility g s) :=
          mul_le_mul hcoeff (ih s hs)
            (mul_nonneg (by positivity) (tail_nonneg hb s)) (by norm_num)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (cube_mass_mono hn hs.le) hB
      calc
        _ ≤ ((r:ℝ)+1)^3 * (susceptibility g r / A + (2*C/M)*tail g s) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = _ := mul_add _ _ _
        _ ≤ (M:ℝ)^3*susceptibility g r+(1/2:ℝ)*(B*susceptibility g r) :=
          add_le_add hfirst hsecond
        _ ≤ _ := by
          have hMB : (M:ℝ)^3 ≤ B/2 := by
            dsimp [B]
            linarith [show (0:ℝ) ≤ ((r₀:ℝ)+1)^3 by positivity]
          linarith [mul_le_mul_of_nonneg_right hMB hχ]
    · have hrr : r ≤ r₀ := by omega
      have hrpow : ((r:ℝ)+1)^3 ≤ ((r₀:ℝ)+1)^3 := by gcongr
      have htail : tail g r ≤ g 0 := tail_le (hn 0) (fun x _ => le_origin_of_stationary hsym hpos x)
      have hrB : ((r:ℝ)+1)^3 ≤ B := by
        dsimp [B]
        linarith only [hrpow,show 0≤(M:ℝ)^3 by positivity]
      exact mul_le_mul hrB (htail.trans hχ₀) (tail_nonneg hb _) hB

theorem norm_bound_explicit {g : Site → ℝ} {C : ℝ} {D r₀ M : ℕ}
    (hn : ∀ x, 0 ≤ g x) (hb : ∀ x, g x ≤ 1) (h0 : g 0 = 1)
    (hsym : ∀ z, g (-z) = g z) (hpos : StationaryPositive g)
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀)
    (hM : 80 ≤ M) (htune : 4*C*(D:ℝ)^3 ≤ M) (r : ℕ) :
    ((r:ℝ)+1)^3 * tail g r ≤
      (2*(M:ℝ)^3 + ((r₀:ℝ)+1)^3) * susceptibility g r :=
  norm_bound_explicit_of_stationary hn hb hsym hpos hC hD hosc hM htune r

/-- Pointwise real-radius version with the exact original sharp cube mass.
The constant works at the first lattice shell and at every larger radius. -/
theorem pointwise_envelope_of_stationary {g : Site → ℝ} {C : ℝ} {D r₀ : ℕ}
    (hn : ∀ x, 0 ≤ g x) (hb : ∀ x, g x ≤ 1)
    (hsym : ∀ z, g (-z) = g z) (hpos : StationaryPositive g)
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Site,
      (∃ i, r ≤ ((x i).natAbs : ℝ)) → g x ≤ B*susceptibility g ⌊r⌋₊ / r^3 := by
  obtain ⟨M,hM⟩ := exists_nat_ge (max (80:ℝ) (4*C*(D:ℝ)^3))
  have hM1 : 80 ≤ M := by exact_mod_cast (le_max_left _ _).trans hM
  have hM2 := (le_max_right _ _).trans hM
  let B : ℝ := 2*(M:ℝ)^3 + ((r₀:ℝ)+1)^3
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro r hr x hx
  have hr' : 0 < r := zero_lt_one.trans_le hr
  have hx' : outside ⌊r⌋₊ x := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i, by exact_mod_cast (Nat.floor_le hr'.le).trans hi⟩
  apply (le_div_iff₀ (pow_pos hr' 3)).mpr
  have hbound := norm_bound_explicit_of_stationary hn hb hsym hpos hC hD hosc hM1 hM2 ⌊r⌋₊
  calc
    _ = r^3 * g x := mul_comm _ _
    _ ≤ ((⌊r⌋₊:ℝ)+1)^3 * tail g ⌊r⌋₊ := by
      apply mul_le_mul _ (le_tail hb hx') (hn _) (by positivity)
      gcongr
      exact (Nat.lt_floor_add_one r).le
    _ ≤ _ := hbound

theorem pointwise_susceptibility_envelope {g : Site → ℝ} {C : ℝ} {D r₀ : ℕ}
    (hn : ∀ x, 0 ≤ g x) (hb : ∀ x, g x ≤ 1) (h0 : g 0 = 1)
    (hsym : ∀ z, g (-z) = g z) (hpos : StationaryPositive g)
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Site,
      (∃ i, r ≤ ((x i).natAbs : ℝ)) → g x ≤ B*susceptibility g ⌊r⌋₊ / r^3 :=
  pointwise_envelope_of_stationary hn hb hsym hpos hC hD hosc

#print axioms translated_block_le_center
#print axioms norm_bound_explicit
#print axioms pointwise_susceptibility_envelope

end IsingScaling.SpatialEnvelope
