import MathlibProbe.CubicIsingTwoPoint
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! Site reflection of the zero-field Ising spin sum in a symmetric free box. -/
open Finset
open scoped BigOperators
noncomputable section
namespace IsingScaling

abbrev BoxSite (L : ℕ) := ↥(cube L)

/-- Site mirrors separate strict half-boxes: no nearest-neighbour edge
joins their interiors. Fixed wall vertices are retained in both copies. -/
structure BoxSiteMirror (L : ℕ) where
  tip : BoxSite L → ℤ
  refl : Equiv.Perm (BoxSite L)
  invol (x) : refl (refl x) = x
  wall (x) : tip x = 0 → refl x = x
  neg (x) : tip (refl x) = -tip x
  dist (x y) : latticeDistance (refl x) (refl y) = latticeDistance x y
  separated (x y) : tip x < 0 → 0 < tip y → latticeDistance x y ≠ 1

namespace BoxSiteMirror
variable {L : ℕ} (M : BoxSiteMirror L)
abbrev Wall := {x : BoxSite L // M.tip x = 0} → Bool
abbrev Half := {x : BoxSite L // 0 < M.tip x} → Bool

def pack (σ : Spin L) : M.Wall × M.Half × M.Half :=
  (fun x ↦ σ x, fun x ↦ σ x, fun x ↦ σ (M.refl x))

def paste (k : M.Wall × M.Half × M.Half) (x : BoxSite L) : Bool :=
  if h : M.tip x = 0 then k.1 ⟨x,h⟩ else
  if hp : 0 < M.tip x then k.2.1 ⟨x,hp⟩ else
  k.2.2 ⟨M.refl x, by rw [M.neg]; omega⟩

def equiv : Spin L ≃ M.Wall × M.Half × M.Half where
  toFun := M.pack
  invFun := M.paste
  left_inv σ := by
    funext x
    unfold paste pack
    split
    · rfl
    split
    · rfl
    simp [M.invol]
  right_inv k := by
    rcases k with ⟨b,u,v⟩
    apply Prod.ext
    · funext x
      simp [pack, paste, x.property]
    apply Prod.ext
    · funext x
      simp [pack, paste, x.property, x.property.ne']
    · funext x
      have hx := x.property
      simp [pack, paste, M.neg, M.invol, hx.ne', not_lt.mpr hx.le]

private def term (σ : Spin L) (x y : BoxSite L) : ℝ :=
  if latticeDistance x y = 1 then value (σ x) * value (σ y) else 0

private def halfTerm (σ : Spin L) (x y : BoxSite L) : ℝ :=
  if 0 ≤ M.tip x ∧ 0 ≤ M.tip y then
    if M.tip x = 0 ∧ M.tip y = 0 then term σ x y / 2 else term σ x y
  else 0

private lemma term_split (σ : Spin L) (x y : BoxSite L) :
    term σ x y = M.halfTerm σ x y +
        M.halfTerm (σ ∘ M.refl) (M.refl x) (M.refl y) := by
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

def halfEnergy (σ : Spin L) : ℝ := (∑ x, ∑ y, M.halfTerm σ x y) / 2

private theorem energy_split (σ : Spin L) :
    interaction L σ = M.halfEnergy σ + M.halfEnergy (σ ∘ M.refl) := by
  change (∑ x, ∑ y, term σ x y) / 2 = _
  simp_rw [M.term_split σ]
  simp only [sum_add_distrib]
  simp_rw [fun x => Equiv.sum_comp M.refl (M.halfTerm (σ ∘ M.refl) (M.refl x))]
  rw [Equiv.sum_comp M.refl (fun x => ∑ y, M.halfTerm (σ ∘ M.refl) x y), add_div]
  rfl

private theorem halfEnergy_congr {σ τ : Spin L}
    (h : ∀ x, 0 ≤ M.tip x → σ x = τ x) : M.halfEnergy σ = M.halfEnergy τ := by
  unfold halfEnergy
  congr 1
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases he : 0 ≤ M.tip x ∧ 0 ≤ M.tip y
  · simp [halfTerm, term, he, h x he.1, h y he.2]
  · simp [halfTerm, he]

private theorem paste_energy (b : M.Wall) (u v : M.Half) :
    interaction L (M.paste (b,u,v)) =
      M.halfEnergy (M.paste (b,u,u)) + M.halfEnergy (M.paste (b,v,v)) := by
  rw [M.energy_split]
  congr 1
  · apply M.halfEnergy_congr
    intro x hx
    by_cases hz : M.tip x = 0
    · simp [paste, hz]
    · simp [paste, hz, lt_of_le_of_ne hx (Ne.symm hz)]
  · apply M.halfEnergy_congr
    intro x hx
    by_cases hz : M.tip x = 0
    · simp [Function.comp_apply, M.wall x hz, paste, hz]
    · have hp : 0 < M.tip x := by omega
      simp [Function.comp_apply, paste, M.neg, hz, hp, M.invol, not_lt.mpr hx]

/-- The actual Gibbs quadratic form is a sum of squares indexed by
the common spins on the reflection plane. F may depend on all wall spins. -/
theorem reflection_positive (β : ℝ) (F : M.Wall → M.Half → ℝ) :
    0 ≤ ∑ σ : Spin L, gibbsWeight β L σ *
      F (M.pack σ).1 (M.pack σ).2.1 * F (M.pack σ).1 (M.pack σ).2.2 := by
  classical
  let a (b : M.Wall) (u : M.Half) := Real.exp (β * M.halfEnergy (M.paste (b,u,u))) * F b u
  let integrand (σ : Spin L) := gibbsWeight β L σ *
      F (M.pack σ).1 (M.pack σ).2.1 * F (M.pack σ).1 (M.pack σ).2.2
  change 0 ≤ ∑ σ, integrand σ
  rw [← Equiv.sum_comp M.equiv.symm integrand]
  have hex (b : M.Wall) (u v : M.Half) :
      integrand (M.equiv.symm (b,u,v)) = a b u * a b v := by
    have hk : M.pack (M.equiv.symm (b,u,v)) = (b,u,v) := M.equiv.apply_symm_apply _
    unfold integrand
    rw [hk]
    change gibbsWeight β L (M.paste (b,u,v)) * F b u * F b v = _
    simp only [gibbsWeight, M.paste_energy, mul_add, Real.exp_add, a]
    ring
  simp only [Fintype.sum_prod_type, hex]
  apply sum_nonneg
  intro b _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact mul_self_nonneg _

end BoxSiteMirror

/-- Finite free-boundary two-point function with both insertions in the cube. -/
def boxCorrelation (β : ℝ) (L : ℕ) (x y : BoxSite L) : ℝ :=
  (∑ σ : Spin L, gibbsWeight β L σ * value (σ x) * value (σ y)) /
    ∑ σ : Spin L, gibbsWeight β L σ

namespace BoxSiteMirror
variable {L : ℕ} (M : BoxSiteMirror L)

private def readHalf (b : M.Wall) (u : M.Half) (x : BoxSite L)
    (hx : 0 ≤ M.tip x) : ℝ :=
  if h : M.tip x = 0 then value (b ⟨x,h⟩) else value (u ⟨x, by omega⟩)

private lemma readHalf_first (σ : Spin L) (x : BoxSite L) (hx : 0 ≤ M.tip x) :
    M.readHalf (M.pack σ).1 (M.pack σ).2.1 x hx = value (σ x) := by
  unfold readHalf pack
  split <;> rfl

private lemma readHalf_second (σ : Spin L) (x : BoxSite L) (hx : 0 ≤ M.tip x) :
    M.readHalf (M.pack σ).1 (M.pack σ).2.2 x hx = value (σ (M.refl x)) := by
  unfold readHalf pack
  split
  · rename_i h
    rw [M.wall x h]
  · rfl

/-- Positivity of the reflected Gibbs two-point matrix, including tests whose
sites meet the mirror. The coefficients can have either sign. -/
theorem twoPoint_reflection_positive {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → BoxSite L) (hx : ∀ i, 0 ≤ M.tip (x i)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * boxCorrelation β L (x i) (M.refl (x j)) := by
  classical
  let F (b : M.Wall) (u : M.Half) := ∑ i, c i * M.readHalf b u (x i) (hx i)
  have h := M.reflection_positive β F
  dsimp only [F] at h
  simp only [M.readHalf_first, M.readHalf_second] at h
  have hZ : 0 ≤ ∑ σ : Spin L, gibbsWeight β L σ :=
    Finset.sum_nonneg fun σ _ => (Real.exp_pos _).le
  have hswap (a : Spin L → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ σ, a σ i j) = ∑ σ, ∑ i, ∑ j, a σ i j := by
    calc
      _ = ∑ i, ∑ σ, ∑ j, a σ i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold boxCorrelation
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  apply div_nonneg _ hZ
  rw [hswap]
  refine h.trans_eq ?_
  symm
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum _ _ (gibbsWeight β L σ), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end BoxSiteMirror

private def latticeMirror (L : ℕ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Equiv.Perm (BoxSite L) := (signedPerm p s).subtypeEquiv (signedPerm_cube p s L)

/-- Pull the mirror back by a signed permutation of the cube. This also
transports every test on the corresponding closed half-box. -/
def BoxSiteMirror.reindex {L : ℕ} (M : BoxSiteMirror L)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : BoxSiteMirror L := by
  let e := latticeMirror L p s
  have hd (x y : BoxSite L) : latticeDistance (e x) (e y) = latticeDistance x y :=
    signedPerm_distance p s x y
  refine ⟨M.tip ∘ e, e.trans (M.refl.trans e.symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp [M.invol]
  · intro x hx; simpa using congrArg e.symm (M.wall (e x) hx)
  · intro x; simp [M.neg]
  · intro x y
    simp only [Equiv.trans_apply]
    rw [← hd (e.symm (M.refl (e x))) (e.symm (M.refl (e y)))]
    simp [M.dist, hd]
  · intro x y hx hy
    simpa only [hd] using M.separated (e x) (e y) hx hy

def axisSiteMirror (L : ℕ) : BoxSiteMirror L := by
  let r := latticeMirror L (Equiv.refl _) (fun i => decide (i = 0))
  have r0 (x : BoxSite L) : (r x).val 0 = -x.val 0 := rfl
  have r1 (x : BoxSite L) : (r x).val 1 = x.val 1 := rfl
  have r2 (x : BoxSite L) : (r x).val 2 = x.val 2 := rfl
  refine ⟨fun x => x.val 0, r, ?_, ?_, r0, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [r0, r1, r2]
  · intro x hx
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [r0, r1, r2, hx]
  · intro x y
    exact signedPerm_distance _ _ x y
  · intro x y hx hy h
    simp only [latticeDistance, Fin.sum_univ_three] at h
    omega

def diagonalSiteMirror (L : ℕ) : BoxSiteMirror L := by
  let r := latticeMirror L (Equiv.swap 0 1) (fun _ => false)
  have r0 (x : BoxSite L) : (r x).val 0 = x.val 1 := rfl
  have r1 (x : BoxSite L) : (r x).val 1 = x.val 0 := rfl
  have r2 (x : BoxSite L) : (r x).val 2 = x.val 2 := rfl
  refine ⟨fun x => x.val 0 - x.val 1, r, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [r0, r1, r2]
  · intro x hx
    have he : x.val 0 = x.val 1 := by omega
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [r0, r1, r2, he]
  · intro x
    simp only [r0, r1]; omega
  · intro x y
    exact signedPerm_distance _ _ x y
  · intro x y hx hy h
    simp only [latticeDistance, Fin.sum_univ_three] at h
    omega

#print axioms BoxSiteMirror.reflection_positive
#print axioms BoxSiteMirror.twoPoint_reflection_positive
#print axioms diagonalSiteMirror
#print axioms axisSiteMirror

/-- Two insertions in a centered cube, with the same zero extension outside
as the one-insertion displacement function freeTwoPoint. -/
def freePair (β : ℝ) (L : ℕ) (x y : Site) : ℝ :=
  (∑ σ : Spin L, gibbsWeight β L σ * occupation L σ x * occupation L σ y) /
    ∑ σ : Spin L, gibbsWeight β L σ

@[simp] theorem freePair_origin (β L x) : freePair β L 0 x = freeTwoPoint β L x := rfl

theorem boxCorrelation_eq_freePair (β L) (x y : BoxSite L) :
    boxCorrelation β L x y = freePair β L x y := by
  simp only [freePair, boxCorrelation, occupation, x.property, y.property, dite_true]

open Filter
open scoped Topology

def IsFreePairLimit (β : ℝ) (G : Site → Site → ℝ) : Prop :=
  ∀ x y, Tendsto (fun L => freePair β L x y) atTop (𝓝 (G x y))

theorem IsFreePairLimit.origin {β G} (h : IsFreePairLimit β G) :
    IsFreeTwoPoint β (G 0) := fun x => h 0 x

theorem abs_freePair_le_one (β L x y) : |freePair β L x y| ≤ 1 := by
  have hZ : 0 < ∑ σ : Spin L, gibbsWeight β L σ :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hspin (s : Bool) : |value s| = 1 := by cases s <;> norm_num [value]
  rw [freePair, abs_div, abs_of_pos hZ, div_le_one hZ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro σ _
  have hw : 0 < gibbsWeight β L σ := Real.exp_pos _
  by_cases hx : x ∈ cube L <;> by_cases hy : y ∈ cube L <;>
    simp [occupation, hx, hy, abs_mul, abs_of_pos hw, hspin, hw.le]

theorem IsFreePairLimit.abs_le_one {β G} (h : IsFreePairLimit β G) (x y) :
    |G x y| ≤ 1 :=
  le_of_tendsto (h x y).abs (Filter.Eventually.of_forall fun _ => abs_freePair_le_one _ _ _ _)

private theorem eventually_mem_cube (x : Site) : ∀ᶠ L : ℕ in atTop, x ∈ cube L := by
  filter_upwards [eventually_ge_atTop (∑ i, (x i).natAbs)] with L hL
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  omega

/-- Positivity passes to any joint thermodynamic limit of the original two-site
spin sums. The finite mirrors must realize the indicated lattice map on each
centered cube; both the coordinate and the face-diagonal mirrors satisfy this. -/
theorem IsFreePairLimit.reflected_positive {β G} (hG : IsFreePairLimit β G)
    (t : Site → ℤ) (r : Site → Site) (M : ∀ L, BoxSiteMirror L)
    (ht : ∀ L (x : BoxSite L), (M L).tip x = t x)
    (hr : ∀ L (x : BoxSite L), ((M L).refl x).val = r x)
    {ι : Type*} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 ≤ t (x i)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * G (x i) (r (x j)) := by
  classical
  have hlim : Tendsto (fun L : ℕ => ∑ i, ∑ j, c i * c j * freePair β L (x i) (r (x j)))
      atTop (𝓝 (∑ i, ∑ j, c i * c j * G (x i) (r (x j)))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_const_nhds.mul (hG _ _)
  apply ge_of_tendsto hlim
  have hall : ∀ᶠ L : ℕ in atTop, ∀ i, x i ∈ cube L :=
      Filter.eventually_all.mpr fun i => eventually_mem_cube (x i)
  filter_upwards [hall] with L hL
  let y (i : ι) : BoxSite L := ⟨x i, hL i⟩
  have hy (i : ι) : 0 ≤ (M L).tip (y i) := by rw [ht]; exact hx i
  have hpos := (M L).twoPoint_reflection_positive β y hy c
  simpa only [boxCorrelation_eq_freePair, hr, y] using hpos

theorem IsFreePairLimit.axis_reflected_positive {β G} (hG : IsFreePairLimit β G)
    {ι : Type*} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 ≤ x i 0) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      G (x i) (signedPerm (Equiv.refl _) (fun k => decide (k = 0)) (x j)) :=
  hG.reflected_positive (fun v => v 0) _ axisSiteMirror (fun _ _ => rfl) (fun _ _ => rfl) x hx c

theorem IsFreePairLimit.diagonal_reflected_positive {β G} (hG : IsFreePairLimit β G)
    {ι : Type*} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 ≤ x i 0 - x i 1) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      G (x i) (signedPerm (Equiv.swap 0 1) (fun _ => false) (x j)) :=
  hG.reflected_positive (fun v => v 0 - v 1) _ diagonalSiteMirror
    (fun _ _ => rfl) (fun _ _ => rfl) x hx c

#print axioms IsFreePairLimit.diagonal_reflected_positive

namespace Packet

/-- Positivity of every shifted Hankel matrix of a scalar packet. -/
def HankelPositive (a : ℕ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (c : ι → ℝ) (n : ℕ),
    0 ≤ ∑ i, ∑ j, c i * c j * a (n + d i + d j)

def diff (a : ℕ → ℝ) (n : ℕ) : ℝ := a n - a (n+1)

theorem HankelPositive.diff_twice {a : ℕ → ℝ} (h : HankelPositive a) :
    HankelPositive (diff (diff a)) := by
  intro ι _ d c n
  let d' : ι ⊕ ι → ℕ := Sum.elim d (fun i => d i + 1)
  let c' : ι ⊕ ι → ℝ := Sum.elim c (fun i => -c i)
  have hh := h _ d' c' n
  simp only [Fintype.sum_sum_type, d', c', Sum.elim_inl, Sum.elim_inr] at hh
  refine hh.trans_eq ?_
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [diff]
  rw [show n+d i+(d j+1) = n+d i+d j+1 by omega,
      show n+(d i+1)+d j = n+d i+d j+1 by omega,
      show n+(d i+1)+(d j+1) = n+d i+d j+1+1 by omega]
  ring

theorem HankelPositive.nonneg {a : ℕ → ℝ} (h : HankelPositive a) (n : ℕ) :
    0 ≤ a n := by simpa using h Unit (fun _ => 0) (fun _ => 1) n

/-- A bounded discretely convex sequence is decreasing. -/
private theorem diff_nonneg_of_convex {a : ℕ → ℝ} (h : ∀ n, 0 ≤ diff (diff a) n)
    {C : ℝ} (hb : ∀ n, a n ≤ C) (n : ℕ) : 0 ≤ diff a n := by
  by_contra! hn
  have hs (k : ℕ) : diff a (n+k) ≤ diff a n := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := h (n+k)
      change 0 ≤ diff a (n+k) - diff a (n+k+1) at hk
      exact (sub_nonneg.mp hk).trans ih
  have hg (k : ℕ) : a n + (k:ℝ) * (-diff a n) ≤ a (n+k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := hs k
      change a (n+k) - a (n+k+1) ≤ diff a n at hk
      push_cast
      rw [← Nat.add_assoc]
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((C - a n) / (-diff a n))
  have hlt := (div_lt_iff₀ (neg_pos.mpr hn)).mp hk
  linarith [hg k, hb (n+k)]

private theorem diff_bounded {a : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |a n| ≤ C) :
    ∀ n, |diff a n| ≤ 2*C := fun n => by
  calc |diff a n| ≤ |a n| + |a (n+1)| := abs_sub _ _
    _ ≤ _ := by linarith [hb n, hb (n+1)]

/-- Complete monotonicity on the even lattice mesh follows from bounded
shifted reflection forms; this gives every order, including odd differences. -/
theorem completeMonotone_of_hankel (k : ℕ) {a : ℕ → ℝ}
    (ha : HankelPositive a) (hb : ∃ C : ℝ, ∀ n, |a n| ≤ C) (n : ℕ) :
    0 ≤ (diff^[k]) a n := by
  induction k using Nat.strong_induction_on generalizing a with
  | h k ih =>
    rcases hb with ⟨C,hC⟩
    cases k with
    | zero => exact ha.nonneg n
    | succ k =>
      cases k with
      | zero =>
        exact diff_nonneg_of_convex ha.diff_twice.nonneg
          (fun i => (le_abs_self _).trans (hC i)) n
      | succ k =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        exact ih k (by omega) ha.diff_twice ⟨_, diff_bounded (diff_bounded hC)⟩

end Packet

/-- Evaluate a finite transverse test on two mirrored parallel layers. -/
def evenPacket {ι : Type} [Fintype ι] (c : ι → ℝ) (K : ℕ → ι → ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, ∑ j, c i * c j * K (2*n) i j

/-- Real reflected packets sampled on even layers. The hypothesis on K
identifies both insertions with their actual two-site limits and gives the
normal-translation identity. Positivity or a spectral measure for K is
never assumed. -/
theorem IsFreePairLimit.completeMonotone_evenPacket {β G} (hG : IsFreePairLimit β G)
    (t : Site → ℤ) (r : Site → Site) (M : ∀ L, BoxSiteMirror L)
    (ht : ∀ L (x : BoxSite L), (M L).tip x = t x)
    (hr : ∀ L (x : BoxSite L), ((M L).refl x).val = r x)
    {ι : Type} [Fintype ι] (X : ℕ → ι → Site) (hX : ∀ p i, 0 ≤ t (X p i))
    (K : ℕ → ι → ι → ℝ) (hK : ∀ p q i j, G (X p i) (r (X q j)) = K (p+q) i j)
    (c : ι → ℝ) (k n : ℕ) : 0 ≤ (Packet.diff^[k]) (evenPacket c K) n := by
  classical
  apply Packet.completeMonotone_of_hankel
  · intro J _ d γ s
    let T (j : J × ι) := X (s + 2*d j.1) j.2
    let b (j : J × ι) := γ j.1 * c j.2
    have hp := hG.reflected_positive t r M ht hr T (fun _ => hX _ _) b
    simp only [Fintype.sum_prod_type, T, b, hK] at hp
    refine hp.trans_eq ?_
    simp only [evenPacket, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [show s+2*d i+(s+2*d j) = 2*(s+d i+d j) by omega]
    ring
  · refine ⟨∑ i, ∑ j, |c i| * |c j|, ?_⟩
    intro s
    unfold evenPacket
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    have hB := hG.abs_le_one (X (2*s) i) (r (X 0 j))
    rw [hK, add_zero] at hB
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_right (by positivity) hB

#print axioms IsFreePairLimit.completeMonotone_evenPacket

/-- A packet at normal distance 2n along a coordinate line, in a
translation-invariant thermodynamic limit of the two-insertion law. -/
theorem axis_evenPacket_completeMonotone {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x - y)))
    {ι : Type} [Fintype ι] (c : ι → ℝ)
    (x y : ι → ℤ) (k n : ℕ) :
    0 ≤ (Packet.diff^[k]) (evenPacket c (fun m i j =>
      g ![(m : ℤ), x i - x j, y i - y j])) n := by
  let X (p : ℕ) (i : ι) : Site := ![(p:ℤ), x i, y i]
  apply hg.completeMonotone_evenPacket (fun w => w 0)
    (signedPerm (Equiv.refl _) (fun l => decide (l = 0))) axisSiteMirror
    (fun _ _ => rfl) (fun _ _ => rfl) X
  · intro p i
    change 0 ≤ (p:ℤ)
    omega
  · intro p q i j
    apply congrArg g
    funext l
    fin_cases l
    · change (p:ℤ) - -(q:ℤ) = ((p+q:ℕ):ℤ)
      omega
    · rfl
    · rfl

/-- The face-diagonal packet lies on the integer layers obtained by
translating the wall along (1,-1,0), so no transverse coset approximation
is needed at the even sampled times in this statement. -/
theorem diagonal_evenPacket_completeMonotone {β : ℝ} {g : Site → ℝ}
    (hg : IsFreePairLimit β (fun x y => g (x - y)))
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) (k n : ℕ) :
    0 ≤ (Packet.diff^[k]) (evenPacket c (fun m i j =>
      g ![x i - x j + (m:ℤ), x i - x j - (m:ℤ), y i - y j])) n := by
  let X (p : ℕ) (i : ι) : Site := ![x i + (p:ℤ), x i - (p:ℤ), y i]
  apply hg.completeMonotone_evenPacket (fun w => w 0 - w 1)
    (signedPerm (Equiv.swap 0 1) (fun _ => false)) diagonalSiteMirror
    (fun _ _ => rfl) (fun _ _ => rfl) X
  · intro p i
    change 0 ≤ (x i + (p:ℤ)) - (x i - (p:ℤ))
    omega
  · intro p q i j
    apply congrArg g
    funext l
    fin_cases l
    · change (x i + (p:ℤ)) - (x j - (q:ℤ)) = x i - x j + ((p+q:ℕ):ℤ)
      omega
    · change (x i - (p:ℤ)) - (x j + (q:ℤ)) = x i - x j - ((p+q:ℕ):ℤ)
      omega
    · rfl

#print axioms diagonal_evenPacket_completeMonotone

end IsingScaling
