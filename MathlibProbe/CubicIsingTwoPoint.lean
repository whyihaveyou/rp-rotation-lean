import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Finite free-boundary, zero-field nearest-neighbour Ising correlations and
their signed-permutation symmetry. The thermodynamic-limit theorem quantifies
over limits of these actual finite spin sums. -/

noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace IsingScaling
abbrev Site := Fin 3 → ℤ

def cube (L : ℕ) : Finset Site :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(L : ℤ)) (L : ℤ))

def latticeDistance (x y : Site) : ℕ := ∑ i, (x i - y i).natAbs

private def signCoord (s : Bool) (a : ℤ) : ℤ := if s then -a else a

private theorem sign_twice (s : Bool) (a : ℤ) : signCoord s (signCoord s a) = a := by
  cases s <;> simp [signCoord]

def signedPerm (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : Equiv.Perm Site where
  toFun x i := signCoord (s i) (x (p i))
  invFun y j := signCoord (s (p.symm j)) (y (p.symm j))
  left_inv x := by funext j; simp [sign_twice]
  right_inv y := by funext i; simp [sign_twice]

@[simp] theorem signedPerm_zero (p : Equiv.Perm (Fin 3)) (s) :
    signedPerm p s 0 = 0 := by
  funext i
  change signCoord (s i) 0 = 0
  cases s i <;> simp [signCoord]

theorem signedPerm_distance (p : Equiv.Perm (Fin 3)) (s) (x y : Site) :
    latticeDistance (signedPerm p s x) (signedPerm p s y) = latticeDistance x y := by
  unfold latticeDistance
  calc
    _ = ∑ i, (x (p i) - y (p i)).natAbs := by
      apply Finset.sum_congr rfl
      intro i _
      change (signCoord (s i) _ - signCoord (s i) _).natAbs = _
      cases s i
      · rfl
      · change (-x (p i) - -y (p i)).natAbs = _
        rw [show -x (p i) - -y (p i) = -(x (p i) - y (p i)) by omega, Int.natAbs_neg]
    _ = _ := Equiv.sum_comp p (fun i => (x i - y i).natAbs)

theorem signedPerm_cube (p : Equiv.Perm (Fin 3)) (s) (L) (x : Site) :
    x ∈ cube L ↔ signedPerm p s x ∈ cube L := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h i
    change _ ≤ signCoord (s i) (x (p i)) ∧ signCoord (s i) (x (p i)) ≤ _
    have hi := h (p i)
    cases s i <;> simp [signCoord] <;> omega
  · intro h i
    have hi := h (p.symm i)
    change _ ≤ signCoord _ (x (p (p.symm i))) ∧ signCoord _ (x (p (p.symm i))) ≤ _ at hi
    simp only [Equiv.apply_symm_apply] at hi
    cases hs : s (p.symm i) <;> simp [hs, signCoord] at hi <;> omega

abbrev Spin (L : ℕ) := ↥(cube L) → Bool

def value (b : Bool) : ℝ := if b then 1 else -1

def occupation (L : ℕ) (σ : Spin L) (x : Site) : ℝ :=
  if h : x ∈ cube L then value (σ ⟨x, h⟩) else 0

/-- The factor one half counts each undirected nearest-neighbour bond once. -/
def interaction (L : ℕ) (σ : Spin L) : ℝ :=
  (∑ x : ↥(cube L), ∑ y : ↥(cube L),
    if latticeDistance x y = 1 then value (σ x) * value (σ y) else 0) / 2

def gibbsWeight (β : ℝ) (L : ℕ) (σ : Spin L) : ℝ :=
  Real.exp (β * interaction L σ)

def freeTwoPoint (β : ℝ) (L : ℕ) (x : Site) : ℝ :=
  (∑ σ : Spin L, gibbsWeight β L σ * occupation L σ 0 * occupation L σ x) /
  (∑ σ : Spin L, gibbsWeight β L σ)

def IsFreeTwoPoint (β : ℝ) (g : Site → ℝ) : Prop :=
  ∀ x, Tendsto (fun L => freeTwoPoint β L x) atTop (𝓝 (g x))

private def boxPerm (L) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : Equiv.Perm ↥(cube L) :=
  (signedPerm p s).subtypeEquiv (signedPerm_cube p s L)

private theorem weight_reindex (β L) (p : Equiv.Perm (Fin 3)) (s) (σ : Spin L) :
    gibbsWeight β L (σ ∘ boxPerm L p s) = gibbsWeight β L σ := by
  let e := boxPerm L p s
  have hd (x y : ↥(cube L)) : latticeDistance (e x) (e y) = latticeDistance x y :=
    signedPerm_distance p s x y
  let term (x y : ↥(cube L)) : ℝ :=
    if latticeDistance x y = 1 then value (σ x) * value (σ y) else 0
  apply congrArg (fun t : ℝ => Real.exp (β * (t / 2)))
  calc
    _ = ∑ x, ∑ y, term (e x) (e y) := by simp only [term, hd, Function.comp_apply]; rfl
    _ = ∑ x, ∑ y, term x y := by
      simp_rw [fun x => Equiv.sum_comp e (term (e x))]
      exact Equiv.sum_comp e (fun x => ∑ y, term x y)

private theorem occupation_reindex (L) (p : Equiv.Perm (Fin 3)) (s) (σ : Spin L) (x) :
    occupation L (σ ∘ boxPerm L p s) x = occupation L σ (signedPerm p s x) := by
  unfold occupation
  by_cases hx : x ∈ cube L
  · simp [hx, (signedPerm_cube p s L x).mp hx, boxPerm]
  · have hx' := mt (signedPerm_cube p s L x).mpr hx
    simp only [hx, hx', dite_false]

theorem freeTwoPoint_signedPerm (β L) (p : Equiv.Perm (Fin 3)) (s) (x) :
    freeTwoPoint β L (signedPerm p s x) = freeTwoPoint β L x := by
  classical
  let e : Equiv.Perm (Spin L) := (boxPerm L p s).symm.arrowCongr (Equiv.refl Bool)
  let f (σ : Spin L) := gibbsWeight β L σ * occupation L σ 0 * occupation L σ x
  have hσ (σ : Spin L) : f (e σ) =
      gibbsWeight β L σ * occupation L σ 0 * occupation L σ (signedPerm p s x) := by
    change gibbsWeight β L (σ ∘ boxPerm L p s) * occupation L (σ ∘ boxPerm L p s) 0 *
      occupation L (σ ∘ boxPerm L p s) x = _
    rw [weight_reindex, occupation_reindex, occupation_reindex, signedPerm_zero]
  unfold freeTwoPoint
  congr 1
  exact (Finset.sum_congr rfl (fun σ _ => (hσ σ).symm)).trans (Equiv.sum_comp e f)

theorem freeLimit_signedPerm {β g} (h : IsFreeTwoPoint β g)
    (p : Equiv.Perm (Fin 3)) (s) (x) : g (signedPerm p s x) = g x := by
  apply tendsto_nhds_unique (h (signedPerm p s x))
  simpa only [freeTwoPoint_signedPerm] using h x

end IsingScaling
