import MathlibProbe.RotorPeriodicSeam
import Mathlib.Data.Int.ModEq
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Filter.Finite

/-! # Local coordinates in the cubic periodic rotor readout

The ordinary torus action records each translated lattice coordinate modulo
the side length. If the period exceeds every coordinate difference in a
patch, the translation is injective on that patch, uniformly in its origin.
The patch may include the interaction collar and additional cylinder sites.
-/

open Filter

namespace IsingScaling.Rotor.PressureSelection.Seam

private theorem coord_eq_of_residue {L : ℕ} [NeZero L] (i : Fin L) {a b : ℤ}
    (hsmall : (b-a).natAbs < L)
    (heq : (((i.val : ℤ)+a) % L).toNat = (((i.val : ℤ)+b) % L).toNat) :
    a = b := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
  have hstep : (i.val : ℤ) + a ≡ (i.val : ℤ) + b [ZMOD (L : ℤ)] := by
    change ((i.val : ℤ)+a) % L = ((i.val : ℤ)+b) % L
    simpa only [Int.toNat_of_nonneg (Int.emod_nonneg _ hL)] using hcast
  have hdvd := (Int.ModEq.add_left_cancel' (i.val : ℤ) hstep).dvd
  have hz : b - a = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hsmall)
  omega

/-- A bound on the coordinate diameters suffices at every origin, including a seam. -/
theorem baseMove_injOn_of_coordinate_span {L : ℕ} [NeZero L] (T : Set IsingScaling.Site)
    (hspan : ∀ x ∈ T, ∀ y ∈ T, ∀ i : Fin 3, (y i-x i).natAbs < L)
    (v : Cell L) : Set.InjOn (fun z => baseMove z v) T := by
  intro x hx y hy heq
  funext i
  fin_cases i
  · exact coord_eq_of_residue v.1 (hspan x hx y hy 0)
      (congrArg (fun c : Cell L => c.1.val) heq)
  · exact coord_eq_of_residue v.2.1 (hspan x hx y hy 1)
      (congrArg (fun c : Cell L => c.2.1.val) heq)
  · exact coord_eq_of_residue v.2.2 (hspan x hx y hy 2)
      (congrArg (fun c : Cell L => c.2.2.val) heq)

/-- A fixed finite lattice patch embeds into every sufficiently large nonzero
period at every origin. The threshold is independent of the chosen origin. -/
theorem eventually_injOn_baseMove {T : Set IsingScaling.Site} (hT : T.Finite) :
    ∀ᶠ L : ℕ in atTop, ∀ [NeZero L], ∀ v : Cell L,
      Set.InjOn (fun z => baseMove z v) T := by
  have hspan : ∀ᶠ L : ℕ in atTop, ∀ x ∈ T, ∀ y ∈ T, ∀ i : Fin 3,
      (y i-x i).natAbs < L := by
    apply hT.eventually_all.mpr
    intro x hx
    apply hT.eventually_all.mpr
    intro y hy
    exact Filter.eventually_all.mpr (fun i => eventually_gt_atTop _)
  filter_upwards [hspan] with L hL
  intro _ v
  exact baseMove_injOn_of_coordinate_span T hL v

/-- Direct version for the positive periods indexed by l+1 in periodic Gibbs limits. -/
theorem eventually_injOn_baseMove_succ (T : Finset IsingScaling.Site) :
    ∀ᶠ l : ℕ in atTop, ∀ v : Cell (l+1),
      Set.InjOn (fun z => baseMove z v) (T : Set IsingScaling.Site) := by
  have h := (tendsto_add_atTop_nat 1).eventually
    (eventually_injOn_baseMove T.finite_toSet)
  filter_upwards [h] with l hl
  exact fun v => hl v

/-- Take the same injection simultaneously on the window and all its prescribed
finite-range neighbours. Extra cylinder sites can be included in the window. -/
theorem eventually_injOn_baseMove_collar (Λ steps : Finset IsingScaling.Site) :
    ∀ᶠ l : ℕ in atTop, ∀ v : Cell (l+1), Set.InjOn (fun z => baseMove z v)
      (((Λ ∪ Λ.biUnion (fun x => steps.image (fun d => x+d))) : Finset IsingScaling.Site) :
        Set IsingScaling.Site) :=
  eventually_injOn_baseMove_succ (Λ ∪ Λ.biUnion (fun x => steps.image (fun d => x+d)))

/-- Reindex the finite coordinates by their actual torus images. -/
noncomputable def baseMoveImageEquiv {L : ℕ} [NeZero L] (v : Cell L)
    (T : Set IsingScaling.Site) (h : Set.InjOn (fun z => baseMove z v) T) :
    T ≃ ((fun z => baseMove z v) '' T) :=
  h.bijOn_image.equiv _

@[simp] theorem baseMoveImageEquiv_apply_val {L : ℕ} [NeZero L] (v : Cell L)
    (T : Set IsingScaling.Site) (h : Set.InjOn (fun z => baseMove z v) T) (x : T) :
    (baseMoveImageEquiv v T h x).val = baseMove x.val v := rfl

end IsingScaling.Rotor.PressureSelection.Seam
