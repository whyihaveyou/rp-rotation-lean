import MathlibProbe.RotorPeriodicPressureTransfer
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The two seams of the diagonal rotor torus

For period basis (2L,0,0),(L,L,0),(0,0,L) use the unique residues
x,y,w in [0,L), together with the bit specifying the L-block of the
first coordinate. Reducing a step changes the bit by its first-coordinate
wrap count minus its second-coordinate wrap count, modulo two. The two
independent cubic tori leave that bit alone at every step.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace IsingScaling.Rotor.PressureSelection.Seam

abbrev Cell (L : ℕ) := Fin L × Fin L × Fin L
abbrev Site (L : ℕ) := Cell L ⊕ Cell L

def badResidues (L : ℕ) (d : ℤ) : Finset (Fin L) :=
  univ.filter (fun i => ¬(0 ≤ (i.val : ℤ) + d ∧ (i.val : ℤ) + d < (L : ℤ)))

theorem badResidues_card (L : ℕ) (d : ℤ) :
    (badResidues L d).card ≤ min L d.natAbs := by
  apply le_min
  · unfold badResidues
    exact (Finset.card_filter_le _ _).trans (by simp)
  by_cases hd : 0 ≤ d
  · have habs := Int.natAbs_of_nonneg hd
    calc
      _ ≤ (range d.natAbs).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin L => L - 1 - i.val)
        · intro i hi
          change i ∈ badResidues L d at hi
          simp only [badResidues, mem_filter, mem_univ, true_and] at hi
          change L - 1 - i.val ∈ range d.natAbs
          apply mem_range.mpr
          omega
        · intro i _ j _ hij
          apply Fin.ext
          change L - 1 - i.val = L - 1 - j.val at hij
          omega
      _ = _ := card_range _
  · have habs := Int.natAbs_of_nonneg (show 0 ≤ -d by omega)
    rw [Int.natAbs_neg] at habs
    calc
      _ ≤ (range d.natAbs).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin L => i.val)
        · intro i hi
          change i ∈ badResidues L d at hi
          simp only [badResidues, mem_filter, mem_univ, true_and] at hi
          change i.val ∈ range d.natAbs
          exact mem_range.mpr (by omega)
        · intro _ _ _ _ h
          exact Fin.ext h
      _ = _ := card_range _

private def residue {L : ℕ} [NeZero L] (i : Fin L) (d : ℤ) : Fin L :=
  ⟨(((i.val : ℤ) + d) % L).toNat, by
    have hL : 0 < (L : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h := Int.emod_lt_of_pos ((i.val : ℤ)+d) hL
    omega⟩

/-- Translation by the lattice step on the ordinary L-periodic cube. -/
def baseMove {L : ℕ} [NeZero L] (z : IsingScaling.Site) (x : Cell L) : Cell L :=
  (residue x.1 (z 0), residue x.2.1 (z 1), residue x.2.2 (z 2))

private def wrap {L : ℕ} (i : Fin L) (d : ℤ) : ℤ := ((i.val : ℤ) + d) / L

/-- The zero-twist comparison retains the component index. -/
def cubicDestination {L : ℕ} [NeZero L] (z : IsingScaling.Site) : Site L → Site L :=
  Sum.map (baseMove z) (baseMove z)

/-- The quotient by the diagonal-adapted periods in block-bit coordinates. -/
def adaptedDestination {L : ℕ} [NeZero L] (z : IsingScaling.Site) (a : Site L) : Site L :=
  let x := Sum.elim id id a
  if (wrap x.1 (z 0) - wrap x.2.1 (z 1)) % 2 = 0 then cubicDestination z a
  else (cubicDestination z a).swap

private def cellOf {L : ℕ} : Site L → Cell L := Sum.elim id id
private def blockBit {L : ℕ} : Site L → ℤ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- Representatives in [0,2L) × [0,L) × [0,L). -/
def representative {L : ℕ} (a : Site L) : IsingScaling.Site :=
  ![((cellOf a).1.val : ℤ) + (L : ℤ) * blockBit a, ((cellOf a).2.1.val : ℤ),
    ((cellOf a).2.2.val : ℤ)]

/-- Difference by integer multiples of (2L,0,0), (L,L,0), (0,0,L). -/
def SamePeriodClass (L : ℕ) (p q : IsingScaling.Site) : Prop :=
  ∃ i j k : ℤ, p 0 - q 0 = 2 * (L : ℤ) * i + (L : ℤ) * j ∧
    p 1 - q 1 = (L : ℤ) * j ∧ p 2 - q 2 = (L : ℤ) * k

private lemma residue_step {L : ℕ} [NeZero L] (x : Fin L) (d : ℤ) :
    (x.val : ℤ) + d - ((residue x d).val : ℤ) = (L : ℤ) * wrap x d := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [residue, wrap, Int.toNat_of_nonneg (Int.emod_nonneg _ hL)]
  have h := Int.emod_add_mul_ediv ((x.val : ℤ) + d) (L : ℤ)
  omega

private lemma cell_after_step {L : ℕ} [NeZero L] (z : IsingScaling.Site) (a : Site L) :
    cellOf (adaptedDestination z a) = baseMove z (cellOf a) := by
  cases a with
  | inl x =>
    by_cases h : (wrap x.1 (z 0) - wrap x.2.1 (z 1)) % 2 = 0 <;>
      simp [cellOf, adaptedDestination, h, cubicDestination]
  | inr x =>
    by_cases h : (wrap x.1 (z 0) - wrap x.2.1 (z 1)) % 2 = 0 <;>
      simp [cellOf, adaptedDestination, h, cubicDestination]

private lemma bit_after_step {L : ℕ} [NeZero L] (z : IsingScaling.Site) (a : Site L) :
    (blockBit a + wrap (cellOf a).1 (z 0) - wrap (cellOf a).2.1 (z 1)
        - blockBit (adaptedDestination z a)) % 2 = 0 := by
  cases a with
  | inl x =>
    by_cases h : (wrap x.1 (z 0) - wrap x.2.1 (z 1)) % 2 = 0 <;>
      simp [blockBit, cellOf, adaptedDestination, h, cubicDestination] <;> omega
  | inr x =>
    by_cases h : (wrap x.1 (z 0) - wrap x.2.1 (z 1)) % 2 = 0 <;>
      simp [blockBit, cellOf, adaptedDestination, h, cubicDestination] <;> omega

/-- The destination used in the pressure matrices really is the lattice
translate modulo the three specified periods, for arbitrarily long steps. -/
theorem adapted_step_same_period (L : ℕ) [NeZero L] (z : IsingScaling.Site) (a : Site L) :
    SamePeriodClass L (representative a + z) (representative (adaptedDestination z a)) := by
  let x := cellOf a
  let b := blockBit (adaptedDestination z a)
  let u := blockBit a + wrap x.1 (z 0) - wrap x.2.1 (z 1) - b
  have hp : u % 2 = 0 := bit_after_step z a
  have hu : u = 2 * (u / 2) := by omega
  have hK : blockBit a + wrap x.1 (z 0) - b = 2 * (u / 2) + wrap x.2.1 (z 1) := by
    linear_combination hu
  refine ⟨u / 2, wrap x.2.1 (z 1), wrap x.2.2 (z 2), ?_, ?_, ?_⟩
  · change (x.1.val : ℤ) + (L : ℤ) * blockBit a + z 0 -
        (((cellOf (adaptedDestination z a)).1.val : ℤ) + (L : ℤ) * b) = _
    rw [cell_after_step]
    calc
      _ = (L : ℤ) * (blockBit a + wrap x.1 (z 0) - b) := by
        change (x.1.val : ℤ) + (L : ℤ) * blockBit a + z 0 -
          (((residue x.1 (z 0)).val : ℤ) + (L : ℤ) * b) = _
        linear_combination residue_step x.1 (z 0)
      _ = _ := by rw [hK]; ring
  · change (x.2.1.val : ℤ) + z 1 - ((cellOf (adaptedDestination z a)).2.1.val : ℤ) = _
    rw [cell_after_step]
    exact residue_step x.2.1 (z 1)
  · change (x.2.2.val : ℤ) + z 2 - ((cellOf (adaptedDestination z a)).2.2.val : ℤ) = _
    rw [cell_after_step]
    exact residue_step x.2.2 (z 2)

private lemma equals_in_residue_range {m a b k : ℤ} (hm : 0 < m)
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m) (he : a - b = m * k) :
    a = b ∧ k = 0 := by
  have hk : k = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg | hpos
    · have hh := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) hm.le
      simp only [mul_neg_one] at hh
      omega
    · have hh := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) hm.le
      simp only [mul_one] at hh
      omega
  rw [hk, mul_zero] at he
  exact ⟨by omega, hk⟩

private lemma representative_bounds {L : ℕ} (a : Site L) :
    (0 ≤ representative a 0 ∧ representative a 0 < 2 * (L : ℤ)) ∧
    (0 ≤ representative a 1 ∧ representative a 1 < (L : ℤ)) ∧
    (0 ≤ representative a 2 ∧ representative a 2 < (L : ℤ)) := by
  cases a with
  | inl x =>
    have h1 := x.1.isLt
    have h2 := x.2.1.isLt
    have h3 := x.2.2.isLt
    simp [representative, cellOf, blockBit] <;> omega
  | inr x =>
    have h1 := x.1.isLt
    have h2 := x.2.1.isLt
    have h3 := x.2.2.isLt
    simp [representative, cellOf, blockBit] <;> omega

/-- The rectangle representatives of a geometric period class agree in
all three coordinates. -/
theorem representative_eq_of_same_period {L : ℕ} [NeZero L] (a b : Site L)
    (h : SamePeriodClass L (representative a) (representative b)) :
    representative a = representative b := by
  obtain ⟨i,j,k,hx,hy,hz⟩ := h
  have hL : 0 < (L : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨xa,ya,za⟩ := representative_bounds a
  obtain ⟨xb,yb,zb⟩ := representative_bounds b
  obtain ⟨ey, rfl⟩ := equals_in_residue_range hL ya yb hy
  obtain ⟨ez, _⟩ := equals_in_residue_range hL za zb hz
  have ex := (equals_in_residue_range (show 0 < 2 * (L : ℤ) by omega) xa xb
    (by simpa using hx)).1
  funext n
  fin_cases n <;> assumption

private lemma cell_eq {L : ℕ} {x y : Cell L}
    (h0 : (x.1.val : ℤ) = y.1.val) (h1 : (x.2.1.val : ℤ) = y.2.1.val)
    (h2 : (x.2.2.val : ℤ) = y.2.2.val) : x = y :=
  Prod.ext (Fin.ext (by exact_mod_cast h0))
    (Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2)))

theorem representative_injective (L : ℕ) : Function.Injective (@representative L) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      apply congrArg Sum.inl
      apply cell_eq
      · simpa [representative, cellOf, blockBit] using h0
      · exact h1
      · exact h2
    | inr y =>
      have hx := x.1.isLt
      simp [representative, cellOf, blockBit] at h0
      omega
  | inr x =>
    cases b with
    | inl y =>
      have hy := y.1.isLt
      simp [representative, cellOf, blockBit] at h0
      omega
    | inr y =>
      apply congrArg Sum.inr
      apply cell_eq
      · simpa [representative, cellOf, blockBit] using h0
      · exact h1
      · exact h2

/-- A step in the original integer lattice has exactly one target label on
the adapted torus, and this label is the one used in the physical energy. -/
theorem adapted_step_unique (L : ℕ) [NeZero L] (z : IsingScaling.Site) (a b : Site L) :
    SamePeriodClass L (representative a + z) (representative b) ↔
      adaptedDestination z a = b := by
  constructor
  · intro hb
    obtain ⟨i,j,k,hx,hy,hz⟩ := adapted_step_same_period L z a
    obtain ⟨i',j',k',hx',hy',hz'⟩ := hb
    apply representative_injective L
    apply representative_eq_of_same_period
    refine ⟨i'-i,j'-j,k'-k, ?_, ?_, ?_⟩
    · linear_combination hx' - hx
    · linear_combination hy' - hy
    · linear_combination hz' - hz
  · rintro rfl
    exact adapted_step_same_period L z a

private def seams (L : ℕ) (z : IsingScaling.Site) : Finset (Cell L) :=
  (badResidues L (z 0) ×ˢ (univ ×ˢ univ)) ∪ (univ ×ˢ (badResidues L (z 1) ×ˢ univ))

private lemma seam_contains {L : ℕ} [NeZero L] (z : IsingScaling.Site) (a : Site L)
    (h : adaptedDestination z a ≠ cubicDestination z a) :
    Sum.elim id id a ∈ seams L z := by
  classical
  let x : Cell L := Sum.elim id id a
  by_contra hno
  change x ∉ seams L z at hno
  simp [seams, badResidues] at hno
  obtain ⟨h1,h2⟩ := hno
  have hzero :
      (wrap x.1 (z 0) - wrap x.2.1 (z 1)) % 2 = 0 := by
    simp only [wrap, Int.ediv_eq_zero_of_lt h1.1 h1.2, Int.ediv_eq_zero_of_lt h2.1 h2.2,
      sub_self, Int.zero_emod]
  exact h (ite_eq_left hzero)

private lemma seams_card (L : ℕ) (z : IsingScaling.Site) :
    (seams L z).card ≤ L ^ 2 * ((z 0).natAbs + (z 1).natAbs) := by
  refine (Finset.card_union_le _ _).trans ?_
  simp only [card_product, card_univ, Fintype.card_fin]
  have h1 := (badResidues_card L (z 0)).trans (min_le_right _ _)
  have h2 := (badResidues_card L (z 1)).trans (min_le_right _ _)
  calc
    _ ≤ (z 0).natAbs * (L * L) + L * ((z 1).natAbs * L) := by gcongr
    _ = _ := by ring

/-- Number of starting vertices whose translated destination differs in the
two finite geometries. The third component of the step is unrestricted. -/
theorem changed_destination_card (L : ℕ) [NeZero L] (z : IsingScaling.Site) :
    (univ.filter (fun v : Site L => adaptedDestination z v ≠ cubicDestination z v)).card
      ≤ 2 * L ^ 2 * ((z 0).natAbs + (z 1).natAbs) := by
  classical
  have hsub : (univ.filter (fun v : Site L => adaptedDestination z v ≠ cubicDestination z v)) ⊆
      (seams L z).disjSum (seams L z) := by
    intro v hv
    have hc := seam_contains z v (mem_filter.mp hv).2
    cases v <;> simpa using hc
  apply (Finset.card_le_card hsub).trans
  rw [card_disjSum]
  have hs := seams_card L z
  nlinarith

/-- Periodize a finite list of lattice displacements. If several translations
land at the same vertex, all of their coupling strengths are added. -/
def periodize {V : Type*} [DecidableEq V] (D : IsingScaling.Site → V → V)
    (steps : Finset IsingScaling.Site) (J : IsingScaling.Site → ℝ) (v w : V) : ℝ :=
  ∑ z ∈ steps, if D z v = w then J z else 0

private theorem row_change {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (j : ℝ) :
    (∑ w : V, |(if a = w then j else 0) - (if b = w then j else 0)|) =
      if a = b then 0 else 2 * |j| := by
  by_cases hab : a = b
  · simp [hab]
  have he (w : V) :
      |(if a = w then j else 0) - (if b = w then j else 0)| =
        (if a = w then |j| else 0) + (if b = w then |j| else 0) := by
    by_cases ha : a = w <;> by_cases hb : b = w <;> simp_all
  simp_rw [he]
  simp [Finset.sum_add_distrib, hab, two_mul]

private theorem sum_steps_first {V : Type*} [Fintype V] (T : Finset IsingScaling.Site)
    (f : V → V → IsingScaling.Site → ℝ) :
    (∑ v : V, ∑ w : V, ∑ z ∈ T, f v w z) = ∑ z ∈ T, ∑ v : V, ∑ w : V, f v w z := by
  calc
    _ = ∑ v : V, ∑ z ∈ T, ∑ w : V, f v w z :=
      Finset.sum_congr rfl fun v _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem periodize_change {V : Type*} [Fintype V] [DecidableEq V]
    (D E : IsingScaling.Site → V → V) (T : Finset IsingScaling.Site)
    (J : IsingScaling.Site → ℝ) :
    (∑ v : V, ∑ w : V, |periodize D T J v w - periodize E T J v w|) ≤
      ∑ z ∈ T, (univ.filter (fun v : V => D z v ≠ E z v)).card * (2 * |J z|) := by
  classical
  calc
    _ ≤ ∑ v : V, ∑ w : V, ∑ z ∈ T,
        |(if D z v = w then J z else 0) - (if E z v = w then J z else 0)| := by
          refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => ?_
          unfold periodize
          rw [← Finset.sum_sub_distrib]
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z ∈ T, ∑ v : V, ∑ w : V,
        |(if D z v = w then J z else 0) - (if E z v = w then J z else 0)| :=
          sum_steps_first _ _
    _ = _ := by
      refine Finset.sum_congr rfl fun z _ => ?_
      simp_rw [row_change]
      classical
      rw [← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
      simp

/-- The ordinary cubic torus has L cubed sites; the adapted quotient has
twice that cardinality. Both coupling matrices use the same original steps. -/
def ordinaryCoupling (L : ℕ) [NeZero L] (T : Finset IsingScaling.Site)
    (J : IsingScaling.Site → ℝ) : Cell L → Cell L → ℝ := periodize baseMove T J

def adaptedCoupling (L : ℕ) [NeZero L] (T : Finset IsingScaling.Site)
    (J : IsingScaling.Site → ℝ) : Site L → Site L → ℝ := periodize adaptedDestination T J

theorem periodize_cubic (L : ℕ) [NeZero L] (T : Finset IsingScaling.Site)
    (J : IsingScaling.Site → ℝ) :
    periodize (cubicDestination (L := L)) T J = twoCopies (ordinaryCoupling L T J) := by
  funext v w
  cases v <;> cases w <;> simp [periodize, ordinaryCoupling, cubicDestination, twoCopies]

/-- Finite-size comparison for the actual Gibbs pressures at every positive
integer spin dimension. All displacement signs and collisions are allowed. -/
theorem finite_range_pressure_error (N L : ℕ) [NeZero N] [NeZero L]
    (T : Finset IsingScaling.Site) (J : IsingScaling.Site → ℝ) :
    |pressure N (adaptedCoupling L T J) - pressure N (ordinaryCoupling L T J)| ≤
      (∑ z ∈ T, |J z| * (((z 0).natAbs + (z 1).natAbs : ℕ) : ℝ)) / L := by
  classical
  let D := adaptedDestination (L := L)
  let E := cubicDestination (L := L)
  have hc (z : IsingScaling.Site) :
      ((univ.filter (fun v : Site L => D z v ≠ E z v)).card : ℝ) ≤
        2 * (L : ℝ)^2 * (((z 0).natAbs + (z 1).natAbs : ℕ) : ℝ) := by
    exact_mod_cast changed_destination_card L z
  have hb := periodize_change D E T J
  let S := ∑ z ∈ T, |J z| * (((z 0).natAbs + (z 1).natAbs : ℕ) : ℝ)
  have hs : (∑ v : Site L, ∑ w : Site L,
      |periodize D T J v w - periodize E T J v w|) ≤ 4 * (L : ℝ)^2 * S := by
    refine hb.trans ?_
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    calc
      _ ≤ (2 * (L : ℝ)^2 * (((z 0).natAbs + (z 1).natAbs : ℕ) : ℝ)) * (2 * |J z|) :=
        mul_le_mul_of_nonneg_right (hc z) (by positivity)
      _ = _ := by ring
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hv : (Fintype.card (Site L) : ℝ) = 2 * (L : ℝ)^3 := by
    simp [Site, Cell, pow_succ]
    ring
  have hp := pressure_distance_by_coupling N (periodize E T J) (periodize D T J)
  change |pressure N (periodize D T J) - pressure N (ordinaryCoupling L T J)| ≤ S / L
  rw [← pressure_twoCopies N (ordinaryCoupling L T J), ← periodize_cubic L T J]
  refine hp.trans ?_
  rw [hv]
  calc
    _ ≤ (4 * (L : ℝ)^2 * S) / 2 / (2 * (L : ℝ)^3) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hs (by norm_num)) (by positivity)
    _ = S / L := by field_simp; ring

/-- Actual fraction of origins where the two quotient destinations differ. -/
def seamFraction (L : ℕ) [NeZero L] (z : IsingScaling.Site) : ℝ :=
  ((univ.filter (fun v : Site L => adaptedDestination z v ≠ cubicDestination z v)).card : ℝ) /
    Fintype.card (Site L)

theorem seamFraction_nonneg (L : ℕ) [NeZero L] (z : IsingScaling.Site) :
    0 ≤ seamFraction L z := by unfold seamFraction; positivity

theorem seamFraction_le_one (L : ℕ) [NeZero L] (z : IsingScaling.Site) :
    seamFraction L z ≤ 1 := by
  classical
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast Finset.card_le_univ _

theorem seamFraction_le_steps (L : ℕ) [NeZero L] (z : IsingScaling.Site) :
    seamFraction L z ≤ (((z 0).natAbs + (z 1).natAbs : ℕ) : ℝ) / L := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hv : (Fintype.card (Site L) : ℝ) = 2 * (L : ℝ)^3 := by
    simp [Site, Cell, pow_succ]
    ring
  have hc := changed_destination_card L z
  unfold seamFraction
  rw [hv]
  apply (div_le_iff₀ (by positivity)).2
  calc
    _ ≤ 2 * (L : ℝ)^2 * (((z 0).natAbs + (z 1).natAbs : ℕ) : ℝ) := by exact_mod_cast hc
    _ = _ := by field_simp

private theorem finite_range_pressure_fraction (N L : ℕ) [NeZero N] [NeZero L]
    (T : Finset IsingScaling.Site) (J : IsingScaling.Site → ℝ) :
    |pressure N (adaptedCoupling L T J) - pressure N (ordinaryCoupling L T J)| ≤
      ∑ z ∈ T, |J z| * seamFraction L z := by
  classical
  let D := adaptedDestination (L := L)
  let E := cubicDestination (L := L)
  have hp := pressure_distance_by_coupling N (periodize E T J) (periodize D T J)
  rw [← pressure_twoCopies N (ordinaryCoupling L T J), ← periodize_cubic L T J]
  refine hp.trans ?_
  calc
    _ ≤ (∑ z ∈ T, (univ.filter (fun v : Site L => D z v ≠ E z v)).card * (2 * |J z|)) / 2 /
          Fintype.card (Site L) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (periodize_change D E T J) (by norm_num)) (by positivity)
    _ = _ := by
      rw [Finset.sum_div, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      unfold seamFraction
      dsimp [D, E]
      ring

/-- Full absolutely summable displacement interactions, including long bonds
which wrap the same finite torus several times. -/
def periodizeSeries {V : Type*} [DecidableEq V] (D : IsingScaling.Site → V → V)
    (J : IsingScaling.Site → ℝ) (v w : V) : ℝ := ∑' z, if D z v = w then J z else 0

def adaptedSeries (L : ℕ) [NeZero L] (J : IsingScaling.Site → ℝ) : Site L → Site L → ℝ :=
  periodizeSeries adaptedDestination J

def ordinarySeries (L : ℕ) [NeZero L] (J : IsingScaling.Site → ℝ) : Cell L → Cell L → ℝ :=
  periodizeSeries baseMove J

private lemma tendsto_periodize {V : Type*} [DecidableEq V] (D : IsingScaling.Site → V → V)
    (J : IsingScaling.Site → ℝ) (hJ : Summable (fun z => |J z|)) (v w : V) :
    Tendsto (fun T => periodize D T J v w) atTop (𝓝 (periodizeSeries D J v w)) := by
  apply Summable.hasSum
  exact hJ.of_norm_bounded fun z => by
    by_cases h : D z v = w <;> simp [h, Real.norm_eq_abs]

private lemma tendsto_periodized_pressure (N : ℕ) [NeZero N] {V : Type*} [Fintype V]
    [DecidableEq V] (D : IsingScaling.Site → V → V) (J : IsingScaling.Site → ℝ)
    (hJ : Summable (fun z => |J z|)) :
    Tendsto (fun T => pressure N (periodize D T J)) atTop (𝓝 (pressure N (periodizeSeries D J))) := by
  apply tendsto_iff_dist_tendsto_zero.2
  simp only [Real.dist_eq]
  refine squeeze_zero (fun _ => abs_nonneg _) (fun T =>
    pressure_distance_by_coupling N (periodizeSeries D J) (periodize D T J)) ?_
  have hf (v w : V) : Tendsto
      (fun T => |periodize D T J v w - periodizeSeries D J v w|) atTop (𝓝 0) := by
    simpa using ((tendsto_periodize D J hJ v w).sub (tendsto_const_nhds
      (x := periodizeSeries D J v w))).abs
  have hs := tendsto_finsetSum (univ : Finset V) (fun v _ =>
    tendsto_finsetSum (univ : Finset V) (fun w _ => hf v w))
  simpa using (hs.div_const 2).div_const (Fintype.card V : ℝ)

/-- The actual long-range sphere pressures on the two particular periodic
geometries differ by at most a summable coupling weighted by seam fractions. -/
theorem summable_pressure_error (N L : ℕ) [NeZero N] [NeZero L]
    (J : IsingScaling.Site → ℝ) (hJ : Summable (fun z => |J z|)) :
    |pressure N (adaptedSeries L J) - pressure N (ordinarySeries L J)| ≤
      ∑' z, |J z| * seamFraction L z := by
  have hu : Summable (fun z => |J z| * seamFraction L z) := by
    apply hJ.of_norm_bounded
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (seamFraction_nonneg L z))]
    exact mul_le_of_le_one_right (abs_nonneg _) (seamFraction_le_one L z)
  exact le_of_tendsto_of_tendsto'
    (((tendsto_periodized_pressure N (adaptedDestination (L := L)) J hJ).sub
      (tendsto_periodized_pressure N (baseMove (L := L)) J hJ)).abs)
    hu.hasSum (fun T => finite_range_pressure_fraction N L T J)

/-- Along every diverging sequence of positive side lengths the actual
per-site free-energy difference vanishes for an arbitrary ℓ¹ coupling. -/
theorem summable_pressure_difference_tendsto (N : ℕ) [NeZero N]
    (J : IsingScaling.Site → ℝ) (hJ : Summable (fun z => |J z|))
    (sides : ℕ → ℕ) [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop) :
    Tendsto (fun n => |pressure N (adaptedSeries (sides n) J) -
      pressure N (ordinarySeries (sides n) J)|) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => abs_nonneg _) (fun n => summable_pressure_error N (sides n) J hJ) ?_
  have hzero z : Tendsto (fun n => seamFraction (sides n) z) atTop (𝓝 0) :=
    squeeze_zero (fun n => seamFraction_nonneg (sides n) z) (fun n => seamFraction_le_steps (sides n) z)
      ((tendsto_const_div_atTop_nhds_zero_nat _).comp hsides)
  have hdom : ∀ n z, ‖|J z| * seamFraction (sides n) z‖ ≤ |J z| := by
    intro n z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (seamFraction_nonneg _ z))]
    exact mul_le_of_le_one_right (abs_nonneg _) (seamFraction_le_one _ z)
  simpa using tendsto_tsum_of_dominated_convergence (f := fun n z => |J z| * seamFraction (sides n) z)
    (g := fun _ => (0 : ℝ)) hJ (fun z => by simpa using (hzero z).const_mul |J z|)
    (Eventually.of_forall hdom)

/-- The original Gibbs pair-energy response at J on the cubes is at most
the response at K on the adapted tori along the same side lengths. Only
the two response limits are assumed; the pressure differences are derived. -/
theorem compare_periodic_pair_responses (N : ℕ) [NeZero N]
    (J K : IsingScaling.Site → ℝ) (hJ : Summable (fun z => |J z|))
    (hK : Summable (fun z => |K z|))
    (sides : ℕ → ℕ) [∀ n, NeZero (sides n)] (hsides : Tendsto sides atTop atTop)
    (u v : ℝ)
    (hu : Tendsto (fun n => response N (ordinarySeries (sides n) J)
      (ordinarySeries (sides n) J) (ordinarySeries (sides n) K)) atTop (𝓝 u))
    (hv : Tendsto (fun n => response N (adaptedSeries (sides n) K)
      (adaptedSeries (sides n) J) (adaptedSeries (sides n) K)) atTop (𝓝 v)) :
    u ≤ v := by
  let δ (F : IsingScaling.Site → ℝ) n :=
    |pressure N (adaptedSeries (sides n) F) - pressure N (ordinarySeries (sides n) F)|
  have hδJ : Tendsto (δ J) atTop (𝓝 0) := summable_pressure_difference_tendsto N J hJ sides hsides
  have hδK : Tendsto (δ K) atTop (𝓝 0) := summable_pressure_difference_tendsto N K hK sides hsides
  have hineq n : response N (ordinarySeries (sides n) J)
      (ordinarySeries (sides n) J) (ordinarySeries (sides n) K) ≤
      response N (adaptedSeries (sides n) K) (adaptedSeries (sides n) J) (adaptedSeries (sides n) K)
        + δ J n + δ K n := by
    have hc := (finite_pressure_sandwich N (ordinarySeries (sides n) J) (ordinarySeries (sides n) K)).1
    have ha := (finite_pressure_sandwich N (adaptedSeries (sides n) J) (adaptedSeries (sides n) K)).2
    have hj := le_abs_self (pressure N (adaptedSeries (sides n) J) - pressure N (ordinarySeries (sides n) J))
    have hk := neg_le_abs (pressure N (adaptedSeries (sides n) K) - pressure N (ordinarySeries (sides n) K))
    dsimp only [δ]
    linarith
  simpa using (le_of_tendsto_of_tendsto' hu ((hv.add hδJ).add hδK) hineq)

end IsingScaling.Rotor.PressureSelection.Seam

#print axioms IsingScaling.Rotor.PressureSelection.Seam.changed_destination_card
#print axioms IsingScaling.Rotor.PressureSelection.Seam.adapted_step_same_period
#print axioms IsingScaling.Rotor.PressureSelection.Seam.adapted_step_unique
#print axioms IsingScaling.Rotor.PressureSelection.Seam.finite_range_pressure_error
#print axioms IsingScaling.Rotor.PressureSelection.Seam.summable_pressure_difference_tendsto
#print axioms IsingScaling.Rotor.PressureSelection.Seam.compare_periodic_pair_responses
