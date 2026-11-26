import MathlibProbe.PottsBondStateSpace
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Metrizable.Basic

/-! A finite open path on the cubic lattice fits in some cube. Its existence
in a fixed cube is a clopen event in the full space of nearest-neighbour
bond configurations. These two facts identify the probability of connection
under a weak limit of free laws with the limit of finite-volume pair
probabilities. -/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Classical Topology

namespace IsingScaling.Potts.FreeBond

theorem cube_monotone : Monotone cube := by
  intro M L hML x hx
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  intro i
  have := hx i
  omega

theorem eventually_mem_cube (x : Site) : ∀ᶠ L : ℕ in atTop, x ∈ cube L := by
  filter_upwards [eventually_ge_atTop (∑ i, (x i).natAbs)] with L hL
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem window_mono : Monotone window := by
  intro M L hML
  exact Finset.subtype_mono (Finset.image_subset_image (Finset.product_subset_product
    (cube_monotone hML) (cube_monotone hML)))

theorem mem_window_iff {L : ℕ} {e : Bond} {u v : Site} (he : e.val = s(u, v)) :
    e ∈ window L ↔ u ∈ cube L ∧ v ∈ cube L := by
  unfold window
  rw [Finset.mem_subtype, he]
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, hab'⟩ := Finset.mem_image.mp h
    rcases Sym2.eq_iff.mp hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.mem_product.mp hab
    · exact (Finset.mem_product.mp hab).symm
  · intro h
    exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr h, rfl⟩

theorem eventually_mem_window (e : Bond) : ∀ᶠ L : ℕ in atTop, e ∈ window L := by
  obtain ⟨u, v, he, _⟩ := e.property
  filter_upwards [eventually_mem_cube u, eventually_mem_cube v] with L hu hv
  exact (mem_window_iff he).mpr ⟨hu, hv⟩

theorem within_mono (x y : Site) : Monotone (fun L => within L x y) := by
  intro M L hML ω hω
  exact Relation.EqvGen.mono (fun _ _ ⟨e, he, huv, hopen⟩ =>
    ⟨e, window_mono hML he, huv, hopen⟩) _ _ hω

theorem within_mono_field {L : ℕ} {x y : Site} {ω η : Field}
    (h : ∀ e, ω e = true → η e = true)
    (hω : ω ∈ within L x y) : η ∈ within L x y :=
  Relation.EqvGen.mono (fun _ _ ⟨e, he, huv, hopen⟩ =>
    ⟨e, he, huv, h e hopen⟩) _ _ hω

theorem within_subset_connection (L : ℕ) (x y : Site) : within L x y ⊆ connection x y := by
  intro ω hω
  exact Relation.EqvGen.mono (fun _ _ ⟨e, _, huv, hopen⟩ => ⟨e, huv, hopen⟩) _ _ hω

/-- Restricting to the bonds of the cube completely determines its path event. -/
theorem within_eq_cylinder (L : ℕ) (x y : Site) :
    ∃ A : Set (↥(window L) → Bool), within L x y = (window L).restrict ⁻¹' A := by
  let A : Set (↥(window L) → Bool) := {b | Relation.EqvGen
    (fun u v : Site => ∃ e : ↥(window L), e.val.val = s(u, v) ∧ b e = true) x y}
  refine ⟨A, ?_⟩
  ext ω
  constructor
  · intro hω
    exact Relation.EqvGen.mono (fun _ _ ⟨e, he, huv, hopen⟩ =>
      ⟨⟨e, he⟩, huv, hopen⟩) _ _ hω
  · intro hω
    exact Relation.EqvGen.mono (fun _ _ ⟨e, huv, hopen⟩ =>
      ⟨e.val, e.property, huv, hopen⟩) _ _ hω

theorem within_isClopen (L : ℕ) (x y : Site) : IsClopen (within L x y) := by
  obtain ⟨A, h⟩ := within_eq_cylinder L x y
  rw [h]
  exact (isClopen_discrete A).preimage (Finset.continuous_restrict _)

/-- Induction on a path certificate gives a radius for the whole path.
Concatenation takes the larger of the radii of its two parts. -/
theorem iUnion_within (x y : Site) : (⋃ L, within L x y) = connection x y := by
  refine Set.Subset.antisymm (iUnion_subset fun L => within_subset_connection L x y) ?_
  intro ω hω
  apply mem_iUnion.mpr
  change Relation.EqvGen _ x y at hω
  induction hω with
  | rel u v h =>
    obtain ⟨e, he, hop⟩ := h
    obtain ⟨L, hL⟩ := (eventually_mem_window e).exists
    exact ⟨L, Relation.EqvGen.rel _ _ ⟨e, hL, he, hop⟩⟩
  | refl u => exact ⟨0, Relation.EqvGen.refl _⟩
  | symm u v _ ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L, Relation.EqvGen.symm _ _ hL⟩
  | trans u v w _ _ huv hvw =>
    obtain ⟨M, hM⟩ := huv
    obtain ⟨L, hL⟩ := hvw
    exact ⟨max M L, Relation.EqvGen.trans _ _ _
      (within_mono u v (le_max_left M L) hM) (within_mono v w (le_max_right M L) hL)⟩

theorem connection_isOpen (x y : Site) : IsOpen (connection x y) := by
  rw [← iUnion_within]
  exact isOpen_iUnion fun L => (within_isClopen L x y).isOpen

theorem within_probability_tendsto (μ : ProbabilityMeasure Field) (x y : Site) :
    Tendsto (fun L => (μ (within L x y) : ℝ)) atTop (𝓝 (μ (connection x y) : ℝ)) := by
  have h := tendsto_measure_iUnion_atTop (μ := (μ : Measure Field)) (within_mono x y)
  rw [iUnion_within] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

/-- For a subsequential limit, clopen fixed-window probabilities converge.
Volume comparison gives the lower bound from the small free box, while
inclusion in the large-box path event gives the upper bound. Passing to
the limit in the window radius determines full-lattice connectivity. -/
theorem connection_eq_of_subseq {P : ℕ → ProbabilityMeasure Field} {μ : ProbabilityMeasure Field}
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hP : Tendsto (fun j => P (k j)) atTop (𝓝 μ)) (x y : Site) {g : ℝ}
    (hp : Tendsto (fun L => (P L (within L x y) : ℝ)) atTop (𝓝 g))
    (hcomp : ∀ M L, M ≤ L → P M (within M x y) ≤ P L (within M x y)) :
    (μ (connection x y) : ℝ) = g := by
  have hcyl (M : ℕ) :
      Tendsto (fun j => (P (k j) (within M x y) : ℝ)) atTop (𝓝 (μ (within M x y) : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hP (within_isClopen M x y))
  have hdiag := hp.comp hk
  have hlow (M : ℕ) : (P M (within M x y) : ℝ) ≤ μ (within M x y) := by
    apply ge_of_tendsto (hcyl M)
    filter_upwards [hk.eventually (eventually_ge_atTop M)] with j hj
    exact_mod_cast hcomp M (k j) hj
  have hupp (M : ℕ) : (μ (within M x y) : ℝ) ≤ g := by
    apply le_of_tendsto_of_tendsto (hcyl M) hdiag
    filter_upwards [hk.eventually (eventually_ge_atTop M)] with j hj
    exact_mod_cast (P (k j)).apply_mono (within_mono x y hj)
  have hμ := within_probability_tendsto μ x y
  exact le_antisymm (le_of_tendsto hμ (Eventually.of_forall hupp))
    (le_of_tendsto_of_tendsto hp hμ (Eventually.of_forall hlow))

#print axioms within_isClopen
#print axioms iUnion_within
#print axioms connection_eq_of_subseq

end IsingScaling.Potts.FreeBond
