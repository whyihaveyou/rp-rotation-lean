import MathlibProbe.HeisenbergSpinorGates
import MathlibProbe.HeisenbergBlochSphereMoment

/-! # Spinor gates at the physical classical spin and complex field

Tracing each Euler gate against the Bloch projections gives exactly the
classical one-bond and one-site factors. Compactness of a family of physical
fields in the open three-component cone provides one discretization index
valid simultaneously at all its points and all sites of the finite graph.
-/

noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace IsingScaling.Rotor.HeisenbergField.SpinorGates

/-- This is the factor for a directed coupling J when c=J/n.
Dot energy in the finite graph counts directed copies with weight 1/2. -/
theorem physical_bond_gate (c : ℝ) (s t : Spin 3) :
    twoLegTrace (BlochSphere.entry s) (BlochSphere.entry t) (exchangeEntry c) =
      1+((c:ℂ)/2)*(1+(⟪s.val,t.val⟫_ℝ : ℂ)) := by
  rw [exchange_trace,BlochSphere.trace_entry,BlochSphere.trace_entry,one_mul]
  have he : 2*oneLegTrace (BlochSphere.entry s) (BlochSphere.entry t) =
      1+(⟪s.val,t.val⟫_ℝ : ℂ) := by
    simpa only [oneLegTrace, real_inner_comm t.val s.val] using BlochSphere.two_trace_entry_mul t s
  linear_combination (c:ℂ)/2 * he

/-- The field gate reads the full complex linear coupling in the original
three coordinate directions. -/
theorem physical_field_gate (t : ℝ) (H : Fin 3 → ℂ) (s : Spin 3) :
    oneLegTrace (BlochSphere.entry s) (fieldEntry t H) =
      1+(t:ℂ)*∑ i : Fin 3, H i*(s.val i : ℂ) := by
  rw [field_trace,BlochSphere.trace_entry,BlochSphere.z_component,BlochSphere.x_component,
    mul_assoc (H 2) Complex.I,BlochSphere.y_component,Fin.sum_univ_three]

/-- A compact family of strictly admissible physical fields has one finite
Euler cutoff for all sites and all points of the family. -/
theorem field_gates_eventually_on_compact {T V : Type*} [TopologicalSpace T] [Finite V]
    {C : Set T} (hC : IsCompact C) (H : T → V → Fin 3 → ℂ)
    (cont : ∀ v j, ContinuousOn (fun z => H z v j) C)
    (cone : ∀ z ∈ C, ∀ v, ‖H z v 1‖+‖H z v 2‖ < (H z v 0).re) :
    ∀ᶠ n : ℕ in atTop, ∀ v, ∀ z ∈ C, ∀ x y : ℂ, ‖x‖<1 → ‖y‖<1 →
      oneLegSymbol (fieldEntry (1/(n:ℝ)) (H z v)) x y ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro v
  let s (z) := ‖H z v 1‖+‖H z v 2‖
  let g (z) := (H z v 0).re-s z
  have cs : ContinuousOn s C := (cont v 1).norm.add (cont v 2).norm
  have cg : ContinuousOn g C := (Complex.continuous_re.comp_continuousOn (cont v 0)).sub cs
  have gp z (hz : z ∈ C) : 0 < g z := sub_pos.mpr (cone z hz v)
  let q (z) := ‖H z v 0‖*s z/g z
  have cq : ContinuousOn q C :=
    ((cont v 0).norm.mul cs).div cg (fun z hz => (gp z hz).ne')
  obtain ⟨M,hM⟩ := hC.bddAbove_image cq
  have grow : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_gt_atTop M,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro z hz x y hx hy
  have ng : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hq : q z < (n:ℝ) := (hM (Set.mem_image_of_mem q hz)).trans_lt hn
  have b : ‖H z v 0‖*s z < (n:ℝ)*g z := (div_lt_iff₀ (gp z hz)).mp hq
  have c : ‖H z v 0‖*s z/(n:ℝ) < g z :=
    (div_lt_iff₀ ng).mpr (by simpa only [mul_comm (g z)] using b)
  apply field_disk_nonzero (by positivity) _ hx hy
  change (1+(1/(n:ℝ))*‖H z v 0‖)*s z < (H z v 0).re
  rw [show (1+(1/(n:ℝ))*‖H z v 0‖)*s z =
    s z + ‖H z v 0‖*s z/(n:ℝ) by ring]
  dsimp only [g] at c
  linarith

#print axioms physical_bond_gate
#print axioms physical_field_gate
#print axioms field_gates_eventually_on_compact

end IsingScaling.Rotor.HeisenbergField.SpinorGates
