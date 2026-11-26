import MathlibProbe.RotorPhysicalAdmissibleVariations

/-! # Symmetries of the original summable rotor couplings

A signed coordinate permutation reindexes lattice ℓ¹ isometrically and
fixes its impulse at the origin. A pair of opposite shifts in one
coordinate is carried to the corresponding opposite pair in its image
coordinate. These opposite-shift sums commute. Thus the three sums of
axial, face-diagonal and body-diagonal steps each commute with every
signed permutation. The physical perturbation slots are the identity,
the third-coordinate pair, and the product of the first two pairs.
They commute with independent sign changes and all permutations fixing
the third coordinate. Commutation passes to the actual resolvent:
on units this is inversion and on nonunits the total ring inverse
vanishes. Evaluating at the impulse gives pointwise identities of the
original lattice profiles, also outside the Neumann-series regime.
Summation over the physical components retains the same symmetries.
-/

noncomputable section

open scoped ENNReal
open Filter Finset
namespace IsingScaling.Rotor.PressureSelection.PhysicalVariations
open LatticeWalk

private theorem act_coord (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) (i : Fin 3) :
    signedPerm p s z i = if s i then -z (p i) else z (p i) := rfl

private theorem act_add (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z w : Site) :
    signedPerm p s (z+w) = signedPerm p s z + signedPerm p s w := by
  funext i
  simp only [act_coord,Pi.add_apply]
  split <;> ring

private theorem act_sub (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z w : Site) :
    signedPerm p s (z-w) = signedPerm p s z - signedPerm p s w := by
  funext i
  simp only [act_coord,Pi.sub_apply]
  split <;> ring

private theorem act_unit (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (i : Fin 3) :
    signedPerm p s (unit i) = if s (p.symm i) then -unit (p.symm i) else unit (p.symm i) := by
  funext j
  by_cases he : j=p.symm i
  · subst j
    cases hs : s (p.symm i) <;> simp [act_coord,unit,hs]
  · have h' : p j≠i := fun h => he (p.eq_symm_apply.mpr h)
    cases h₁ : s (p.symm i) <;> cases h₂ : s j <;>
      simp [act_coord,unit,h₂,he,h']

private theorem both_action (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (i : Fin 3) (f : Profile)
    (z : Site) : both i (fun y => f (signedPerm p s y)) z =
      both (p.symm i) f (signedPerm p s z) := by
  simp only [both,act_add,act_sub,act_unit]
  cases h : s (p.symm i) <;> simp [sub_eq_add_neg,add_comm]

private theorem orbit_action (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (l : List (Fin 3))
    (f : Profile) (z : Site) :
    orbit l (fun y => f (signedPerm p s y)) z =
      orbit (l.map p.symm) f (signedPerm p s z) := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    simp only [orbit,List.map_cons]
    have e : orbit l (fun y => f (signedPerm p s y)) =
        fun y => orbit (l.map p.symm) f (signedPerm p s y) := funext ih
    rw [e,both_action]

private theorem orbit_perm {l l' : List (Fin 3)} (h : l.Perm l') (f : Profile) :
    orbit l f = orbit l' f := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [orbit,ih]
  | swap i j l =>
    funext z
    simp [orbit,both,sub_eq_add_neg,add_comm,add_left_comm,add_assoc]
  | trans h g ih jh => exact ih.trans jh

private def other : Fin 3 → List (Fin 3) := ![[1,2],[0,2],[0,1]]
private def allAxes : List (Fin 3) := [0,1,2]

private theorem other_mem (i k : Fin 3) : k ∈ other i ↔ k≠i := by
  fin_cases i <;> fin_cases k <;> decide

private theorem other_nodup (i : Fin 3) : (other i).Nodup := by fin_cases i <;> decide

private theorem perm_other (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ((other i).map p).Perm (other (p i)) := by
  apply (List.perm_ext_iff_of_nodup ((other_nodup i).map p.injective) (other_nodup _)).mpr
  intro k
  rw [List.mem_map,other_mem]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact fun he => (other_mem _ _).mp hj (p.injective he)
  · intro h
    exact ⟨p.symm k,(other_mem _ _).mpr (fun he => h ((p.apply_symm_apply k).symm.trans (congrArg p he))),
      p.apply_symm_apply k⟩

private theorem perm_all (p : Equiv.Perm (Fin 3)) : (allAxes.map p).Perm allAxes := by
  have nd : allAxes.Nodup := by decide
  have un (i : Fin 3) : i ∈ allAxes := by fin_cases i <;> decide
  apply (List.perm_ext_iff_of_nodup (nd.map p.injective) nd).mpr
  intro i
  exact ⟨fun _ => un _,fun _ => List.mem_map.mpr ⟨p.symm i,un _,p.apply_symm_apply i⟩⟩

private theorem step_axes (a b c : ℝ) (f : Profile) (z : Site) :
    step a b c f z = a*(∑ i : Fin 3, orbit [i] f z) +
      b*(∑ i : Fin 3, orbit (other i) f z) + c*orbit allAxes f z := by
  simp [step,directions,weight,other,allAxes,Fin.sum_univ_succ]
  ring

private theorem step_action (a b c : ℝ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (f : Profile) (z : Site) :
    step a b c (fun y => f (signedPerm p s y)) z = step a b c f (signedPerm p s z) := by
  rw [step_axes,step_axes]
  simp_rw [orbit_action]
  simp only [List.map_cons,List.map_nil]
  have hp (i : Fin 3) := orbit_perm (perm_other p.symm i) f
  simp_rw [hp]
  rw [orbit_perm (perm_all p.symm)]
  rw [p.symm.sum_comp (fun i => orbit [i] f (signedPerm p s z)),
    p.symm.sum_comp (fun i => orbit (other i) f (signedPerm p s z))]

private def pullLM (e : Equiv.Perm Site) : LatticeL1 →ₗ[ℝ] LatticeL1 where
  toFun f := ⟨fun z => f (e z), by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)).2
    simpa [Function.comp_def] using e.summable_iff.mpr (f.2.summable_of_one.norm)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pull_norm (e : Equiv.Perm Site) (f : LatticeL1) : ‖pullLM e f‖=‖f‖ := by
  simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal),ENNReal.toReal_one,
    Real.rpow_one,div_one]
  exact e.tsum_eq (fun z => ‖f z‖)

private def pull (e : Equiv.Perm Site) : Operator :=
  (pullLM e).mkContinuous 1 fun f => by rw [pull_norm,one_mul]

private theorem commute_walk (a b c : ℝ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Commute (pull (signedPerm p s)) (walkOperator a b c) := by
  ext f z
  change walkOperator a b c f (signedPerm p s z) = walkOperator a b c (pull (signedPerm p s) f) z
  simp only [walkOperator_apply]
  exact (step_action a b c p s f z).symm

private theorem commute_slot (i : Fin 3) (p : Equiv.Perm (Fin 3)) (hp : p 2=2) (s : Fin 3 → Bool) :
    Commute (pull (signedPerm p s)) (orbitOperator (sites i)) := by
  have h₂ : p.symm 2=2 := by rw [← hp,p.symm_apply_apply,hp]
  have h : ((sites i).map p.symm).Perm (sites i) := by
    fin_cases i
    · exact List.Perm.nil
    · change ([2].map p.symm).Perm [2]
      simp [h₂]
    · change ((other 2).map p.symm).Perm (other 2)
      simpa only [h₂] using perm_other p.symm 2
  ext f z
  change orbitOperator (sites i) f (signedPerm p s z) =
    orbitOperator (sites i) (pull (signedPerm p s) f) z
  simp only [orbitOperator_apply]
  exact ((orbit_action p s (sites i) f z).trans (congrFun (orbit_perm h f) _)).symm

private theorem pull_impulse (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    pull (signedPerm p s) impulse = impulse := by
  ext z
  change (lp.single 1 0 (1:ℝ) : LatticeL1) (signedPerm p s z) =
    (lp.single 1 0 (1:ℝ) : LatticeL1) z
  have hz : signedPerm p s z=0 ↔ z=0 :=
    by simpa only [signedPerm_zero] using (signedPerm p s).injective.eq_iff (a:=z) (b:=0)
  by_cases h : z=0
  · simp [h]
  · simp [lp.single_apply,h,mt hz.mp h]

private theorem commute_inverse {A B : Operator} (h : Commute A B) : Commute A (Ring.inverse B) := by
  by_cases hu : IsUnit B
  · obtain ⟨u,rfl⟩ := hu
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right _

private theorem inverse_invariant {B : Operator} (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (hc : Commute (pull (signedPerm p s)) B) (z : Site) :
    ((resolvent B (1:ℝ)) impulse) (signedPerm p s z) = ((resolvent B (1:ℝ)) impulse) z := by
  have h : Commute (pull (signedPerm p s)) (resolvent B (1:ℝ)) := by
    simp only [resolvent,map_one]
    exact commute_inverse ((Commute.one_right _).sub_right hc)
  have h' := congrArg (fun T : Operator => T impulse) h.eq
  change pull (signedPerm p s) ((resolvent B (1:ℝ)) impulse) =
    (resolvent B (1:ℝ)) (pull (signedPerm p s) impulse) at h'
  rw [pull_impulse] at h'
  exact congrArg (fun f : LatticeL1 => f z) h'

/-- All independent sign changes and every axis permutation fixing axis 2
preserve every physical perturbed resolvent, for every real parameter. -/
theorem component_signedPerm_of_fix (j : Index) (t : ℝ) (p : Equiv.Perm (Fin 3))
    (hp : p 2=2) (s : Fin 3 → Bool) (z : Site) :
    component j t (signedPerm p s z) = component j t z := by
  apply inverse_invariant
  exact (commute_walk (a j) (b j) (c j) p s).add_right ((commute_slot j.2 p hp s).smul_right t)

/-- At the unperturbed point every component has all signed cubic symmetries. -/
theorem C_signedPerm (j : Index) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) :
    C j (signedPerm p s z) = C j z := by
  change ((resolvent (walkOperator (a j) (b j) (c j)+0 • orbitOperator (sites j.2)) (1:ℝ)) impulse) _=_
  simp only [C,component,operatorCurve,zero_smul,add_zero]
  exact inverse_invariant p s (commute_walk (a j) (b j) (c j) p s) z

theorem nearest_signedPerm (β : ℝ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) :
    LocalGibbs.nearestCoupling β (signedPerm p s z) = LocalGibbs.nearestCoupling β z := by
  have hd := signedPerm_distance p s 0 z
  rw [signedPerm_zero] at hd
  simp [LocalGibbs.nearestCoupling,LocalGibbs.mem_nearestSteps_iff_latticeDistance,hd]

theorem perturbed_signedPerm_of_fix (β δ : ℝ) (d : Index →₀ ℝ) (t : ℝ)
    (p : Equiv.Perm (Fin 3)) (hp : p 2=2) (s : Fin 3 → Bool) (z : Site) :
    perturbed β δ d t (signedPerm p s z) = perturbed β δ d t z := by
  rw [perturbed_apply,perturbed_apply,nearest_signedPerm]
  congr 2
  exact tsum_congr (fun j => congrArg (alpha j * ·) (component_signedPerm_of_fix j _ p hp s z))

theorem perturbed_horizontal (β δ : ℝ) (d : Index →₀ ℝ) (t : ℝ)
    (b : Bool) (s : Fin 3 → Bool) (z : Site) :
    perturbed β δ d t (signedPerm (if b then Equiv.swap 0 1 else Equiv.refl _) s z) =
      perturbed β δ d t z := by
  apply perturbed_signedPerm_of_fix
  cases b <;> decide

/-- The full cubic group acts on the unperturbed coupling, including its original
nearest-neighbour term and the entire positive countable resolvent mixture. -/
theorem J_signedPerm (β δ : ℝ) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) :
    J β δ (signedPerm p s z) = J β δ z := by
  rw [←perturbed_zero β δ (0 : Index →₀ ℝ),perturbed_apply,perturbed_apply,nearest_signedPerm]
  simp only [mul_zero,component_zero,C_signedPerm]

theorem mixture_signedPerm (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) :
    mixture (signedPerm p s z) = mixture z := by
  have h := J_signedPerm 0 1 p s z
  change LocalGibbs.nearestCoupling 0 (signedPerm p s z) + 1*mixture (signedPerm p s z) =
    LocalGibbs.nearestCoupling 0 z + 1*mixture z at h
  simpa [LocalGibbs.nearestCoupling] using h

theorem J_nonnegative {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (z : Site) :
    0 ≤ J β δ z := by
  rw [J_apply]
  apply add_nonneg (by unfold LocalGibbs.nearestCoupling; split <;> positivity)
  exact mul_nonneg hδ (tsum_nonneg fun j => mul_nonneg (alpha_pos j).le
    (by simpa only [component_zero_apply] using C_nonneg j z))

theorem perturbed_nonnegative_of_allowed {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (d : Index →₀ ℝ) (t : ℝ) (h : ∀ j, Allowed j (speed δ d j*t)) (z : Site) :
    0 ≤ perturbed β δ d t z := by
  rw [perturbed_apply]
  exact add_nonneg (by unfold LocalGibbs.nearestCoupling; split <;> positivity)
    (mul_nonneg hδ (tsum_nonneg fun j => mul_nonneg (alpha_pos j).le ((h j).2.2.2.2.2.2.2 z)))

theorem J_even (β δ : ℝ) (z : Site) : J β δ (-z) = J β δ z :=
  J_signedPerm β δ (Equiv.refl _) (fun _ => true) z

theorem perturbed_even (β δ : ℝ) (d : Index →₀ ℝ) (t : ℝ) (z : Site) :
    perturbed β δ d t (-z) = perturbed β δ d t z :=
  perturbed_horizontal β δ d t false (fun _ => true) z

#print axioms component_signedPerm_of_fix
#print axioms perturbed_horizontal
#print axioms J_signedPerm

end IsingScaling.Rotor.PressureSelection.PhysicalVariations
