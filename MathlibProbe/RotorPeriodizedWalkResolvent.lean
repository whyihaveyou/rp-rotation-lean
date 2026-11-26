import MathlibProbe.RotorLatticeWalkResolvent
import MathlibProbe.RotorPrecisionLatticeSeam
import MathlibProbe.RotorPrecisionAxialSeam

/-! # Periodization of the massive lattice walk on the two pressure tori

For a lattice displacement z let D(z)x be its actual finite destination.
Projection sums all original displacements with D(z)x=y. Reindexing by a
unit translation intertwines projection with the two shifts in each
walk coordinate. Iterating over the coordinate subset and summing the
seven physical weights gives P(Hf)=H_per P(f). Project the exact lattice
resolvent equation. The lattice impulse projects to the identity matrix,
and the resulting right inverse equals the nonsingular matrix inverse.
No distinctness of the images of finite steps is used.
-/

noncomputable section
open Finset
open Filter Topology
namespace IsingScaling.Rotor.PressureSelection.PeriodizedWalk
open LatticeWalk

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite hopping matrix, *counting* all coincident destinations. -/
def walkMatrix (D : Site → V → V) (v : Fin 7 → ℝ) : Matrix V V ℝ :=
  fun x y => ∑ j, v j * orbit (directions j) (fun z => DiagonalSeam.bit (D z x=y)) 0

section
omit [Fintype V]

private theorem cell_summable (D : Site → V → V) {f : Profile} (hf : Summable f) (x y : V) :
    Summable (fun z => if D z x = y then f z else 0) := by
  apply hf.norm.of_norm_bounded
  intro z
  by_cases h : D z x=y <;> simp [h]

private theorem proj_add (D : Site → V → V) {f g : Profile} (hf : Summable f) (hg : Summable g)
    (x y : V) : Seam.periodizeSeries D (fun z => f z + g z) x y =
      Seam.periodizeSeries D f x y + Seam.periodizeSeries D g x y := by
  unfold Seam.periodizeSeries
  rw [← (cell_summable D hf x y).tsum_add (cell_summable D hg x y)]
  apply tsum_congr
  intro z
  by_cases h : D z x = y <;> simp [h]

private theorem proj_sub (D : Site → V → V) {f g : Profile} (hf : Summable f) (hg : Summable g)
    (x y : V) : Seam.periodizeSeries D (fun z => f z - g z) x y =
      Seam.periodizeSeries D f x y - Seam.periodizeSeries D g x y := by
  unfold Seam.periodizeSeries
  rw [← (cell_summable D hf x y).tsum_sub (cell_summable D hg x y)]
  apply tsum_congr
  intro z
  by_cases h : D z x = y <;> simp [h]

private theorem proj_smul (D : Site → V → V) (r : ℝ) (f : Profile) (x y : V) :
    Seam.periodizeSeries D (fun z => r*f z) x y = r * Seam.periodizeSeries D f x y := by
  unfold Seam.periodizeSeries
  rw [← tsum_mul_left]
  exact tsum_congr fun z => by by_cases h : D z x=y <;> simp [h]

private theorem proj_translate (D : Site → V → V)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x))
    (f : Profile) (d : Site) (x y : V) :
    Seam.periodizeSeries D (fun z => f (z+d)) x y =
      Seam.periodizeSeries D f (D (-d) x) y := by
  unfold Seam.periodizeSeries
  rw [← (Equiv.addRight d).tsum_eq (fun z => if D z (D (-d) x)=y then f z else 0)]
  apply tsum_congr
  intro u
  have h : D (u+d) (D (-d) x) = D u x := by rw [←hadd]; congr 1; abel
  simp only [Equiv.coe_addRight,h]

private theorem proj_orbit (D : Site → V → V)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x))
    {f : Profile} (hf : Summable f) (l : List (Fin 3)) (x y : V) (z : Site) :
    Seam.periodizeSeries D (orbit l f) (D z x) y =
      orbit l (fun p => Seam.periodizeSeries D f (D p x) y) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
      let g := orbit l f
      have hs := orbit_summable l hf
      let u := unit i
      have hp : Summable (fun z => g (z+u)) := (Equiv.addRight u).summable_iff.mpr hs
      have hm : Summable (fun z => g (z+ -u)) := (Equiv.addRight (-u)).summable_iff.mpr hs
      change Seam.periodizeSeries D (fun p => g (p+u)+g (p-u)) (D z x) y = _
      simp only [sub_eq_add_neg]
      rw [proj_add D hp hm,proj_translate D hadd,proj_translate D hadd,neg_neg,←hadd,←hadd]
      change Seam.periodizeSeries D (orbit l f) (D (z+-u) x) y +
        Seam.periodizeSeries D (orbit l f) (D (z+u) x) y = _
      rw [ih,ih]
      change _ = orbit l _ (z+u)+orbit l _ (z-u)
      rw [sub_eq_add_neg,add_comm]

end

private theorem orbit_expect (D : Site → V → V) (l : List (Fin 3)) (x : V) (z : Site)
    (F : V → ℝ) :
    ∑ y, orbit l (fun p => DiagonalSeam.bit (D p x=y)) z * F y =
      orbit l (fun p => F (D p x)) z := by
  induction l generalizing z with
  | nil => classical simp [orbit,DiagonalSeam.bit,ite_mul]
  | cons i l ih => simp only [orbit,both,add_mul,Finset.sum_add_distrib,ih]

omit [Fintype V] in
theorem walkMatrix_nonneg (D : Site → V → V) (v : Fin 7 → ℝ) (hv : ∀ j, 0 ≤ v j)
    (x y : V) : 0 ≤ walkMatrix D v x y := by
  apply Finset.sum_nonneg
  exact fun j _ => mul_nonneg (hv j) (orbit_nonneg _ (fun z => by
    dsimp only [DiagonalSeam.bit]
    split_ifs <;> norm_num) 0)

private theorem orbit_constant_one (l : List (Fin 3)) (z : Site) :
    orbit l (fun _ => 1) z = (2:ℝ)^l.length := by
  induction l generalizing z with
  | nil => simp [orbit]
  | cons i l ih => simp only [orbit,both,ih,List.length_cons,pow_succ]; ring

/-- The row mass keeps even coincident steps at periods one and two. -/
theorem walkMatrix_row_sum (D : Site → V → V) (v : Fin 7 → ℝ) (x : V) :
    ∑ y, walkMatrix D v x y = ∑ j, v j * (2:ℝ)^(directions j).length := by
  simp only [walkMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.mul_sum]
  have h := orbit_expect D (directions j) x 0 (fun _ => 1)
  simp only [mul_one,orbit_constant_one] at h
  rw [h]

theorem row_mass_weights (a b c : ℝ) :
    (∑ j, weight a b c j * (2:ℝ)^(directions j).length) = 6*a+12*b+8*c := by
  simp [Fin.sum_univ_succ,weight,directions]
  ring

/-- The inequalities ensuring finite positive precision persist for a
two-sided perturbation interval, uniformly in the choice of torus. -/
theorem eventually_admissible_weights {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgap : 6*a+12*b+8*c < 1) (m : ℝ) (d : Fin 7 → ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), (∀ j, 0 ≤ weight a b c j+t*d j) ∧
      ∑ j, (weight a b c j+t*d j) * (2:ℝ)^(directions j).length < 1-t*m ∧
      ‖walkOperator a b c + t • (m • (1:Operator) + hopping d)‖ < 1 := by
  have hweights : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, 0 < weight a b c j+t*d j := by
    rw [Filter.eventually_all]
    intro j
    have h0 : 0 < weight a b c j := by fin_cases j <;> first | exact ha | exact hb | exact hc
    exact (isOpen_lt continuous_const (show Continuous (fun t : ℝ => weight a b c j+t*d j) by
      fun_prop)).mem_nhds (by simpa using h0)
  have hmass : ∀ᶠ t in 𝓝 (0:ℝ),
      ∑ j, (weight a b c j+t*d j) * (2:ℝ)^(directions j).length < 1-t*m :=
    (isOpen_lt (show Continuous (fun t : ℝ =>
      ∑ j, (weight a b c j+t*d j) * (2:ℝ)^(directions j).length) by fun_prop)
      (show Continuous (fun t : ℝ => 1-t*m) by fun_prop)).mem_nhds (by simpa [row_mass_weights] using hgap)
  have hop : ∀ᶠ t in 𝓝 (0:ℝ), ‖walkOperator a b c + t • (m • (1:Operator) + hopping d)‖ < 1 :=
    (isOpen_lt (show Continuous (fun t : ℝ =>
      ‖walkOperator a b c + t • (m • (1:Operator) + hopping d)‖) by fun_prop)
      continuous_const).mem_nhds (by simpa using (norm_walkOperator ha.le hb.le hc.le).trans_lt hgap)
  filter_upwards [hweights,hmass,hop] with t hw hrow ht
  exact ⟨fun j => (hw j).le,hrow,ht⟩

private theorem orbit_reverse (l : List (Fin 3)) {f g : Profile} (h : ∀ z, f (-z)=g z) :
    ∀ z, orbit l f (-z) = orbit l g z := by
  induction l with
  | nil => exact h
  | cons i l ih =>
      intro z
      have hp : -z+unit i = -(z-unit i) := by abel
      have hm : -z-unit i = -(z+unit i) := by abel
      simp only [orbit,both,hp,hm,ih]
      exact add_comm ..

omit [Fintype V] in
theorem walkMatrix_isHermitian (D : Site → V → V) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x)) (v : Fin 7 → ℝ) :
    (walkMatrix D v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  change walkMatrix D v y x = walkMatrix D v x y
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have rev (z : Site) : D (-z) y = x ↔ D z x = y := by
    constructor
    · intro e
      rw [←e,←hadd,neg_add_cancel,hzero]
    · intro e
      rw [←e,←hadd,add_neg_cancel,hzero]
  have h := orbit_reverse (directions j)
    (f := fun p => DiagonalSeam.bit (D p y=x)) (g := fun p => DiagonalSeam.bit (D p x=y))
    (fun z => by
      by_cases e : D z x=y
      · simp [DiagonalSeam.bit,e,(rev z).2 e]
      · have he : D (-z) y ≠ x := fun hp => e ((rev z).1 hp)
        simp [DiagonalSeam.bit,e,he]) 0
  simpa only [neg_zero] using h

private theorem proj_hops (D : Site → V → V) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x))
    (v : Fin 7 → ℝ) {f : Profile} (hf : Summable f) (x y : V) :
    Seam.periodizeSeries D (fun z => ∑ j, v j*orbit (directions j) f z) x y =
      (walkMatrix D v * Matrix.of (Seam.periodizeSeries D f)) x y := by
  have hi (j : Fin 7) := (cell_summable D (orbit_summable (directions j) hf) x y).hasSum.mul_left (v j)
  have HH := hasSum_sum (s := Finset.univ) (fun j _ => hi j)
  calc
    Seam.periodizeSeries D (fun z => ∑ j, v j*orbit (directions j) f z) x y =
        ∑ j, v j * Seam.periodizeSeries D (orbit (directions j) f) x y := by
      apply HasSum.tsum_eq
      exact HH.congr_fun fun z => by by_cases h : D z x=y <;> simp [h]
    _ = ∑ j, v j * orbit (directions j) (fun p => Seam.periodizeSeries D f (D p x) y) 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (v j * ·) (by simpa only [hzero] using proj_orbit D hadd hf (directions j) x y 0)
    _ = _ := by
      simp only [walkMatrix,Matrix.mul_apply,Matrix.of_apply,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have h := orbit_expect D (directions j) x 0 (fun p => Seam.periodizeSeries D f p y)
      simp only [mul_assoc,←Finset.mul_sum]
      rw [h]

omit [Fintype V] in
private theorem proj_impulse (D : Site → V → V) (hzero : ∀ x, D 0 x=x) (x y : V) :
    Seam.periodizeSeries D delta x y = (1 : Matrix V V ℝ) x y := by
  classical
  unfold Seam.periodizeSeries
  rw [tsum_eq_single 0]
  · simp [delta,hzero,Matrix.one_apply]
  · intro z hz
    by_cases h : D z x=y <;> simp [h,delta,hz]

/-- A lattice resolvent equation transfers to the true finite matrix on
any finite additive destination, with the same mass and the same hops. -/
theorem eq_inverse_of_lattice_equation (D : Site → V → V) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x))
    (v : Fin 7 → ℝ) (M : ℝ) (f : LatticeL1)
    (heq : ∀ z, M*f z - ∑ j, v j*orbit (directions j) f z = delta z) :
    Matrix.of (Seam.periodizeSeries D f) = (Matrix.diagonal (fun _ => M)-walkMatrix D v)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_right_inv
  ext x y
  rw [sub_mul,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.of_apply]
  have hf := f.2.summable_of_one
  have hs := (hasSum_sum (s := Finset.univ) (fun j _ => (orbit_summable (directions j) hf).hasSum.mul_left
    (v j))).summable
  rw [←proj_smul,←proj_hops D hzero hadd v hf,←proj_sub D (hf.mul_left _) hs]
  simp only [heq,proj_impulse D hzero]

private theorem scaledWeights (a b c M : ℝ) (j : Fin 7) :
    weight (a/M) (b/M) (c/M) j = M⁻¹ * weight a b c j := by
  fin_cases j <;> simp [weight,div_eq_mul_inv,mul_comm]

private theorem scaledOperator (a b c M : ℝ) :
    walkOperator (a/M) (b/M) (c/M) = M⁻¹ • walkOperator a b c := by
  simp only [walkOperator,Finset.smul_sum,smul_smul,scaledWeights]

private theorem impulse_value (z : Site) : impulse z = delta z := by
  by_cases h : z=0 <;> simp [impulse,delta,h]

/-- The full lattice coupling produced by its Neumann series, with
arbitrary physical mass. No finite-volume resolvent is assumed. -/
theorem periodize_coupling_eq_inverse (D : Site → V → V) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x))
    {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : 0 < M) (hgap : 6*a+12*b+8*c < M) :
    Matrix.of (Seam.periodizeSeries D (coupling a b c M)) =
      (Matrix.diagonal (fun _ => M)-walkMatrix D (weight a b c))⁻¹ := by
  have h1 := div_nonneg ha hM.le
  have h2 := div_nonneg hb hM.le
  have h3 := div_nonneg hc hM.le
  have h4 : 6*(a/M)+12*(b/M)+8*(c/M) < 1 := by
    calc 6*(a/M)+12*(b/M)+8*(c/M) = (6*a+12*b+8*c)/M := by ring
         _ < 1 := (div_lt_one hM).mpr hgap
  let g := operatorCurve (a/M) (b/M) (c/M) (0:Operator) 0
  let f : LatticeL1 := M⁻¹ • g
  have hf : ⇑f = coupling a b c M := by
    funext z
    change M⁻¹*g z = _
    have hh := operatorCurve_zero h1 h2 h3 h4 (0:Operator) z
    change g z = _ at hh
    rw [hh]
    simp [coupling]
  have hn : ‖walkOperator (a/M) (b/M) (c/M) + (0:ℝ) • (0:Operator)‖ < 1 := by
    simpa only [zero_smul,add_zero] using (norm_walkOperator h1 h2 h3).trans_lt h4
  have hg := operatorCurve_equation (a/M) (b/M) (c/M) 0 0 hn
  change g-(walkOperator (a/M) (b/M) (c/M)+ (0:ℝ) • (0:Operator)) g = impulse at hg
  simp only [zero_smul,add_zero,scaledOperator,_root_.smul_apply] at hg
  have hq : M • f - walkOperator a b c f = impulse := by
    dsimp only [f]
    simpa only [smul_smul,mul_inv_cancel₀ hM.ne',one_smul,map_smul] using hg
  rw [← hf]
  apply eq_inverse_of_lattice_equation D hzero hadd _ _ f
  intro z
  have hv := congrArg (fun F : LatticeL1 => F z) hq
  simpa only [lp.coeFn_sub,lp.coeFn_smul, Pi.sub_apply,Pi.smul_apply,smul_eq_mul,step,
    walkOperator_apply,impulse_value] using hv

private theorem hopping_value (v : Fin 7 → ℝ) (f : LatticeL1) (z : Site) :
    hopping v f z = ∑ j, v j * orbit (directions j) f z := by
  let E := lp.evalCLM ℝ (fun _ : Site => ℝ) 1 z
  change E ((∑ j, v j • orbitOperator (directions j)) f) = _
  rw [_root_.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change v j * orbitOperator (directions j) f z = _
  rw [orbitOperator_apply]

/-- The same periodization identity for the actual perturbed infinite
lattice curve used in the pressure derivatives. The positive mass is
changed by -t*m and each of the seven signed-step orbits by t*d_j. -/
theorem periodize_operatorCurve_eq_inverse (D : Site → V → V) (hzero : ∀ x, D 0 x=x)
    (hadd : ∀ z t x, D (z+t) x = D t (D z x)) (a b c m t : ℝ) (d : Fin 7 → ℝ)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator) + hopping d)‖ < 1) :
    let f := operatorCurve a b c (m • (1:Operator) + hopping d) t
    Matrix.of (Seam.periodizeSeries D f) =
      (Matrix.diagonal (fun _ => 1-t*m) - walkMatrix D (fun j => weight a b c j+t*d j))⁻¹ := by
  let f := operatorCurve a b c (m • (1:Operator) + hopping d) t
  apply eq_inverse_of_lattice_equation D hzero hadd _ _ f
  intro z
  have h := congrArg (fun g : LatticeL1 => g z)
    (operatorCurve_equation a b c (m • (1:Operator) + hopping d) t ht)
  change f z - (walkOperator a b c f z+t*(m*f z+hopping d f z)) = impulse z at h
  rw [impulse_value,walkOperator_apply,hopping_value] at h
  simp only [step] at h
  simp only [add_mul,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum]
  linarith

theorem adapted_zero (L : ℕ) [NeZero L] (x : Seam.Site L) : Seam.adaptedDestination 0 x=x := by
  apply (DiagonalSeam.siteCoords_bijective L).1
  rw [DiagonalSeam.coords_adaptedDestination]
  simp [DiagonalSeam.coords]

theorem adapted_add (L : ℕ) [NeZero L] (z t : Site) (x : Seam.Site L) :
    Seam.adaptedDestination (z+t) x = Seam.adaptedDestination t (Seam.adaptedDestination z x) := by
  apply (DiagonalSeam.siteCoords_bijective L).1
  simp only [DiagonalSeam.coords_adaptedDestination,DiagonalSeam.coords_add,add_assoc]

theorem adaptedSeries_eq_inverse (L : ℕ) [NeZero L] {a b c M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : 0 < M)
    (hgap : 6*a+12*b+8*c < M) :
    Matrix.of (Seam.adaptedSeries L (coupling a b c M)) =
    (Matrix.diagonal (fun _ => M) - Matrix.of (DiagonalSeam.physicalWalk L a b c))⁻¹ :=
  periodize_coupling_eq_inverse _ (adapted_zero L) (adapted_add L) ha hb hc hM hgap

theorem ordinary_zero (L : ℕ) [NeZero L] (x : Seam.Cell L) : Seam.baseMove 0 x=x := by
  apply (CubicSeam.cubeCoords_bijective L).1
  rw [CubicSeam.cubeCoords_baseMove]
  have hc : CubicSeam.coords L 0 = 0 := by ext <;> simp [CubicSeam.coords]
  rw [hc, add_zero]

theorem ordinary_add (L : ℕ) [NeZero L] (z t : Site) (x : Seam.Cell L) :
    Seam.baseMove (z+t) x = Seam.baseMove t (Seam.baseMove z x) := by
  apply (CubicSeam.cubeCoords_bijective L).1
  have hc : CubicSeam.coords L (z+t) = CubicSeam.coords L z + CubicSeam.coords L t := by
    ext <;> simp [CubicSeam.coords]
  simp only [CubicSeam.cubeCoords_baseMove,hc,add_assoc]

theorem ordinarySeries_eq_inverse (L : ℕ) [NeZero L] {a b c M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : 0 < M)
    (hgap : 6*a+12*b+8*c < M) :
    Matrix.of (Seam.ordinarySeries L (coupling a b c M)) =
    (Matrix.diagonal (fun _ => M) - Matrix.of (CubicSeam.physicalWalk L a b c))⁻¹ :=
  periodize_coupling_eq_inverse _ (ordinary_zero L) (ordinary_add L) ha hb hc hM hgap

/-- At period one, all 26 displacements return to the same physical site. -/
theorem ordinary_period_one {a b c M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : 0 < M)
    (hgap : 6*a+12*b+8*c < M) (x y : Seam.Cell 1) :
    Seam.ordinarySeries 1 (coupling a b c M) x y = (M-(6*a+12*b+8*c))⁻¹ := by
  have hd (z : Site) : Seam.baseMove z x = y := Subsingleton.elim _ _
  simpa only [Seam.ordinarySeries,Seam.periodizeSeries,hd,if_true] using
    coupling_mass ha hb hc hM hgap

theorem adaptedCurve_eq_inverse (L : ℕ) [NeZero L] (a b c m t : ℝ) (d : Fin 7 → ℝ)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator) + hopping d)‖ < 1) :
    let f := operatorCurve a b c (m • (1:Operator) + hopping d) t
    Matrix.of (Seam.adaptedSeries L f) =
      (Matrix.diagonal (fun _ => 1-t*m) -
       walkMatrix Seam.adaptedDestination (fun j => weight a b c j+t*d j))⁻¹ :=
  periodize_operatorCurve_eq_inverse _ (adapted_zero L) (adapted_add L) a b c m t d ht

theorem ordinaryCurve_eq_inverse (L : ℕ) [NeZero L] (a b c m t : ℝ) (d : Fin 7 → ℝ)
    (ht : ‖walkOperator a b c + t • (m • (1:Operator) + hopping d)‖ < 1) :
    let f := operatorCurve a b c (m • (1:Operator) + hopping d) t
    Matrix.of (Seam.ordinarySeries L f) =
      (Matrix.diagonal (fun _ => 1-t*m) -
       walkMatrix Seam.baseMove (fun j => weight a b c j+t*d j))⁻¹ :=
  periodize_operatorCurve_eq_inverse _ (ordinary_zero L) (ordinary_add L) a b c m t d ht

#print axioms adaptedSeries_eq_inverse
#print axioms ordinarySeries_eq_inverse
#print axioms adaptedCurve_eq_inverse
#print axioms ordinaryCurve_eq_inverse
#print axioms walkMatrix_isHermitian
#print axioms eventually_admissible_weights

end IsingScaling.Rotor.PressureSelection.PeriodizedWalk
