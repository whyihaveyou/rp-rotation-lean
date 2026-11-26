import MathlibProbe.RotorPeriodicPairResponse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-! # Physical massive lattice walk for the rotor auxiliary interaction

Dᵢ is the sum of the translations by the two unit steps in direction i.
The seven nonempty coordinate subsets give three Dᵢ, three DᵢDⱼ and
D₀D₁D₂, with coefficients a, b and c respectively. Thus each permitted
lattice displacement occurs exactly once. The unnormalized total
one-step mass is 6a+12b+8c. After division by M it is less than one,
so all endpoint weights summed over walk lengths and sites are summable.
On the actual torus character, the adjoint of Dᵢ multiplies by twice
the real part of kᵢ. Fubini and the geometric series therefore compute
the Fourier transform of the same nonnegative summable coupling.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace IsingScaling.Rotor.PressureSelection.LatticeWalk

abbrev Profile := Site → ℝ

def unit (i : Fin 3) : Site := Pi.single i (1:ℤ)

def both (i : Fin 3) (f : Profile) (z : Site) : ℝ := f (z+unit i) + f (z-unit i)

def orbit : List (Fin 3) → Profile → Profile
  | [], f => f
  | i::l, f => both i (orbit l f)

def directions : Fin 7 → List (Fin 3) :=
  ![[0],[1],[2],[0,1],[0,2],[1,2],[0,1,2]]

def weight (a b c : ℝ) : Fin 7 → ℝ := ![a,a,a,b,b,b,c]

def step (a b c : ℝ) (f : Profile) (z : Site) : ℝ :=
  ∑ j, weight a b c j * orbit (directions j) f z

def multiplier (a b c : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ j, weight a b c j * ((directions j).map v).prod

theorem multiplier_eq (a b c : ℝ) (v : Fin 3 → ℝ) :
    multiplier a b c v = a*(v 0+v 1+v 2) +
       b*(v 0*v 1+v 0*v 2+v 1*v 2) + c*v 0*v 1*v 2 := by
  simp [multiplier, weight, directions, Fin.sum_univ_succ]
  ring

private theorem weight_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (j : Fin 7) : 0 ≤ weight a b c j := by
  fin_cases j <;> first | exact ha | exact hb | exact hc

theorem orbit_nonneg (l : List (Fin 3)) {f : Profile} (hf : ∀ z, 0 ≤ f z) :
    ∀ z, 0 ≤ orbit l f z := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact fun z => add_nonneg (ih _) (ih _)

theorem step_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {f : Profile} (hf : ∀ z, 0 ≤ f z) (z : Site) : 0 ≤ step a b c f z := by
  apply Finset.sum_nonneg
  exact fun j _ => mul_nonneg (weight_nonneg ha hb hc _) (orbit_nonneg _ hf _)

theorem orbit_summable (l : List (Fin 3)) {f : Profile} (hf : Summable f) :
    Summable (orbit l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
      have h₁ := (Equiv.addRight (unit i)).summable_iff.mpr ih
      have h₂ := (Equiv.addRight (-unit i)).summable_iff.mpr ih
      change Summable (fun z => orbit l f (z+unit i) + orbit l f (z-unit i))
      simpa only [Function.comp_def,Equiv.coe_addRight,sub_eq_add_neg] using h₁.add h₂

theorem step_summable (a b c : ℝ) {f : Profile} (hf : Summable f) :
    Summable (step a b c f) :=
  (hasSum_sum (s := Finset.univ) (fun j _ => ((orbit_summable (directions j) hf).hasSum.mul_left
    (weight a b c j)))).summable

def pairing (f h : Profile) : ℝ := ∑' z, f z*h z

private theorem summable_pair {f h : Profile} (hf : Summable f) (hh : ∀ z, |h z| ≤ 1) :
    Summable (fun z => f z*h z) := by
  apply hf.norm.of_norm_bounded
  intro z
  simp only [Real.norm_eq_abs,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hh z)

private theorem pairing_both {f h : Profile} (hf : Summable f) (hh : ∀ z, |h z| ≤ 1)
    (v : Fin 3 → ℝ) (he : ∀ i z, h (z+unit i) + h (z-unit i) = v i*h z)
    (i : Fin 3) : pairing (both i f) h = v i*pairing f h := by
  let e := unit i
  have h₁ := summable_pair hf (h := fun z => h (z-e)) (fun z => hh _)
  have h₂ := summable_pair hf (h := fun z => h (z+e)) (fun z => hh _)
  have ht₁ := (Equiv.addRight e).hasSum_iff.mpr h₁.hasSum
  have ht₂ := (Equiv.addRight (-e)).hasSum_iff.mpr h₂.hasSum
  have hg : HasSum (fun z => both i f z*h z)
      ((∑' z, f z * h (z-e)) + ∑' z, f z * h (z+e)) := by
    -- Keep the two translated sums distinct before taking their total.
    exact (ht₁.add ht₂).congr_fun (fun z => by
      simp [both,Equiv.coe_addRight,e,sub_eq_add_neg,add_mul])
  rw [pairing, hg.tsum_eq]
  rw [← h₁.tsum_add h₂,pairing, ← tsum_mul_left]
  apply tsum_congr
  intro z
  dsimp only [e]
  rw [← mul_add, add_comm (h (z-unit i)), he]
  ring

private theorem pairing_orbit {f h : Profile} (hf : Summable f) (hh : ∀ z, |h z| ≤ 1)
    (v : Fin 3 → ℝ) (he : ∀ i z, h (z+unit i) + h (z-unit i) = v i*h z)
    (l : List (Fin 3)) : pairing (orbit l f) h = (l.map v).prod * pairing f h := by
  induction l with
  | nil => simp [orbit]
  | cons i l ih =>
      rw [orbit, pairing_both (orbit_summable l hf) hh v he, ih]
      simp [mul_assoc]

private theorem pairing_step {f h : Profile} (hf : Summable f) (hh : ∀ z, |h z| ≤ 1)
    (v : Fin 3 → ℝ) (he : ∀ i z, h (z+unit i) + h (z-unit i) = v i*h z)
    (a b c : ℝ) : pairing (step a b c f) h = multiplier a b c v * pairing f h := by
  have hi (j : Fin 7) := ((summable_pair (orbit_summable (directions j) hf) hh).hasSum.mul_left
    (weight a b c j))
  have S := hasSum_sum (s := Finset.univ) (fun j _ => hi j)
  unfold pairing step
  simp_rw [Finset.sum_mul,mul_assoc]
  rw [S.tsum_eq]
  change (∑ j, weight a b c j * pairing (orbit (directions j) f) h) = _
  simp_rw [pairing_orbit hf hh v he]
  simp [multiplier, Finset.sum_mul, mul_assoc, pairing]

def delta (z : Site) : ℝ := if z = 0 then 1 else 0

private theorem delta_summable : Summable delta := by
  apply summable_of_ne_finset_zero (s := {0})
  intro z hz
  simpa [delta] using hz

private theorem pairing_delta (h : Profile) : pairing delta h = h 0 := by
  simp [pairing,delta,ite_mul]

/-- The endpoint weights after n actual unnormalized walk steps. -/
def walk (a b c : ℝ) : ℕ → Profile
  | 0 => delta
  | n+1 => step a b c (walk a b c n)

theorem walk_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (n : ℕ) (z : Site) : 0 ≤ walk a b c n z := by
  induction n generalizing z with
  | zero => by_cases h : z = 0 <;> simp [walk,delta,h]
  | succ n ih => exact step_nonneg ha hb hc ih z

theorem walk_summable (a b c : ℝ) (n : ℕ) : Summable (walk a b c n) := by
  induction n with
  | zero => exact delta_summable
  | succ n ih => exact step_summable a b c ih

private theorem pairing_walk (a b c : ℝ) (n : ℕ) (h : Profile) (hh : ∀ z, |h z| ≤ 1)
    (v : Fin 3 → ℝ) (he : ∀ i z, h (z+unit i) + h (z-unit i) = v i*h z)
    (h₀ : h 0 = 1) : pairing (walk a b c n) h = multiplier a b c v ^ n := by
  induction n with
  | zero => simp [walk, pairing_delta,h₀]
  | succ n ih => rw [walk,pairing_step (walk_summable ..) hh v he,ih,pow_succ']

theorem walk_mass (a b c : ℝ) (n : ℕ) :
    ∑' z, walk a b c n z = (6*a + 12*b + 8*c)^n := by
  have ht := pairing_walk a b c n (fun _ => 1) (by simp) (fun _ => 2)
    (fun _ _ => by norm_num) rfl
  have h : multiplier a b c (fun _ => 2) = 6*a+12*b+8*c := by rw [multiplier_eq]; ring
  simpa only [pairing,mul_one,h] using ht

private def phase (k : Momentum) (z : Site) : Circle := ∏ i, k i ^ z i

private theorem phase_add (k : Momentum) (x y : Site) :
    phase k (x+y) = phase k x * phase k y := by
  simp [phase,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]

private theorem phase_unit (k : Momentum) (i : Fin 3) : phase k (unit i) = k i := by
  classical
  simp [phase,unit,Pi.single_apply,apply_ite]

private theorem real_character_eigen (k : Momentum) (i : Fin 3) (z : Site) :
    realCharacter (z+unit i) k + realCharacter (z-unit i) k =
      (2*((k i : Circle):ℂ).re)*realCharacter z k := by
  have inv : phase k (-unit i) = (k i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← phase_unit k i,← phase_add, neg_add_cancel]
    simp [phase]
  change ((phase k (z+unit i):Circle):ℂ).re + ((phase k (z-unit i):Circle):ℂ).re = _
  rw [sub_eq_add_neg,phase_add,phase_add,phase_unit,inv]
  simp only [Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.mul_re,Complex.conj_re,Complex.conj_im]
  change _ = (2*((k i:Circle):ℂ).re)*((phase k z:Circle):ℂ).re
  ring

def fourierStep (a b c : ℝ) (k : Momentum) : ℝ :=
  multiplier a b c (fun i => 2*((k i : Circle):ℂ).re)

theorem fourierStep_eq (a b c : ℝ) (k : Momentum) :
    fourierStep a b c k =
      let u := ((k 0 : Circle):ℂ).re
      let v := ((k 1 : Circle):ℂ).re
      let w := ((k 2 : Circle):ℂ).re
      2*a*(u+v+w) + 4*b*(u*v+u*w+v*w) + 8*c*u*v*w := by
  rw [fourierStep,multiplier_eq]
  ring

theorem walk_fourier (a b c : ℝ) (n : ℕ) (k : Momentum) :
    pairing (walk a b c n) (fun z => realCharacter z k) = fourierStep a b c k ^ n :=
  pairing_walk a b c n _ (fun z => abs_realCharacter_le_one z k) _ (real_character_eigen k)
    (by simp [realCharacter])

private theorem normalized_all {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) :
    Summable (fun p : ℕ × Site => walk a b c p.1 p.2) := by
  apply (summable_prod_of_nonneg (fun p => walk_nonneg ha hb hc p.1 p.2)).2
  refine ⟨walk_summable a b c,?_⟩
  simpa only [walk_mass] using
    (summable_geometric_of_lt_one (by positivity : 0 ≤ 6*a+12*b+8*c) hgap)

private def kernel (a b c : ℝ) (z : Site) : ℝ := ∑' n, walk a b c n z

private theorem kernel_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (z : Site) :
    0 ≤ kernel a b c z := tsum_nonneg fun i => walk_nonneg ha hb hc i z

private theorem kernel_summable {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) : Summable (kernel a b c) :=
  (normalized_all ha hb hc hgap).prod_symm.prod

private theorem abs_fourierStep_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k : Momentum) : |fourierStep a b c k| ≤ 6*a+12*b+8*c := by
  have hs := summable_pair (walk_summable a b c 1) (fun z => abs_realCharacter_le_one z k)
  calc |fourierStep a b c k|
    = ‖∑' z, walk a b c 1 z * realCharacter z k‖ := by
        have h := walk_fourier a b c 1 k
        simpa only [pairing,pow_one,Real.norm_eq_abs,h] using congrArg abs h.symm
    _ ≤ ∑' z, ‖walk a b c 1 z * realCharacter z k‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' z, walk a b c 1 z := by
        apply hs.norm.tsum_le_tsum _ (walk_summable _ _ _ _)
        intro z
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (walk_nonneg ha hb hc _ _)]
        exact mul_le_of_le_one_right (walk_nonneg ha hb hc ..) (abs_realCharacter_le_one ..)
    _ = 6*a+12*b+8*c := by rw [walk_mass,pow_one]

private theorem kernel_fourier {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) (k : Momentum) :
    pairing (kernel a b c) (fun z => realCharacter z k) = (1-fourierStep a b c k)⁻¹ := by
  let H (n : ℕ) (z : Site) := walk a b c n z*realCharacter z k
  have hs := normalized_all ha hb hc hgap
  have hi : Summable (Function.uncurry H) := by
    apply hs.of_norm_bounded
    intro p
    change ‖walk a b c p.1 p.2 * realCharacter p.2 k‖ ≤ walk a b c p.1 p.2
    rw [Real.norm_eq_abs, abs_mul,abs_of_nonneg (walk_nonneg ha hb hc _ _)]
    exact mul_le_of_le_one_right (walk_nonneg ha hb hc ..) (abs_realCharacter_le_one ..)
  calc pairing (kernel a b c) (fun z => realCharacter z k)
    = ∑' z, ∑' n, H n z := by simp only [pairing,kernel,H,tsum_mul_right]
    _ = ∑' n, ∑' z, H n z := hi.tsum_comm
    _ = ∑' n, (fourierStep a b c k)^n := tsum_congr fun n => walk_fourier a b c n k
    _ = _ := tsum_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs]; exact (abs_fourierStep_le ha hb hc k).trans_lt hgap)

/-- All lengths and windings are retained. These are the weights on the
actual original integer lattice before periodizing either torus. -/
def coupling (a b c M : ℝ) (z : Site) : ℝ :=
  M⁻¹ * kernel (a/M) (b/M) (c/M) z

private theorem scaled_gap {a b c M : ℝ} (hM : 0 < M) (hgap : 6*a+12*b+8*c < M) :
    6*(a/M)+12*(b/M)+8*(c/M) < 1 := by
  calc 6*(a/M)+12*(b/M)+8*(c/M) = (6*a+12*b+8*c)/M := by ring
    _ < 1 := (div_lt_one hM).mpr hgap

theorem coupling_nonneg {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : 0 < M) (z : Site) : 0 ≤ coupling a b c M z :=
  mul_nonneg (inv_nonneg.mpr hM.le) (kernel_nonneg (div_nonneg ha hM.le)
    (div_nonneg hb hM.le) (div_nonneg hc hM.le) _)

theorem coupling_abs_summable {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : 0 < M) (hgap : 6*a+12*b+8*c < M) : Summable (fun z => |coupling a b c M z|) := by
  have hs := (kernel_summable (div_nonneg ha hM.le) (div_nonneg hb hM.le)
    (div_nonneg hc hM.le) (scaled_gap hM hgap)).mul_left M⁻¹
  simpa only [Real.norm_eq_abs,coupling] using hs.norm

private theorem fourierStep_scale (a b c M : ℝ) (k : Momentum) :
    fourierStep (a/M) (b/M) (c/M) k = fourierStep a b c k / M := by
  simp only [fourierStep_eq, div_eq_mul_inv]
  ring

/-- VM-1 at every physical momentum for the very same lattice coupling
admitted by the finite-pressure response theorem. -/
theorem interactionMultiplier_coupling {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : 0 < M) (hgap : 6*a+12*b+8*c < M) (k : Momentum) :
    interactionMultiplier (coupling a b c M) (coupling_abs_summable ha hb hc hM hgap) k =
      (M - fourierStep a b c k)⁻¹ := by
  change (∑' z, (M⁻¹ * kernel (a/M) (b/M) (c/M) z) * realCharacter z k) = _
  simp_rw [mul_assoc,tsum_mul_left]
  change M⁻¹ * pairing _ _ = _
  rw [kernel_fourier (div_nonneg ha hM.le) (div_nonneg hb hM.le) (div_nonneg hc hM.le)
    (scaled_gap hM hgap), fourierStep_scale]
  rw [← mul_inv_rev]
  congr 1
  field_simp

theorem coupling_mass {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : 0 < M) (hgap : 6*a+12*b+8*c < M) :
    (∑' z, coupling a b c M z) = (M-(6*a+12*b+8*c))⁻¹ := by
  have h := interactionMultiplier_coupling ha hb hc hM hgap (fun _ => 1)
  have hstep : fourierStep a b c (fun _ => 1) = 6*a+12*b+8*c := by
    rw [fourierStep_eq]
    norm_num <;> ring
  have hchar (z : Site) : realCharacter z (fun _ => 1) = 1 := by
    simp [realCharacter,Finset.prod_const_one]
  simpa only [interactionMultiplier,ContinuousMap.coe_mk,hchar,mul_one,hstep] using h

private theorem orbit_even (l : List (Fin 3)) {f : Profile} (hf : ∀ z, f (-z) = f z) :
    ∀ z, orbit l f (-z) = orbit l f z := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
      intro z
      have h₁ := ih (z-unit i)
      have h₂ := ih (z+unit i)
      simp only [orbit,both]
      convert add_comm (orbit l f (z-unit i)) (orbit l f (z+unit i)) using 1
      rw [←h₁,←h₂]
      abel_nf

private theorem walk_even (a b c : ℝ) (n : ℕ) : ∀ z, walk a b c n (-z) = walk a b c n z := by
  induction n with
  | zero => simp [walk,delta]
  | succ n ih =>
      intro z
      simp only [walk,step]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      exact orbit_even _ ih z

theorem coupling_even (a b c M : ℝ) (z : Site) :
    coupling a b c M (-z) = coupling a b c M z := by
  simp only [coupling,kernel,walk_even]

abbrev LatticeL1 := lp (fun _ : Site => ℝ) 1
abbrev Operator := LatticeL1 →L[ℝ] LatticeL1

private def shiftLM (u : Site) : LatticeL1 →ₗ[ℝ] LatticeL1 where
  toFun f := ⟨fun z => f (z+u), by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ENNReal).toReal)).2
    have h := (Equiv.addRight u).summable_iff.mpr (f.2.summable_of_one.norm)
    simpa [Equiv.coe_addRight, Function.comp_def] using h⟩
  map_add' f g := rfl
  map_smul' t f := rfl

private lemma shift_norm (u : Site) (f : LatticeL1) : ‖shiftLM u f‖ = ‖f‖ := by
  simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ENNReal).toReal),ENNReal.toReal_one,
    Real.rpow_one, div_one]
  exact (Equiv.addRight u).tsum_eq (fun z => ‖f z‖)

private def translation (u : Site) : Operator :=
  (shiftLM u).mkContinuous 1 fun f => by rw [shift_norm,one_mul]

private theorem translation_norm (u : Site) : ‖translation u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact (shift_norm u f).le.trans (by simp)

def orbitOperator : List (Fin 3) → Operator
  | [] => 1
  | i::l => (translation (unit i)+translation (-unit i)) * orbitOperator l

theorem orbitOperator_apply (l : List (Fin 3)) (f : LatticeL1) (z : Site) :
    orbitOperator l f z = orbit l f z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
      change orbitOperator l f (z+unit i)+orbitOperator l f (z+-unit i) =
        orbit l f (z+unit i)+orbit l f (z-unit i)
      simp only [ih,sub_eq_add_neg]

private theorem norm_orbitOperator (l : List (Fin 3)) :
    ‖orbitOperator l‖ ≤ (l.map (fun _ => (2:ℝ))).prod := by
  induction l with
  | nil =>
      change ‖(1:Operator)‖ ≤ 1
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by simp)
  | cons i l ih =>
      have h : ‖translation (unit i) + translation (-unit i)‖ ≤ 2 :=
        (norm_add_le ..).trans (by linarith [translation_norm (unit i), translation_norm (-unit i)])
      exact (norm_mul_le ..).trans (mul_le_mul h ih (norm_nonneg _) (by norm_num))

def walkOperator (a b c : ℝ) : Operator :=
  ∑ j, weight a b c j • orbitOperator (directions j)

theorem walkOperator_apply (a b c : ℝ) (f : LatticeL1) (z : Site) :
    walkOperator a b c f z = step a b c f z := by
  let E := lp.evalCLM ℝ (fun _ : Site => ℝ) 1 z
  change E ((∑ j,weight a b c j • orbitOperator (directions j)) f) = _
  rw [_root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change weight a b c j * orbitOperator (directions j) f z = _
  rw [orbitOperator_apply]

theorem norm_walkOperator {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ‖walkOperator a b c‖ ≤ 6*a+12*b+8*c := by
  have hw (j : Fin 7) : 0 ≤ weight a b c j := by
    fin_cases j <;> first | exact ha | exact hb | exact hc
  calc
    ‖walkOperator a b c‖ ≤ ∑ j, ‖weight a b c j • orbitOperator (directions j)‖ := norm_sum_le ..
    _ ≤ multiplier a b c (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (norm_orbitOperator _) (hw _)
    _ = _ := by rw [multiplier_eq]; ring

def impulse : LatticeL1 := lp.single 1 0 (1:ℝ)

private theorem impulse_apply (z : Site) : impulse z = delta z := by
  by_cases h : z = 0 <;> simp [impulse,delta,h]

private theorem op_pow_impulse (a b c : ℝ) (n : ℕ) (z : Site) :
    (walkOperator a b c ^ n) impulse z = walk a b c n z := by
  induction n generalizing z with
  | zero => simpa only [pow_zero,one_apply_eq_self,walk] using impulse_apply z
  | succ n ih =>
      rw [pow_succ',mul_apply_eq_comp,walkOperator_apply,walk]
      congr 1
      funext y
      exact ih y

/-- Real-space response curve in the Banach space of absolutely summable
displacements. All translation and hopping operators act on that space. -/
def operatorCurve (a b c : ℝ) (D : Operator) (t : ℝ) : LatticeL1 :=
  resolvent (walkOperator a b c+t • D) (1:ℝ) impulse

theorem operatorCurve_zero {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) (D : Operator) (z : Site) :
    operatorCurve a b c D 0 z = coupling a b c 1 z := by
  have hs := hasSum_geom_series_inverse (walkOperator a b c)
    ((norm_walkOperator ha hb hc).trans_lt hgap)
  have hv := (((lp.evalCLM ℝ (fun _ : Site => ℝ) 1 z).comp
    (ContinuousLinearMap.apply ℝ LatticeL1 impulse)).hasSum hs)
  change HasSum (fun n : ℕ => (walkOperator a b c ^ n) impulse z)
    ((Ring.inverse (1-walkOperator a b c)) impulse z) at hv
  simp only [op_pow_impulse] at hv
  change _ = (1:ℝ)⁻¹ * ∑' n, walk (a/1) (b/1) (c/1) n z
  simpa only [operatorCurve,div_one,inv_one,one_mul,zero_smul,add_zero,resolvent,map_one] using hv.tsum_eq.symm

theorem hasDerivAt_operatorCurve {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) (D : Operator) :
    HasDerivAt (operatorCurve a b c D)
      ((resolvent (walkOperator a b c) (1:ℝ))
       (D ((resolvent (walkOperator a b c) (1:ℝ)) impulse))) 0 := by
  let A := walkOperator a b c
  have hunit : (1:ℝ) ∈ resolventSet ℝ A := by
    change IsUnit (algebraMap ℝ Operator 1-A)
    rw [map_one]
    exact isUnit_one_sub_of_norm_lt_one ((norm_walkOperator ha hb hc).trans_lt hgap)
  have hd : HasDerivAt (fun t : ℝ => A+t • D) D 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const D).const_add A
  have hr := (spectrum.hasFDerivAt_resolvent (𝕜 := ℝ) hunit).comp_hasDerivAt_of_eq 0 hd (by simp)
  have hv := (ContinuousLinearMap.apply ℝ LatticeL1 impulse).hasFDerivAt.comp_hasDerivAt 0 hr
  exact hv

theorem l1_abs_summable (f : LatticeL1) : Summable (fun z => |f z|) := by
  simpa only [Real.norm_eq_abs] using f.2.summable_of_one.norm

/-- The perturbed displacement solves the resolvent equation on the actual
lattice in the open operator norm gap, including nonzero perturbations. -/
theorem operatorCurve_equation (a b c : ℝ) (D : Operator) (t : ℝ)
    (ht : ‖walkOperator a b c + t • D‖ < 1) :
    let f := operatorCurve a b c D t
    f - (walkOperator a b c + t • D) f = impulse := by
  let A := walkOperator a b c + t • D
  have h := Ring.mul_inverse_cancel (1-A) (isUnit_one_sub_of_norm_lt_one ht)
  have he := congrArg (fun B : Operator => B impulse) h
  simpa only [operatorCurve,A,resolvent,map_one,mul_apply_eq_comp,
    ContinuousLinearMap.sub_apply,one_apply_eq_self] using he

private theorem pairing_resolvent {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) (f : LatticeL1) (k : Momentum) :
    pairing ((resolvent (walkOperator a b c) (1:ℝ)) f) (fun z => realCharacter z k) =
      (1-fourierStep a b c k)⁻¹ * pairing f (fun z => realCharacter z k) := by
  let A := walkOperator a b c
  let g : LatticeL1 := (resolvent A (1:ℝ)) f
  have hg1 := g.2.summable_of_one
  have hn := (norm_walkOperator ha hb hc).trans_lt hgap
  have hu := Ring.mul_inverse_cancel (1-A) (isUnit_one_sub_of_norm_lt_one hn)
  have hfg : g-A g = f := by
    have hu' := congrArg (fun B : Operator => B f) hu
    simpa only [g,resolvent,map_one,mul_apply_eq_comp,ContinuousLinearMap.sub_apply,
      one_apply_eq_self] using hu'
  let ψ (z : Site) := realCharacter z k
  have hbnd (z : Site) : |ψ z| ≤ 1 := abs_realCharacter_le_one z k
  have hpair : pairing g ψ - pairing (step a b c g) ψ = pairing f ψ := by
    unfold pairing
    rw [← (summable_pair hg1 hbnd).tsum_sub (summable_pair (step_summable a b c hg1) hbnd)]
    apply tsum_congr
    intro z
    rw [← sub_mul]
    congr 1
    simpa only [A,lp.coeFn_sub,Pi.sub_apply,walkOperator_apply] using
      (congrArg (fun v : LatticeL1 => v z) hfg)
  rw [pairing_step hg1 hbnd _ (real_character_eigen k) a b c] at hpair
  change pairing g ψ - fourierStep a b c k * pairing g ψ = pairing f ψ at hpair
  have hk : 1-fourierStep a b c k ≠ 0 :=
    sub_ne_zero.mpr (lt_of_le_of_lt (le_abs_self _) ((abs_fourierStep_le ha hb hc _).trans_lt hgap)).ne'
  change pairing g ψ = (1-fourierStep a b c k)⁻¹ * pairing f ψ
  field_simp
  linarith

/-- The three differentiated walk families correspond to l=[], [2] and
[0,1]. Factors two and four are retained in the actual Fourier derivative.
The derivative is taken in the norm of absolutely summable displacements. -/
theorem physical_orbit_variation {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hgap : 6*a+12*b+8*c < 1) (l : List (Fin 3)) :
    ∃ H : LatticeL1, HasDerivAt (operatorCurve a b c (orbitOperator l)) H 0 ∧
      ∀ k : Momentum, interactionMultiplier H (l1_abs_summable H) k =
        (l.map (fun i => 2*((k i : Circle):ℂ).re)).prod * ((1-fourierStep a b c k)⁻¹)^2 := by
  let R := resolvent (walkOperator a b c) (1:ℝ)
  refine ⟨R (orbitOperator l (R impulse)), hasDerivAt_operatorCurve ha hb hc hgap _, fun k => ?_⟩
  change pairing _ _ = _
  rw [pairing_resolvent ha hb hc hgap]
  have ho : ⇑((orbitOperator l) (R impulse)) = orbit l (R impulse) :=
    funext (orbitOperator_apply l (R impulse))
  rw [ho,pairing_orbit (R impulse).2.summable_of_one (fun z => abs_realCharacter_le_one z k) _
    (real_character_eigen k)]
  change _ * (_ * pairing ((resolvent (walkOperator a b c) (1:ℝ)) impulse)
    (fun z => realCharacter z k)) = _
  rw [pairing_resolvent ha hb hc hgap]
  have hi : pairing impulse (fun z => realCharacter z k) = 1 := by
    have hh : ⇑impulse = delta := funext impulse_apply
    rw [hh,pairing_delta]
    simp [realCharacter]
  rw [hi]
  ring

def hopping (v : Fin 7 → ℝ) : Operator :=
  ∑ j, v j • orbitOperator (directions j)

private lemma hopping_apply (v : Fin 7 → ℝ) (f : LatticeL1) (z : Site) :
    hopping v f z = ∑ j, v j * orbit (directions j) f z := by
  let E := lp.evalCLM ℝ (fun _ : Site => ℝ) 1 z
  change E ((∑ j, v j • orbitOperator (directions j)) f) = _
  rw [_root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change v j * orbitOperator (directions j) f z = _
  rw [orbitOperator_apply]

private lemma hopping_nonneg (v : Fin 7 → ℝ) (hv : ∀ j, 0 ≤ v j) :
    ∀ f : LatticeL1, (∀ z, 0 ≤ f z) → ∀ z, 0 ≤ hopping v f z := by
  intro f hf z
  rw [hopping_apply]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hv j) (orbit_nonneg _ hf _)

private lemma hopping_affine (v d : Fin 7 → ℝ) (t : ℝ) :
    hopping (fun j => v j+t*d j) = hopping v + t • hopping d := by
  simp only [hopping,add_smul,Finset.sum_add_distrib,mul_smul,Finset.smul_sum]

private lemma invOp_nonneg (B : Operator) (hb : ‖B‖ < 1)
    (hpos : ∀ f : LatticeL1, (∀ z, 0 ≤ f z) → ∀ z, 0 ≤ B f z) (z : Site) :
    0 ≤ (resolvent B (1:ℝ)) impulse z := by
  have hp (n : ℕ) : ∀ y, 0 ≤ (B^n) impulse y := by
    induction n with
    | zero =>
        intro y
        change 0 ≤ (lp.single (E := fun _ : Site => ℝ) 1 0 1 : LatticeL1) y
        by_cases h : y = 0 <;> simp [lp.single_apply,h]
    | succ n ih => simpa only [pow_succ',mul_apply_eq_comp] using hpos _ ih
  have hv := (((lp.evalCLM ℝ (fun _ : Site => ℝ) 1 z).comp
    (ContinuousLinearMap.apply ℝ LatticeL1 impulse)).hasSum
      (hasSum_geom_series_inverse B hb))
  change HasSum (fun n : ℕ => (B ^ n) impulse z) ((Ring.inverse (1-B)) impulse z) at hv
  simpa only [resolvent,map_one,← hv.tsum_eq] using tsum_nonneg fun n => hp n z

private lemma normalized_equation (B : Operator) (r : ℝ) (hr : 0 < r)
    (hgap : ‖r⁻¹ • B‖ < 1) :
    let f := r⁻¹ • (resolvent (r⁻¹ • B) (1:ℝ)) impulse
    r • f - B f = impulse := by
  let G := resolvent (r⁻¹ • B) (1:ℝ)
  have hx := congrArg (fun T : Operator => T impulse)
    (Ring.mul_inverse_cancel (1-r⁻¹ • B) (isUnit_one_sub_of_norm_lt_one hgap))
  have hg : G impulse - r⁻¹ • B (G impulse) = impulse := by
    simpa only [G,resolvent,map_one,mul_apply_eq_comp, sub_apply, one_apply_eq_self,
      ContinuousLinearMap.smul_apply] using hx
  change r • (r⁻¹ • G impulse) - B (r⁻¹ • G impulse) = impulse
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, map_smul] using hg

/-- For a small affine change of all seven hopping weights and the mass,
the operator curve at both signs has the nonnegative physical walk law. -/
theorem affine_curve_nonneg {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgap : 6*a+12*b+8*c < 1) (m : ℝ) (dw : Fin 7 → ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ z, 0 ≤ operatorCurve a b c (m • (1:Operator) + hopping dw) t z := by
  let A := walkOperator a b c
  let H := hopping dw
  let D := m • (1:Operator) + H
  let r (t : ℝ) := 1-t*m
  let B (t : ℝ) := A + t • H
  have hn : ‖A‖ < 1 := (norm_walkOperator ha.le hb.le hc.le).trans_lt hgap
  have occ : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, 0 ≤ weight a b c j+t*dw j := by
    rw [Filter.eventually_all]
    intro j
    have h0 : 0 < weight a b c j := by fin_cases j <;> first | exact ha | exact hb | exact hc
    have ho : IsOpen {t : ℝ | 0 < weight a b c j+t*dw j} := isOpen_lt continuous_const (by fun_prop)
    have hmem : ∀ᶠ t in 𝓝 (0:ℝ), 0 < weight a b c j+t*dw j :=
      ho.mem_nhds (by simpa using h0)
    exact hmem.mono fun _ h => le_of_lt h
  have hR : ∀ᶠ t in 𝓝 (0:ℝ), 0 < r t :=
    (isOpen_lt continuous_const (show Continuous r by dsimp [r]; fun_prop)).mem_nhds (by simp [r])
  have hOP : ∀ᶠ t in 𝓝 (0:ℝ), ‖A+t • D‖ < 1 :=
    (isOpen_lt (show Continuous (fun t : ℝ => ‖A+t • D‖) by fun_prop) continuous_const).mem_nhds
      (by simpa using hn)
  have hB : Continuous B := by dsimp only [B]; fun_prop
  have hC : ContinuousAt (fun t : ℝ => (r t)⁻¹ • B t) 0 := by
    have hr : Continuous r := by dsimp only [r]; fun_prop
    change ContinuousAt (r⁻¹ • B) 0
    exact (hr.continuousAt.inv₀ (by simp [r])).smul hB.continuousAt
  have hgB : ∀ᶠ t in 𝓝 (0:ℝ), ‖(r t)⁻¹ • B t‖ < 1 :=
    hC.norm (isOpen_Iio.mem_nhds (by simpa [r,B] using hn))
  filter_upwards [hR, hOP, hgB, occ] with t ht hnorm hq hweights
  let v := (r t)⁻¹ • (resolvent ((r t)⁻¹ • B t) (1:ℝ)) impulse
  have hv := normalized_equation (B t) (r t) ht hq
  change r t • v - B t v = impulse at hv
  let Q := 1 - (A + t • D)
  have hunit : IsUnit Q := isUnit_one_sub_of_norm_lt_one hnorm
  have hQ : Q v = impulse := by
    have hh : r t • v = v - (t*m) • v := by
      dsimp only [r]
      rw [sub_smul,one_smul]
    rw [hh] at hv
    change v - (A v + t • (m • v + H v)) = _
    change v - (t*m) • v - (A v + t • H v) = _ at hv
    rw [←hv,smul_add,smul_smul]
    abel
  have hi := congrArg (fun T : Operator => T v) (Ring.inverse_mul_cancel Q hunit)
  have he : operatorCurve a b c D t = v := by
    change (Ring.inverse (algebraMap ℝ Operator 1 - (A+t • D))) impulse = v
    rw [map_one,← hQ]
    exact hi
  intro z
  rw [show m • (1:Operator) + hopping dw = D by rfl,he]
  change 0 ≤ (r t)⁻¹ * (resolvent ((r t)⁻¹ • B t) (1:ℝ)) impulse z
  apply mul_nonneg (inv_nonneg.mpr ht.le)
  apply invOp_nonneg _ hq
  intro f hf y
  change 0 ≤ (r t)⁻¹ * B t f y
  apply mul_nonneg (inv_nonneg.mpr ht.le)
  have hB' : B t = hopping (fun j => weight a b c j + t*dw j) :=
    (hopping_affine (weight a b c) dw t).symm
  rw [hB']
  exact hopping_nonneg _ hweights f hf y

#print axioms affine_curve_nonneg
#print axioms physical_orbit_variation
#print axioms interactionMultiplier_coupling
#print axioms hasDerivAt_operatorCurve
#print axioms coupling_abs_summable

end IsingScaling.Rotor.PressureSelection.LatticeWalk
