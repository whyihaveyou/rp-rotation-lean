import MathlibProbe.RotorLocalGibbsLimit

/-! # Single-site oscillations for the nearest-neighbour sphere Gibbs update

Replacing the spin at a site removes its previous value. Changing one
neighbour changes one term of the conditional energy by at most `2 * β`.
Comparison of the partition functions gives a ratio at most `exp (4 * β)`
of the normalized densities against the same sphere prior. Centering the
test at a fixed replacement spin bounds the effect by its oscillation in
the updated coordinate.
-/

noncomputable section
open MeasureTheory
open scoped Classical InnerProductSpace Topology
namespace IsingScaling.Rotor.PressureSelection.Dobrushin
open LocalGibbs

def AgreeOff {N : ℕ} (j : Site) (s t : SpinField N) : Prop :=
  ∀ x, x ≠ j → s x = t x

def OscBound {N : ℕ} (F : C(SpinField N, ℝ)) (j : Site) (a : ℝ) : Prop :=
  ∀ s t, AgreeOff j s t → |F s - F t| ≤ a

def energy (N : ℕ) (β : ℝ) (i : Site) : C(SpinField N, ℝ) :=
  windowEnergy N {i} (nearestCoupling β) (summable_abs_nearest β)

def update {N : ℕ} [NeZero N] (β : ℝ) (i : Site) (F : C(SpinField N, ℝ)) : C(SpinField N, ℝ) :=
  readout {i} (energy N β i) F

private theorem intCont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : ProbabilityMeasure X) {f : X → ℝ} (hf : Continuous f) :
    Integrable f (P : Measure X) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem energy_eq {N : ℕ} (β : ℝ) (i : Site) (s : SpinField N) :
    energy N β i s = ∑ z ∈ nearestSteps, β * ⟪(s i).val, (s (i + z)).val⟫_ℝ := by
  let H (x z : Site) := nearestCoupling β z * ((if x + z ∈ ({i} : Finset Site)
    then (1 : ℝ) / 2 else 1) * ⟪(s x).val, (s (x+z)).val⟫_ℝ)
  change (∑ x : ↥({i} : Finset Site), ∑' z, H x.val z) = _
  rw [Finset.sum_coe_sort {i} (fun x => ∑' z, H x z), Finset.sum_singleton]
  rw [tsum_eq_sum (s := nearestSteps) (fun z hz => by simp [H, nearestCoupling, hz])]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hne : z ≠ 0 := by
    rintro rfl
    simpa [latticeDistance] using (mem_nearestSteps_iff_latticeDistance 0).mp hz
  simp [H, nearestCoupling, hz, hne]

private theorem abs_dot {N : ℕ} (u v : Spin N) : |⟪u.val, v.val⟫_ℝ| ≤ 1 := by
  simpa only [mem_sphere_zero_iff_norm.mp u.property, mem_sphere_zero_iff_norm.mp v.property,
    one_mul] using abs_real_inner_le_norm u.val v.val

private theorem change_energy {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {i j : Site}
    {s t : SpinField N} (h : AgreeOff j s t) (hi : s i = t i) :
    |energy N β i s - energy N β i t| ≤ if j-i ∈ nearestSteps then 2*β else 0 := by
  simp only [energy_eq, ← Finset.sum_sub_distrib, hi]
  let H (z : Site) := β * ⟪(t i).val, (s (i+z)).val⟫_ℝ -
    β * ⟪(t i).val, (t (i+z)).val⟫_ℝ
  have zero (z : Site) (hz : z ≠ j-i) : H z = 0 := by
    have hn : i+z ≠ j := by
      intro he
      exact hz (by rw [← he]; abel)
    simp [H, h _ hn]
  change |∑ z ∈ nearestSteps, H z| ≤ _
  by_cases hj : j-i ∈ nearestSteps
  · rw [ite_eq_left hj, Finset.sum_eq_single_of_mem (j-i) hj (fun z _ hz => zero z hz)]
    change |β * _ - β * _| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg hβ]
    have H₁ := abs_dot (t i) (s (i+(j-i)))
    have H₂ := abs_dot (t i) (t (i+(j-i)))
    have hsum := (abs_sub _ _).trans (add_le_add H₁ H₂)
    linarith [mul_le_mul_of_nonneg_left hsum hβ]
  · rw [ite_eq_right hj, Finset.sum_eq_zero (fun z hz => zero z (fun he => hj (he ▸ hz))), abs_zero]

private def inserted {N : ℕ} (i : Site) (s : SpinField N) (F : C(SpinField N, ℝ)) :
    C(WindowSpin N {i}, ℝ) :=
  ⟨fun a => F (replace {i} s a),
    F.continuous.comp ((replace_continuous {i}).comp (continuous_const.prodMk continuous_id))⟩

private theorem replace_agreeOff {N : ℕ} {i j : Site} {s t : SpinField N}
    (h : AgreeOff j s t) (a : WindowSpin N {i}) :
    AgreeOff j (replace {i} s a) (replace {i} t a) := by
  intro x hx
  by_cases he : x ∈ ({i} : Finset Site)
  · rw [replace_inside _ _ _ he, replace_inside _ _ _ he]
  · rw [replace_outside _ _ _ he, replace_outside _ _ _ he, h _ hx]

private theorem inserted_energy_bound {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {i j : Site}
    {s t : SpinField N} (h : AgreeOff j s t) (a : WindowSpin N {i}) :
    |inserted i s (energy N β i) a - inserted i t (energy N β i) a| ≤
      if j-i ∈ nearestSteps then 2*β else 0 := by
  change |energy N β i (replace {i} s a) - energy N β i (replace {i} t a)| ≤ _
  apply change_energy (i := i) hβ (replace_agreeOff h a)
  rw [replace_inside _ _ _ (Finset.mem_singleton_self i), replace_inside _ _ _ (Finset.mem_singleton_self i)]

private def partition {N : ℕ} [NeZero N] (β : ℝ) (i : Site) (s : SpinField N) : ℝ :=
  ∫ a, Real.exp (inserted i s (energy N β i) a) ∂(windowPrior N {i} : Measure _)

private theorem partition_pos {N : ℕ} [NeZero N] (β : ℝ) (i : Site) (s : SpinField N) :
    0 < partition β i s :=
  integral_exp_pos (intCont (windowPrior N {i}) (inserted i s (energy N β i)).continuous.rexp)

/-- Density of the actual single-site spin replacement against its product
of one normalized sphere measure. -/
def density {N : ℕ} [NeZero N] (β : ℝ) (i : Site) (s : SpinField N) : C(WindowSpin N {i}, ℝ) :=
  ⟨fun a => Real.exp (inserted i s (energy N β i) a) / partition β i s,
    (inserted i s (energy N β i)).continuous.rexp.div_const _⟩

private theorem density_nonneg {N : ℕ} [NeZero N] (β : ℝ) (i : Site)
    (s : SpinField N) (a : WindowSpin N {i}) : 0 ≤ density β i s a :=
  (div_pos (Real.exp_pos _) (partition_pos β i s)).le

private theorem density_mass {N : ℕ} [NeZero N] (β : ℝ) (i : Site) (s : SpinField N) :
    (∫ a, density β i s a ∂(windowPrior N {i} : Measure _)) = 1 := by
  change (∫ a, Real.exp (inserted i s (energy N β i) a) / partition β i s
    ∂(windowPrior N {i} : Measure (WindowSpin N {i}))) = 1
  rw [integral_div]
  exact div_self (partition_pos β i s).ne'

private theorem update_eq_integral {N : ℕ} [NeZero N] (β : ℝ) (i : Site)
    (F : C(SpinField N, ℝ)) (s : SpinField N) :
    update β i F s = ∫ a, density β i s a * inserted i s F a ∂(windowPrior N {i} : Measure _) := by
  change (∫ t, F t ∂(resample {i} (energy N β i) s : Measure _)) = _
  rw [resample_integral]
  change (∫ a, Real.exp (inserted i s (energy N β i) a) * inserted i s F a
    ∂(windowPrior N {i} : Measure _)) / partition β i s = _
  simp only [density, ContinuousMap.coe_mk, div_mul_eq_mul_div, integral_div]

theorem density_cap {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β) {i j : Site} {s t : SpinField N}
    (h : AgreeOff j s t) (a : WindowSpin N {i}) :
    density β i s a ≤ (if j-i ∈ nearestSteps then Real.exp (4*β) else 1) * density β i t a := by
  let D := if j-i ∈ nearestSteps then 2*β else 0
  let E (u : SpinField N) := inserted i u (energy N β i)
  have H (b : WindowSpin N {i}) : |E s b - E t b| ≤ D := inserted_energy_bound hβ h b
  have cap : Real.exp (E s a) / partition β i s ≤
      Real.exp (2*D) * (Real.exp (E t a) / partition β i t) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (partition_pos β i s) (partition_pos β i t)]
    change Real.exp (E s a) * (∫ b, Real.exp (E t b) ∂(windowPrior N {i} : Measure _)) ≤
      (Real.exp (2*D) * Real.exp (E t a)) * ∫ b, Real.exp (E s b) ∂(windowPrior N {i} : Measure _)
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono (intCont _ (continuous_const.mul (E t).continuous.rexp))
      (intCont _ (continuous_const.mul (E s).continuous.rexp))
    intro b
    change Real.exp (E s a) * Real.exp (E t b) ≤ (Real.exp (2*D) * Real.exp (E t a)) * Real.exp (E s b)
    simp only [← Real.exp_add, Real.exp_le_exp]
    linarith [(abs_le.mp (H a)).2, (abs_le.mp (H b)).1]
  change Real.exp (E s a) / partition β i s ≤ _ * (Real.exp (E t a) / partition β i t)
  split_ifs with hn
  · simpa [D, hn, show 2 * (2*β) = 4*β by ring] using cap
  · simpa [D, hn] using cap

private theorem change_reading {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (θ : ProbabilityMeasure X) (w v f g : C(X, ℝ))
    (hw : ∀ a, 0 ≤ w a) (hv : ∀ a, 0 ≤ v a)
    (hmw : (∫ a, w a ∂(θ : Measure X)) = 1) (hmv : (∫ a, v a ∂(θ : Measure X)) = 1)
    {d A B : ℝ} (hd : 0 ≤ d) (hden : ∀ a, |w a - v a| ≤ d * v a)
    (hfg : ∀ a, |f a - g a| ≤ A) (hg : ∀ a b, |g a - g b| ≤ B) (b : X) :
    |(∫ a, w a * f a ∂(θ : Measure X)) - ∫ a, v a * g a ∂(θ : Measure X)| ≤ A + d*B := by
  let H (a : X) := w a * (f a - g a) + (w a - v a) * (g a - g b)
  have hH : Continuous H := (w.continuous.mul (f.continuous.sub g.continuous)).add
    ((w.continuous.sub v.continuous).mul (g.continuous.sub continuous_const))
  have hconst : (∫ a, (w a - v a) * g b ∂(θ : Measure X)) = 0 := by
    rw [integral_mul_const, integral_sub (intCont θ w.continuous) (intCont θ v.continuous),
      hmw, hmv, sub_self, zero_mul]
  have hdiff : (∫ a, w a*f a ∂(θ : Measure X)) - (∫ a, v a*g a ∂(θ : Measure X)) =
      ∫ a, H a ∂(θ : Measure X) := by
    rw [← integral_sub (f := fun a => w a * f a) (g := fun a => v a * g a)
      (intCont θ (w.continuous.mul f.continuous)) (intCont θ (v.continuous.mul g.continuous))]
    calc
      _ = ∫ a, H a + (w a - v a)*g b ∂(θ : Measure X) := by
        apply integral_congr_ae
        filter_upwards with a
        dsimp [H]
        ring
      _ = _ := by rw [integral_add (f := H) (g := fun a => (w a - v a) * g b) (intCont θ hH)
        (intCont θ ((w.continuous.sub v.continuous).mul continuous_const)), hconst, add_zero]
  have hp (a : X) : |H a| ≤ w a * A + d*v a*B := by
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_of_nonneg (hw a)]
    exact add_le_add (mul_le_mul_of_nonneg_left (hfg a) (hw a))
      (mul_le_mul (hden a) (hg a b) (abs_nonneg _) (mul_nonneg hd (hv a)))
  rw [hdiff]
  calc
    _ ≤ ∫ a, |H a| ∂(θ : Measure X) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := H) (μ := (θ : Measure X))
    _ ≤ ∫ a, w a*A + d*v a*B ∂(θ : Measure X) :=
      integral_mono (intCont θ hH.abs) (intCont θ ((w.continuous.mul continuous_const).add
        ((continuous_const.mul v.continuous).mul continuous_const))) hp
    _ = _ := by
      rw [integral_add (f := fun a => w a * A) (g := fun a => d * v a * B)
        (intCont θ (w.continuous.mul continuous_const))
        (intCont θ ((continuous_const.mul v.continuous).mul continuous_const)),
        integral_mul_const, integral_mul_const, integral_const_mul, hmw, hmv]
      ring

/-- The old spin at the updated site disappears from its conditional law. -/
theorem update_self {N : ℕ} [NeZero N] (β : ℝ) (i : Site) (F : C(SpinField N, ℝ)) :
    OscBound (update β i F) i 0 := by
  intro s t h
  have H := resample_eq_of_outside {i} (energy N β i) (fun x hx => h x (by simpa using hx))
  change |(∫ a, F a ∂(resample {i} (energy N β i) s : Measure _)) -
    ∫ a, F a ∂(resample {i} (energy N β i) t : Measure _)| ≤ 0
  rw [H, sub_self, abs_zero]

/-- Resampling increases oscillation at a neighbouring site by at most
`(exp (4β) - 1) * ai`, where `ai` bounds variation in the updated spin.
The direct test variation at the boundary site remains `aj`. -/
theorem update_other {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β) {i j : Site} (_hij : j ≠ i)
    {F : C(SpinField N, ℝ)} {ai aj : ℝ} (hi : OscBound F i ai) (hj : OscBound F j aj) :
    OscBound (update β i F) j (aj + if j-i ∈ nearestSteps then (Real.exp (4*β) - 1)*ai else 0) := by
  intro s t h
  let c := if j-i ∈ nearestSteps then Real.exp (4*β) else 1
  have hc : 0 ≤ c-1 := by
    dsimp [c]
    split
    · exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
    · simp
  have hts : AgreeOff j t s := fun x hx => (h x hx).symm
  have hden (a : WindowSpin N {i}) : |density β i s a - density β i t a| ≤
      (c-1)*density β i t a := by
    have hs : density β i s a ≤ c * density β i t a := density_cap hβ h a
    have ht : density β i t a ≤ c * density β i s a := density_cap hβ hts a
    apply abs_sub_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    by_cases hh : density β i s a ≤ density β i t a
    · linarith [mul_le_mul_of_nonneg_left hh hc]
    · exact (sub_nonpos.mpr (le_of_not_ge hh)).trans (mul_nonneg hc (density_nonneg β i t a))
  have direct (a : WindowSpin N {i}) : |inserted i s F a - inserted i t F a| ≤ aj :=
    hj _ _ (replace_agreeOff h a)
  have rangeBound (a b : WindowSpin N {i}) : |inserted i t F a - inserted i t F b| ≤ ai := by
    apply hi
    intro x hx
    have he : x ∉ ({i} : Finset Site) := by simpa using hx
    rw [replace_outside _ _ _ he, replace_outside _ _ _ he]
  have H := change_reading (windowPrior N {i}) (density β i s) (density β i t)
    (inserted i s F) (inserted i t F) (density_nonneg β i s) (density_nonneg β i t)
    (density_mass β i s) (density_mass β i t) hc hden direct rangeBound (({i} : Finset Site).restrict t)
  rw [update_eq_integral, update_eq_integral]
  by_cases he : j-i ∈ nearestSteps <;> simpa [c, he] using H

/-- Normalization drops out of the likelihood cross product. The exponent
uses the changes of the site energy at two possible replacement spins. -/
theorem density_cross_ratio {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β) {i j : Site}
    {s t : SpinField N} (h : AgreeOff j s t) (a b : WindowSpin N {i}) :
    density β i s a * density β i t b ≤
      Real.exp (2*β)^2 * (density β i t a * density β i s b) := by
  let E (u : SpinField N) := inserted i u (energy N β i)
  have bound (c : WindowSpin N {i}) : |E s c - E t c| ≤ 2*β := by
    apply (inserted_energy_bound hβ h c).trans
    split
    · exact le_rfl
    · exact mul_nonneg (by norm_num) hβ
  change Real.exp (E s a) / partition β i s * (Real.exp (E t b) / partition β i t) ≤
    Real.exp (2*β)^2 * (Real.exp (E t a) / partition β i t * (Real.exp (E s b) / partition β i s))
  rw [div_mul_div_comm, div_mul_div_comm, mul_comm (partition β i t) _,
    ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (partition_pos β i s).le (partition_pos β i t).le)
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [(abs_le.mp (bound a)).2, (abs_le.mp (bound b)).1]

private theorem gap_of_odds {p q B r : ℝ} (h0p : 0 ≤ p) (hp : p ≤ B)
    (h0q : 0 ≤ q) (hq : q ≤ B) (hr : 1 ≤ r)
    (hodds : p*(B-q) ≤ r^2 * (q*(B-p))) :
    p-q ≤ (r-1)/(r+1)*B := by
  have hc : 0 ≤ r^2-1 := by nlinarith [sq_nonneg (r-1)]
  have hmid : 4*q*(B-p) ≤ (B-(p-q))^2 := by nlinarith [sq_nonneg (q-(B-p))]
  have hs : (B+(p-q))^2 ≤ (r*(B-(p-q)))^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hmid hc, hodds]
  have hlinear : B+(p-q) ≤ r*(B-(p-q)) := by
    have hn : 0 ≤ r*(B-(p-q)) := mul_nonneg (by linarith) (by linarith)
    exact (sq_le_sq₀ (by linarith) hn).mp hs
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < r+1)]
  nlinarith [hlinear]

private theorem mean_product_cross {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (θ : ProbabilityMeasure X) (w v f g : C(X, ℝ))
    {c : ℝ} (hcross : ∀ x y, w x * v y ≤ c * (v x * w y))
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∫ x, w x * f x ∂(θ : Measure X)) * (∫ x, v x * g x ∂(θ : Measure X)) ≤
      c * ((∫ x, v x * f x ∂(θ : Measure X)) * ∫ x, w x * g x ∂(θ : Measure X)) := by
  let V := ∫ x, v x*g x ∂(θ : Measure X)
  let W := ∫ x, w x*g x ∂(θ : Measure X)
  have inner (x : X) : w x * f x * V ≤ c * (v x * f x) * W := by
    dsimp [V,W]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono (intCont θ (continuous_const.mul (v.continuous.mul g.continuous)))
      (intCont θ (continuous_const.mul (w.continuous.mul g.continuous)))
    intro y
    change w x * f x * (v y*g y) ≤ c*(v x*f x)*(w y*g y)
    calc w x * f x * (v y * g y) = (w x * v y) * (f x*g y) := by ring
       _ ≤ (c*(v x*w y))*(f x*g y) :=
         mul_le_mul_of_nonneg_right (hcross x y) (mul_nonneg (hf x) (hg y))
       _ = _ := by ring
  have integrated := integral_mono (μ := (θ : Measure X))
    (f := fun x => w x*f x*V) (g := fun x => c*(v x*f x)*W)
    (intCont θ ((w.continuous.mul f.continuous).mul continuous_const))
    (intCont θ ((continuous_const.mul (v.continuous.mul f.continuous)).mul continuous_const)) inner
  change _ * V ≤ c * (_ * W)
  rw [integral_mul_const V (fun x => w x*f x),
    integral_mul_const W (fun x => c*(v x*f x)),
    integral_const_mul c (fun x => v x*f x)] at integrated
  simpa only [mul_assoc] using integrated

/-- Comparing expectations by a cross ratio gives the full oscillation
times (r-1)/(r+1); there is no factor of two for signed tests. -/
private theorem change_reading_cross {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] (θ : ProbabilityMeasure X) (w v f g : C(X, ℝ))
    (hw : ∀ a, 0 ≤ w a) (hv : ∀ a, 0 ≤ v a)
    (hmw : (∫ a, w a ∂(θ : Measure X)) = 1) (hmv : (∫ a, v a ∂(θ : Measure X)) = 1)
    {r A B : ℝ} (hr : 1 ≤ r) (hden : ∀ a b, w a*v b ≤ r^2*(v a*w b))
    (hfg : ∀ a, |f a-g a| ≤ A) (hg : ∀ a b, |g a-g b| ≤ B) :
    |(∫ a, w a*f a ∂(θ : Measure X)) - ∫ a, v a*g a ∂(θ : Measure X)| ≤ A + (r-1)/(r+1)*B := by
  obtain ⟨b,_,hb⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty g.continuous.continuousOn
  let T : C(X,ℝ) := g - ContinuousMap.const X (g b)
  let S : C(X,ℝ) := ContinuousMap.const X B - T
  have hT (x : X) : 0 ≤ T x := sub_nonneg.mpr (hb (Set.mem_univ x))
  have hS (x : X) : 0 ≤ S x := sub_nonneg.mpr ((le_abs_self _).trans (hg x b))
  let mean (u F : C(X,ℝ)) := ∫ a, u a * F a ∂(θ : Measure X)
  have sub (u F : C(X,ℝ)) (hu : (∫ a, u a ∂(θ : Measure X)) = 1) (c : ℝ) :
      mean u (ContinuousMap.const X c - F) = c - mean u F := by
    change (∫ a, u a * (c-F a) ∂(θ : Measure X)) = _
    simp_rw [mul_sub]
    rw [integral_sub (f := fun a => u a*c) (g := fun a => u a*F a) (intCont θ (u.continuous.mul continuous_const))
      (intCont θ (u.continuous.mul F.continuous)), integral_mul_const, hu, one_mul]
  have plus (u : C(X,ℝ)) (hu : (∫ a, u a ∂(θ : Measure X)) = 1) :
      mean u T = mean u g - g b := by
    change (∫ a, u a * (g a - g b) ∂(θ : Measure X)) = _
    simp_rw [mul_sub]
    rw [integral_sub (f := fun a => u a*g a) (g := fun a => u a*g b) (intCont θ (u.continuous.mul g.continuous))
      (intCont θ (u.continuous.mul continuous_const)), integral_mul_const, hu, one_mul]
  have sw := sub w T hmw B
  have sv := sub v T hmv B
  have pw : 0 ≤ mean w T := integral_nonneg fun x => mul_nonneg (hw x) (hT x)
  have pv : 0 ≤ mean v T := integral_nonneg fun x => mul_nonneg (hv x) (hT x)
  have bw : mean w T ≤ B := sub_nonneg.mp (sw ▸ (integral_nonneg (μ := (θ : Measure X))
    fun x => mul_nonneg (hw x) (hS x)) : 0 ≤ B - mean w T)
  have bv : mean v T ≤ B := sub_nonneg.mp (sv ▸ (integral_nonneg (μ := (θ : Measure X))
    fun x => mul_nonneg (hv x) (hS x)) : 0 ≤ B - mean v T)
  have odds : mean w T * (B-mean v T) ≤ r^2*(mean v T*(B-mean w T)) := by
    rw [← sw, ← sv]
    exact mean_product_cross θ w v T S hden hT hS
  have rev : mean v T * (B-mean w T) ≤ r^2*(mean w T*(B-mean v T)) := by
    rw [← sw, ← sv]
    refine mean_product_cross θ v w T S ?_ hT hS
    intro x y
    simpa only [mul_comm (w y) (v x), mul_comm (v y) (w x)] using (hden y x)
  have compare : |mean w g - mean v g| ≤ (r-1)/(r+1)*B := by
    apply abs_sub_le_iff.mpr
    constructor
    · linarith [plus w hmw, plus v hmv, gap_of_odds pw bw pv bv hr odds]
    · linarith [plus w hmw, plus v hmv, gap_of_odds pv bv pw bw hr rev]
  have direct : |mean w f - mean w g| ≤ A := by
    dsimp [mean]
    rw [← integral_sub (f := fun a => w a*f a) (g := fun a => w a*g a)
      (intCont θ (w.continuous.mul f.continuous)) (intCont θ (w.continuous.mul g.continuous))]
    calc _ ≤ ∫ a, |w a * f a - w a*g a| ∂(θ : Measure X) := by
               simpa only [Real.norm_eq_abs] using
                 norm_integral_le_integral_norm (f := fun a => w a*f a - w a*g a) (μ := (θ : Measure X))
         _ ≤ ∫ a, w a*A ∂(θ : Measure X) := by
               apply integral_mono (intCont θ ((w.continuous.mul f.continuous).sub
                 (w.continuous.mul g.continuous)).abs) (intCont θ (w.continuous.mul continuous_const))
               intro a
               change |w a*f a-w a*g a| ≤ w a*A
               rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
               exact mul_le_mul_of_nonneg_left (hfg a) (hw a)
         _ = A := by rw [integral_mul_const, hmw, one_mul]
  exact (abs_sub_le (mean w f) (mean w g) (mean v g)).trans (add_le_add direct compare)

theorem tanh_exp_ratio (β : ℝ) : (Real.exp (2*β)-1)/(Real.exp (2*β)+1) = Real.tanh β := by
  rw [Real.tanh_eq, two_mul, Real.exp_add, Real.exp_neg]
  have h := Real.exp_pos β
  field_simp

/-- The one-neighbour Dobrushin influence of a ferromagnetic unit-sphere
spin in total variation is at most tanh β, in every finite dimension. -/
theorem update_other_tanh {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β) {i j : Site} (hij : j ≠ i)
    {F : C(SpinField N, ℝ)} {ai aj : ℝ} (hi : OscBound F i ai) (hj : OscBound F j aj) :
    OscBound (update β i F) j (aj + if j-i ∈ nearestSteps then Real.tanh β * ai else 0) := by
  by_cases hn : j-i ∈ nearestSteps
  · intro s t h
    have direct (a : WindowSpin N {i}) : |inserted i s F a - inserted i t F a| ≤ aj :=
      hj _ _ (replace_agreeOff h a)
    have rangeBound (a b : WindowSpin N {i}) : |inserted i t F a - inserted i t F b| ≤ ai := by
      apply hi
      intro x hx
      have he : x ∉ ({i} : Finset Site) := by simpa using hx
      rw [replace_outside _ _ _ he, replace_outside _ _ _ he]
    let : Nonempty (WindowSpin N {i}) := ⟨({i} : Finset Site).restrict t⟩
    have H := change_reading_cross (windowPrior N {i}) (density β i s) (density β i t)
      (inserted i s F) (inserted i t F) (density_nonneg β i s) (density_nonneg β i t)
      (density_mass β i s) (density_mass β i t) (Real.one_le_exp (by positivity : 0 ≤ 2*β))
      (density_cross_ratio hβ h) direct rangeBound
    rw [update_eq_integral, update_eq_integral, ite_eq_left hn]
    simpa only [tanh_exp_ratio] using H
  · simpa only [ite_eq_right hn] using update_other hβ hij hi hj

#print axioms density_cross_ratio
#print axioms update_other_tanh
#print axioms density_cap
#print axioms update_self
#print axioms update_other

end IsingScaling.Rotor.PressureSelection.Dobrushin
