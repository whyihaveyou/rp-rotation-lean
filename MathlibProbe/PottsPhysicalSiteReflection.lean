import MathlibProbe.IsingSiteReflection
import MathlibProbe.ReflectedLatticePacket

/-! Site-reflection positivity for the physical scalar Potts two-point function
in a centered free cube. Every edge in the displayed interaction is counted
once. The wall-square proof works for arbitrary finite colour pair potentials. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace IsingScaling.Potts.SiteBox

abbrev Config (q L : ℕ) := BoxSite L → Fin q

def bondTerm {q L : ℕ} (P : Fin q → Fin q → ℝ) (σ : Config q L)
    (x y : BoxSite L) : ℝ :=
  if latticeDistance x y = 1 then P (σ x) (σ y) else 0

def energy {q L : ℕ} (P : Fin q → Fin q → ℝ) (σ : Config q L) : ℝ :=
  (∑ x, ∑ y, bondTerm P σ x y) / 2

def weight {q L : ℕ} (P : Fin q → Fin q → ℝ) (β : ℝ) (σ : Config q L) : ℝ :=
  Real.exp (β * energy P σ)

def componentCorrelation {q L : ℕ} (P : Fin q → Fin q → ℝ) (β : ℝ) (f : Fin q → ℝ)
    (x y : BoxSite L) : ℝ :=
  (∑ σ : Config q L, weight P β σ * f (σ x) * f (σ y)) / ∑ σ : Config q L, weight P β σ

structure Mirror (q L : ℕ) extends BoxSiteMirror L where
  potential : Fin q → Fin q → ℝ

namespace Mirror
variable {q L : ℕ} (M : Mirror q L)
abbrev Wall := {x : BoxSite L // M.tip x = 0} → Fin q
abbrev Half := {x : BoxSite L // 0 < M.tip x} → Fin q

def pack (σ : Config q L) : M.Wall × M.Half × M.Half :=
  (fun x ↦ σ x, fun x ↦ σ x, fun x ↦ σ (M.refl x))

def paste (k : M.Wall × M.Half × M.Half) (x : BoxSite L) : Fin q :=
  if h : M.tip x = 0 then k.1 ⟨x,h⟩ else
  if hp : 0 < M.tip x then k.2.1 ⟨x,hp⟩ else
  k.2.2 ⟨M.refl x, by rw [M.neg]; omega⟩

def equiv : Config q L ≃ M.Wall × M.Half × M.Half where
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

private def halfTerm (σ : Config q L) (x y : BoxSite L) : ℝ :=
  if 0 ≤ M.tip x ∧ 0 ≤ M.tip y then
    if M.tip x = 0 ∧ M.tip y = 0 then bondTerm M.potential σ x y / 2 else bondTerm M.potential σ x y
  else 0

private lemma term_split (σ : Config q L) (x y : BoxSite L) :
    bondTerm M.potential σ x y = M.halfTerm σ x y +
        M.halfTerm (σ ∘ M.refl) (M.refl x) (M.refl y) := by
  unfold halfTerm bondTerm
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

def halfEnergy (σ : Config q L) : ℝ := (∑ x, ∑ y, M.halfTerm σ x y) / 2

private theorem energy_split (σ : Config q L) :
    energy M.potential σ = M.halfEnergy σ + M.halfEnergy (σ ∘ M.refl) := by
  change (∑ x, ∑ y, bondTerm M.potential σ x y) / 2 = _
  simp_rw [M.term_split σ]
  simp only [sum_add_distrib]
  simp_rw [fun x => Equiv.sum_comp M.refl (M.halfTerm (σ ∘ M.refl) (M.refl x))]
  rw [Equiv.sum_comp M.refl (fun x => ∑ y, M.halfTerm (σ ∘ M.refl) x y), add_div]
  rfl

private theorem halfEnergy_congr {σ τ : Config q L}
    (h : ∀ x, 0 ≤ M.tip x → σ x = τ x) : M.halfEnergy σ = M.halfEnergy τ := by
  unfold halfEnergy
  congr 1
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases he : 0 ≤ M.tip x ∧ 0 ≤ M.tip y
  · simp [halfTerm, bondTerm, he, h x he.1, h y he.2]
  · simp [halfTerm, he]

private theorem paste_energy (b : M.Wall) (u v : M.Half) :
    energy M.potential (M.paste (b,u,v)) =
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
    0 ≤ ∑ σ : Config q L, weight M.potential β σ *
      F (M.pack σ).1 (M.pack σ).2.1 * F (M.pack σ).1 (M.pack σ).2.2 := by
  classical
  let a (b : M.Wall) (u : M.Half) := Real.exp (β * M.halfEnergy (M.paste (b,u,u))) * F b u
  let integrand (σ : Config q L) := weight M.potential β σ *
      F (M.pack σ).1 (M.pack σ).2.1 * F (M.pack σ).1 (M.pack σ).2.2
  change 0 ≤ ∑ σ, integrand σ
  rw [← Equiv.sum_comp M.equiv.symm integrand]
  have hex (b : M.Wall) (u v : M.Half) :
      integrand (M.equiv.symm (b,u,v)) = a b u * a b v := by
    have hk : M.pack (M.equiv.symm (b,u,v)) = (b,u,v) := M.equiv.apply_symm_apply _
    unfold integrand
    rw [hk]
    change weight M.potential β (M.paste (b,u,v)) * F b u * F b v = _
    simp only [weight, M.paste_energy, mul_add, Real.exp_add, a]
    ring
  simp only [Fintype.sum_prod_type, hex]
  apply sum_nonneg
  intro b _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact mul_self_nonneg _

private def readHalf (f : Fin q → ℝ) (b : M.Wall) (u : M.Half) (x : BoxSite L)
    (hx : 0 ≤ M.tip x) : ℝ :=
  if h : M.tip x = 0 then f (b ⟨x,h⟩) else f (u ⟨x, by omega⟩)

private lemma readHalf_first (f : Fin q → ℝ) (σ : Config q L) (x : BoxSite L) (hx : 0 ≤ M.tip x) :
    M.readHalf f (M.pack σ).1 (M.pack σ).2.1 x hx = f (σ x) := by
  unfold readHalf pack
  split <;> rfl

private lemma readHalf_second (f : Fin q → ℝ) (σ : Config q L) (x : BoxSite L) (hx : 0 ≤ M.tip x) :
    M.readHalf f (M.pack σ).1 (M.pack σ).2.2 x hx = f (σ (M.refl x)) := by
  unfold readHalf pack
  split
  · rename_i h
    rw [M.wall x h]
  · rfl

/-- Positivity of the reflected Gibbs two-point matrix, including tests whose
sites meet the mirror. The coefficients can have either sign. -/
theorem twoPoint_reflection_positive {ι : Type*} [Fintype ι]
    (β : ℝ) (f : Fin q → ℝ) (x : ι → BoxSite L) (hx : ∀ i, 0 ≤ M.tip (x i)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * componentCorrelation M.potential β f (x i) (M.refl (x j)) := by
  classical
  let F (b : M.Wall) (u : M.Half) := ∑ i, c i * M.readHalf f b u (x i) (hx i)
  have h := M.reflection_positive β F
  dsimp only [F] at h
  simp only [M.readHalf_first, M.readHalf_second] at h
  have hZ : 0 ≤ ∑ σ : Config q L, weight M.potential β σ :=
    Finset.sum_nonneg fun σ _ => (Real.exp_pos _).le
  have hswap (a : Config q L → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ σ, a σ i j) = ∑ σ, ∑ i, ∑ j, a σ i j := by
    calc
      _ = ∑ i, ∑ σ, ∑ j, a σ i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold componentCorrelation
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  apply div_nonneg _ hZ
  rw [hswap]
  refine h.trans_eq ?_
  symm
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum _ _ (weight M.potential β σ), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring


end Mirror

/-- One physical equal-colour bond has Boltzmann weight exp(β * equalColour a b). -/
def equalColour {q : ℕ} (a b : Fin q) : ℝ := if a = b then 1 else 0

def colourMark {q : ℕ} (j a : Fin q) : ℝ := (q : ℝ) * equalColour j a - 1

def simplex {q : ℕ} (a b : Fin q) : ℝ :=
  ((q : ℝ) * equalColour a b - 1) / ((q : ℝ) - 1)

private theorem colourMark_sum {q : ℕ} (a b : Fin q) :
    ∑ j, colourMark j a * colourMark j b =
      (q : ℝ) * ((q : ℝ) * equalColour a b - 1) := by
  classical
  have hsum (x : Fin q) : ∑ j, equalColour j x = 1 := by simp [equalColour]
  have hcross : ∑ j, equalColour j a * equalColour j b = equalColour a b := by
    by_cases h : a = b <;> simp [equalColour, h, eq_comm]
  calc
    _ = ∑ j : Fin q, ((q : ℝ)^2 * (equalColour j a * equalColour j b) -
          q * equalColour j a - q * equalColour j b + 1) := by
      apply sum_congr rfl
      intro j _
      unfold colourMark
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum, hcross, hsum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem simplex_eq_colourForm {q : ℕ} (hq : 2 ≤ q) (a b : Fin q) :
    simplex a b = (∑ j, colourMark j a * colourMark j b) /
      ((q : ℝ) * (q - 1 : ℝ)) := by
  have h : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [colourMark_sum]
  unfold simplex
  field_simp

theorem abs_simplex_le_one {q : ℕ} (hq : 2 ≤ q) (a b : Fin q) : |simplex a b| ≤ 1 := by
  have h : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) - 1 := by linarith
  unfold simplex equalColour
  split_ifs <;> simp only [mul_one, mul_zero, zero_sub, abs_div, abs_neg, abs_one,
    abs_of_pos hpos]
  · rw [div_self hpos.ne']
  · rw [div_le_one hpos]
    linarith

/-- Unit-simplex Potts scalar in an actual free Gibbs cube. -/
def boxPair (q : ℕ) (β : ℝ) {L : ℕ} (x y : BoxSite L) : ℝ :=
  (∑ σ : Config q L, weight equalColour β σ * simplex (σ x) (σ y)) /
    ∑ σ : Config q L, weight equalColour β σ

theorem boxPair_eq_colourForm {q L : ℕ} (hq : 2 ≤ q) (β : ℝ) (x y : BoxSite L) :
    boxPair q β x y = (∑ j : Fin q, componentCorrelation equalColour β (colourMark j) x y) /
      ((q : ℝ) * (q - 1 : ℝ)) := by
  classical
  unfold boxPair componentCorrelation
  simp_rw [simplex_eq_colourForm hq, div_eq_mul_inv, ← mul_assoc,
    ← Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Config q L)))]
  ring_nf

theorem abs_boxPair_le_one {q L : ℕ} (hq : 2 ≤ q) (β : ℝ) (x y : BoxSite L) :
    |boxPair q β x y| ≤ 1 := by
  classical
  have : NeZero q := ⟨by omega⟩
  have hZ : 0 < ∑ σ : Config q L, weight equalColour β σ :=
    sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [boxPair, abs_div, abs_of_pos hZ, div_le_one hZ]
  apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro σ _
  have hw : 0 < weight equalColour β σ := Real.exp_pos _
  rw [abs_mul, abs_of_pos hw]
  exact mul_le_of_le_one_right hw.le (abs_simplex_le_one hq _ _)

theorem boxPair_mirror_nonneg {q L : ℕ} (hq : 2 ≤ q) (β : ℝ) (M : BoxSiteMirror L)
    {ι : Type*} [Fintype ι] (x : ι → BoxSite L) (hx : ∀ i, 0 ≤ M.tip (x i)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * boxPair q β (x i) (M.refl (x j)) := by
  classical
  let T : Mirror q L := ⟨M, equalColour⟩
  have h (a : Fin q) := T.twoPoint_reflection_positive β (colourMark a) x hx c
  have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hg : 0 ≤ (q : ℝ) * (q - 1 : ℝ) := mul_nonneg (by linarith) (by linarith)
  simp_rw [boxPair_eq_colourForm hq, ← mul_div_assoc, Finset.mul_sum, div_eq_mul_inv,
    ← Finset.sum_mul]
  apply mul_nonneg _ (inv_nonneg.mpr hg)
  calc
    0 ≤ ∑ a : Fin q, ∑ i, ∑ j, c i * c j *
        componentCorrelation equalColour β (colourMark a) (x i) (M.refl (x j)) :=
      Finset.sum_nonneg (fun a _ => h a)
    _ = _ := by
      rw [Finset.sum_comm]
      exact sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- The pair has zero extension outside the finite cube. -/
def latticePair (q : ℕ) (β : ℝ) (L : ℕ) (x y : Site) : ℝ :=
  if hx : x ∈ cube L then if hy : y ∈ cube L then boxPair q β ⟨x,hx⟩ ⟨y,hy⟩ else 0 else 0

@[simp] theorem latticePair_inside {q L : ℕ} (β : ℝ) (x y : BoxSite L) :
    latticePair q β L x y = boxPair q β x y := by simp [latticePair, x.property, y.property]

def StationaryPairLimit (q : ℕ) (β : ℝ) (sizes : ℕ → ℕ) (g : Site → ℝ) : Prop :=
  ∀ x y : Site, Tendsto (fun j => latticePair q β (sizes j) x y) atTop (𝓝 (g (x-y)))

theorem StationaryPairLimit.abs_le_one {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (z : Site) : |g z| ≤ 1 := by
  have hl := (hg z 0).abs
  rw [sub_zero] at hl
  apply le_of_tendsto hl (Eventually.of_forall ?_)
  intro j
  unfold latticePair
  split <;> rename_i h
  · split
    · exact abs_boxPair_le_one hq _ _ _
    · simp
  · simp

private theorem eventually_in_cube (x : Site) : ∀ᶠ L : ℕ in atTop, x ∈ cube L := by
  filter_upwards [eventually_ge_atTop (∑ i, (x i).natAbs)] with L hL
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  omega

theorem StationaryPairLimit.reflected_positive {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (hL : Tendsto sizes atTop atTop)
    (t : Site → ℤ) (r : Site → Site) (M : ∀ L, BoxSiteMirror L)
    (ht : ∀ L (x : BoxSite L), (M L).tip x = t x)
    (hr : ∀ L (x : BoxSite L), ((M L).refl x).val = r x)
    {ι : Type} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 ≤ t (x i)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * g (x i - r (x j)) := by
  classical
  have hlim : Tendsto (fun j : ℕ => ∑ a, ∑ b, c a * c b *
      latticePair q β (sizes j) (x a) (r (x b))) atTop
      (𝓝 (∑ a, ∑ b, c a * c b * g (x a - r (x b)))) :=
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      tendsto_const_nhds.mul (hg _ _)
  apply ge_of_tendsto hlim
  have hall : ∀ᶠ j in atTop, ∀ i, x i ∈ cube (sizes j) :=
    Filter.eventually_all.mpr fun i => hL.eventually (eventually_in_cube (x i))
  filter_upwards [hall] with j hj
  let y (i : ι) : BoxSite (sizes j) := ⟨x i,hj i⟩
  have hs := boxPair_mirror_nonneg hq β (M (sizes j)) y
    (fun i => by rw [ht]; exact hx i) c
  simpa only [← latticePair_inside, hr, y] using hs

theorem StationaryPairLimit.axis_positive {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (hL : Tendsto sizes atTop atTop)
    {ι : Type} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 ≤ x i 0) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * g (x i - signedPerm (Equiv.refl _) (fun a => decide (a = 0)) (x j)) :=
  hg.reflected_positive hq hL (fun v => v 0) _ axisSiteMirror
    (fun _ _ => rfl) (fun _ _ => rfl) x hx c

theorem StationaryPairLimit.diagonal_positive {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (hL : Tendsto sizes atTop atTop)
    {ι : Type} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 ≤ x i 0 - x i 1) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * g (x i - signedPerm (Equiv.swap 0 1) (fun _ => false) (x j)) :=
  hg.reflected_positive hq hL (fun v => v 0-v 1) _ diagonalSiteMirror
    (fun _ _ => rfl) (fun _ _ => rfl) x hx c

/-- Every stationary limit of the actual free-box Potts scalar has a positive
Hausdorff spectrum for every signed transverse test along each representative
axis or face diagonal. The cube radii and temperature are shared by all pairs. -/
theorem StationaryPairLimit.gridPacket_spectrum {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (hL : Tendsto sizes atTop atTop)
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal g c x y n := by
  apply Packet.gridPacket_spectrum_of_site_reflection (hg.abs_le_one hq)
  · intro ι _ s hs u
    exact hg.axis_positive hq hL s hs u
  · intro ι _ s hs u
    exact hg.diagonal_positive hq hL s hs u


private def cubePerm (L) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Equiv.Perm (BoxSite L) :=
  (signedPerm p s).subtypeEquiv (signedPerm_cube p s L)

private theorem weight_cubePerm {q L : ℕ} (P : Fin q → Fin q → ℝ) (β : ℝ)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (σ : Config q L) :
    weight P β (σ ∘ cubePerm L p s) = weight P β σ := by
  let e := cubePerm L p s
  have hd (x y : BoxSite L) : latticeDistance (e x) (e y) = latticeDistance x y :=
    signedPerm_distance p s x y
  apply congrArg (fun t : ℝ => Real.exp (β * (t / 2)))
  calc
    _ = ∑ x, ∑ y, bondTerm P σ (e x) (e y) := by
      simp only [bondTerm, hd, Function.comp_apply]
      rfl
    _ = _ := by
      simp_rw [fun x => Equiv.sum_comp e (bondTerm P σ (e x))]
      exact Equiv.sum_comp e (fun x => ∑ y, bondTerm P σ x y)

private theorem boxPair_cubePerm (q : ℕ) (β : ℝ) {L : ℕ} (p : Equiv.Perm (Fin 3))
    (s : Fin 3 → Bool) (x y : BoxSite L) :
    boxPair q β (cubePerm L p s x) (cubePerm L p s y) = boxPair q β x y := by
  classical
  let e : Equiv.Perm (Config q L) := (cubePerm L p s).symm.arrowCongr (Equiv.refl (Fin q))
  let f (σ : Config q L) := weight equalColour β σ * simplex (σ x) (σ y)
  have hf (σ : Config q L) : f (e σ) =
      weight equalColour β σ * simplex (σ (cubePerm L p s x)) (σ (cubePerm L p s y)) := by
    change weight _ _ (σ ∘ cubePerm L p s) * _ = _
    rw [weight_cubePerm]
    rfl
  unfold boxPair
  congr 1
  exact (Finset.sum_congr rfl (fun σ _ => (hf σ).symm)).trans (Equiv.sum_comp e f)

theorem latticePair_signedPerm (q : ℕ) (β : ℝ) (L : ℕ) (p : Equiv.Perm (Fin 3))
    (s : Fin 3 → Bool) (x y : Site) :
    latticePair q β L (signedPerm p s x) (signedPerm p s y) = latticePair q β L x y := by
  classical
  by_cases hx : x ∈ cube L
  · have hx' := (signedPerm_cube p s L x).mp hx
    by_cases hy : y ∈ cube L
    · have hy' := (signedPerm_cube p s L y).mp hy
      simp only [latticePair, hx, hy, hx', hy', dite_true]
      exact boxPair_cubePerm q β p s ⟨x,hx⟩ ⟨y,hy⟩
    · have hy' := mt (signedPerm_cube p s L y).mpr hy
      simp [latticePair, hx, hx', hy, hy']
  · have hx' := mt (signedPerm_cube p s L x).mpr hx
    simp [latticePair, hx, hx']

theorem StationaryPairLimit.signedPerm_invariant {q β sizes g}
    (hg : StationaryPairLimit q β sizes g) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (x : Site) : g (signedPerm p s x) = g x := by
  have h₁ := hg (signedPerm p s x) (signedPerm p s 0)
  have h₂ := hg x 0
  simp only [latticePair_signedPerm] at h₁
  simp only [signedPerm_zero, sub_zero] at h₁ h₂
  exact tendsto_nhds_unique h₁ h₂

/-- The same moment identity for all cubic images of both chosen normals. -/
theorem StationaryPairLimit.gridPacket_signedPerm_spectrum {q : ℕ} (hq : 2 ≤ q) {β sizes g}
    (hg : StationaryPairLimit q β sizes g) (hL : Tendsto sizes atTop atTop)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (diagonal : Bool)
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, ∀ n,
      (∫ t, (t : ℝ)^n ∂(μ : Measure Packet.UnitInterval)) =
        Packet.gridPacket diagonal (fun z => g (signedPerm p s z)) c x y n := by
  have h : (fun z => g (signedPerm p s z)) = g := funext (hg.signedPerm_invariant p s)
  rw [h]
  exact hg.gridPacket_spectrum hq hL diagonal c x y

theorem latticePair_origin {q : ℕ} (hq : 2 ≤ q) (β : ℝ) (L : ℕ) :
    latticePair q β L 0 0 = 1 := by
  classical
  have : NeZero q := ⟨by omega⟩
  have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hd (a : Fin q) : simplex a a = 1 := by
    simp [simplex, equalColour, show (q : ℝ) - 1 ≠ 0 by linarith]
  have hm : (0 : Site) ∈ cube L := by simp [cube, Fintype.mem_piFinset]
  have hZ : 0 < ∑ σ : Config q L, weight equalColour β σ :=
    sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [latticePair, hm, dite_true, boxPair, hd, mul_one, div_self hZ.ne']

theorem StationaryPairLimit.origin {q β sizes g} (hq : 2 ≤ q)
    (hg : StationaryPairLimit q β sizes g) : g 0 = 1 := by
  have h := hg (0 : Site) 0
  simp only [sub_zero, latticePair_origin hq] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem StationaryPairLimit.cube_pos_of_nonneg {q β sizes g} (hq : 2 ≤ q)
    (hg : StationaryPairLimit q β sizes g) (hp : ∀ z, 0 ≤ g z) (R : ℕ) :
    0 < ∑ z ∈ cube R, g z := by
  have hm : (0 : Site) ∈ cube R := by simp [cube, Fintype.mem_piFinset]
  have h0 : 0 < g 0 := by rw [hg.origin hq]; norm_num
  exact h0.trans_le (Finset.single_le_sum (fun z _ => hp z) hm)

#print axioms boxPair_mirror_nonneg
#print axioms StationaryPairLimit.cube_pos_of_nonneg
#print axioms StationaryPairLimit.signedPerm_invariant
#print axioms StationaryPairLimit.gridPacket_signedPerm_spectrum
#print axioms StationaryPairLimit.gridPacket_spectrum
#print axioms StationaryPairLimit.axis_positive
#print axioms StationaryPairLimit.diagonal_positive

end IsingScaling.Potts.SiteBox
