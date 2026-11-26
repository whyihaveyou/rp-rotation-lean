import MathlibProbe.PottsCanonicalFreePair
import MathlibProbe.IsingBondMirror

/-! The shifted axial reflection for the canonical Potts scalar. The
rectangles have a real crossing bond at each site of the face. Their
Gibbs pair is squeezed between that of two successive centered cubes. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace IsingScaling.Potts.SiteBox.Shifted
open EdwardsSokal

private def edges {T : Type*} [Fintype T] (p : T → Site) : Finset (T × T) :=
  univ.filter fun e => latticeDistance (p e.1) (p e.2) = 1

private def volumePair {T : Type*} [Fintype T] (q : ℕ) (β : ℝ) (p : T → Site) (x y : T) :=
  graphScalar q (edges p) (fun _ => β / 2) x y

private theorem volumePair_cube {q L : ℕ} (β : ℝ) (x y : BoxSite L) :
    volumePair q β Subtype.val x y = boxPair q β x y := (boxPair_directed β x y).symm

private theorem volumePair_embed {T W : Type*} [Fintype T] [Fintype W]
    {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) (p : T → Site) (p' : W → Site)
    (e : T ↪ W) (he : ∀ i, p' (e i) = p i) (x y : T) :
    volumePair q β p x y ≤ volumePair q β p' (e x) (e y) := by
  classical
  have : NeZero q := ⟨by omega⟩
  let J := (edges p).map (e.prodMap e)
  have hJ : J ⊆ edges p' := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hb
    change (e a.1, e a.2) ∈ edges p'
    exact mem_filter.mpr ⟨mem_univ _, by simpa only [he] using (mem_filter.mp ha).2⟩
  have hw (σ : W → Fin q) :
      spinWeight J (fun _ => β/2) σ = spinWeight (edges p) (fun _ => β/2) (σ ∘ e) := by
    unfold spinWeight J
    rw [prod_map]
    rfl
  have hsmall : graphScalar q J (fun _ => β/2) (e x) (e y) = volumePair q β p x y := by
    unfold volumePair graphScalar
    simp only [hw]
    exact normalized_restriction e
      (fun σ : T → Fin q => spinWeight (edges p) (fun _ => β/2) σ * simplexMark (σ x) (σ y))
      (spinWeight (edges p) (fun _ => β/2)) _ _
  rw [← hsmall]
  exact graphScalar_mono hq hJ (fun _ => div_nonneg hβ (by norm_num)) _ _

open BondMirror (P V loc)

private def halves {L q : ℕ} : (V L → Fin q) ≃ (P L → Fin q) × (P L → Fin q) where
  toFun σ := (fun i => σ (true,i), fun i => σ (false,i))
  invFun a x := if x.1 then a.1 x.2 else a.2 x.2
  left_inv σ := by funext ⟨b,i⟩; cases b <;> rfl
  right_inv a := by rcases a with ⟨u,v⟩; rfl

private def seam (L : ℕ) := univ.filter fun i : P L => i.1.val = 0
private abbrev posSite {L : ℕ} (i : P L) : Site := loc (true,i)

private def term {T : Type*} {q : ℕ} (p : T → Site) (β : ℝ) (σ : T → Fin q) (i j : T) : ℝ :=
  if latticeDistance (p i) (p j) = 1 then (β / 2) * equalColour (σ i) (σ j) else 0

private theorem spinWeight_exp {T : Type*} [Fintype T] {q : ℕ} (p : T → Site) (β : ℝ)
    (σ : T → Fin q) : spinWeight (edges p) (fun _ => β/2) σ =
      Real.exp (∑ i, ∑ j, term p β σ i j) := by
  have hed (a b : Fin q) : edgeWeight (β/2) a b = Real.exp ((β/2)*equalColour a b) := by
    by_cases h : a = b <;> simp [edgeWeight, equalColour, h]
  unfold spinWeight
  simp only [hed, ← Real.exp_sum]
  apply congrArg Real.exp
  rw [edges, Finset.sum_filter, Fintype.sum_prod_type]
  rfl

private def crossTerm {q L : ℕ} (β : ℝ) (u v : P L → Fin q) (i : P L) : ℝ :=
  if i.1.val = 0 then (β/2) * equalColour (u i) (v i) else 0

private theorem cross_row {q L : ℕ} (β : ℝ) (u v : P L → Fin q) (b : Bool) (i : P L) :
    (∑ j : P L, if latticeDistance (loc (b,i)) (loc (!b,j)) = 1
      then (β/2) * equalColour (u i) (v j) else 0) = crossTerm β u v i := by
  classical
  calc
    _ = ∑ j : P L, if j=i then crossTerm β u v i else 0 := by
      apply sum_congr rfl
      intro j _
      simp only [BondMirror.cross_dist]
      by_cases hi : j=i
      · subst j; simp [crossTerm]
      · simp [hi, Ne.symm hi]
    _ = _ := by simp

private theorem cross_exp {q L : ℕ} (β : ℝ) (u v : P L → Fin q) :
    crossingWeight (seam L) (fun _ => β) u v =
      Real.exp ((∑ i, crossTerm β u v i) + ∑ i, crossTerm β u v i) := by
  rw [← Finset.sum_add_distrib, Real.exp_sum]
  unfold crossingWeight seam
  rw [Finset.prod_filter]
  apply prod_congr rfl
  intro i _
  by_cases hi : i.1.val=0 <;> by_cases huv : u i = v i <;>
    simp [crossTerm, edgeWeight, equalColour, hi, huv]

private theorem weight_split {q L : ℕ} (β : ℝ) (u v : P L → Fin q) :
    spinWeight (edges (loc (L:=L))) (fun _ => β/2) ((halves (L:=L)).symm (u,v)) =
      reflectedGibbsWeight (edges (posSite (L:=L))) (seam L) (fun _ => β/2) (fun _ => β) u v := by
  let σ : V L → Fin q := halves.symm (u,v)
  have htt (i j : P L) : term loc β σ (true,i) (true,j) = term posSite β u i j := rfl
  have hff (i j : P L) : term loc β σ (false,i) (false,j) = term posSite β v i j := by
    unfold term
    rw [BondMirror.same_dist]
    rfl
  have htf (i : P L) : (∑ j, term loc β σ (true,i) (false,j)) = crossTerm β u v i :=
    cross_row β u v true i
  have hft (i : P L) : (∑ j, term loc β σ (false,i) (true,j)) = crossTerm β u v i := by
    have eq : crossTerm β v u i = crossTerm β u v i := by simp [crossTerm, equalColour, eq_comm]
    exact (cross_row β v u false i).trans eq
  change spinWeight (edges loc) (fun _ => β/2) σ =
    spinWeight (edges posSite) (fun _ => β/2) u * spinWeight (edges posSite) (fun _ => β/2) v *
      crossingWeight (seam L) (fun _ => β) u v
  rw [spinWeight_exp, spinWeight_exp, spinWeight_exp, cross_exp, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  simp only [BondMirror.sum_halves, Finset.sum_add_distrib, htt, hff, htf, hft]
  ring

private theorem raw_gram {q L : ℕ} [NeZero q] {β : ℝ} (hβ : 0 ≤ β) (F : (P L → Fin q) → ℝ) :
    0 ≤ ∑ σ : V L → Fin q, spinWeight (edges loc) (fun _ => β/2) σ *
      (F (fun i => σ (true,i)) * F (fun i => σ (false,i))) := by
  classical
  let W := reflectedGibbsWeight (q:=q) (edges (posSite (L:=L))) (seam L) (fun _ => β/2) (fun _ => β)
  let A (σ : V L → Fin q) := spinWeight (edges loc) (fun _ => β/2) σ *
      (F (fun i => σ (true,i)) * F (fun i => σ (false,i)))
  have hp := reflectedGibbs_signed_test_nonneg (q:=q) (edges (posSite (L:=L))) (seam L)
    (fun _ => β/2) (fun _ => β) (fun _ _ => hβ) F
  have hZ : 0 < ∑ u, ∑ v, W u v := by
    apply sum_pos _ univ_nonempty
    intro u _
    exact sum_pos (fun v _ => reflectedGibbsWeight_pos _ _ _ _ u v) univ_nonempty
  change 0 ≤ (∑ u, ∑ v, W u v * (F u * F v)) / (∑ u, ∑ v, W u v) at hp
  change 0 ≤ ∑ σ, A σ
  rw [← Equiv.sum_comp (halves (q:=q) (L:=L)).symm A, Fintype.sum_prod_type]
  have hn := (le_div_iff₀ hZ).mp hp
  rw [zero_mul] at hn
  refine hn.trans_eq ?_
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  simp only [A, weight_split]
  rfl

private def componentPair {q L : ℕ} (β : ℝ) (a : Fin q) (x y : V L) : ℝ :=
  (∑ σ : V L → Fin q, spinWeight (edges loc) (fun _ => β/2) σ * (colourMark a (σ x) * colourMark a (σ y))) /
  (∑ σ : V L → Fin q, spinWeight (edges loc) (fun _ => β/2) σ)

private theorem pair_colour_sum {q L : ℕ} (hq : 2 ≤ q) (β : ℝ) (x y : V L) :
    volumePair q β loc x y = (∑ a : Fin q, componentPair β a x y) / ((q : ℝ) * (q-1 : ℝ)) := by
  unfold volumePair graphScalar componentPair
  simp_rw [← marks_eq, simplex_eq_colourForm hq, div_eq_mul_inv, ← mul_assoc, ← sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  let configs : Finset (V L → Fin q) := Finset.univ
  have hconfigs (I : Fintype (V L → Fin q)) : @Finset.univ _ I = configs := by
    ext σ
    simp only [configs, Finset.mem_univ]
  simp only [hconfigs, mul_assoc]
  ring

private theorem component_reflected {q L : ℕ} [NeZero q] {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type*} [Fintype ι] (x : ι → P L) (c : ι → ℝ) (a : Fin q) :
    0 ≤ ∑ i, ∑ j, c i * c j * componentPair β a (true,x i) (false,x j) := by
  classical
  let W (σ : V L → Fin q) := spinWeight (edges loc) (fun _ => β/2) σ
  let F (u : P L → Fin q) := ∑ i, c i * colourMark a (u (x i))
  have h := raw_gram hβ F
  have hz : 0 ≤ ∑ σ, W σ := by
    apply sum_nonneg
    intro σ _
    change 0 ≤ spinWeight (edges loc) (fun _ => β/2) σ
    rw [spinWeight_exp]
    exact (Real.exp_pos _).le
  have hswap (A : (V L → Fin q) → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ σ, A σ i j) = ∑ σ, ∑ i, ∑ j, A σ i j := by
    calc _ = ∑ i, ∑ σ, ∑ j, A σ i j := sum_congr rfl (fun _ _ => sum_comm)
         _ = _ := sum_comm
  change 0 ≤ ∑ i, ∑ j, c i*c j * ((∑ σ, W σ *
    (colourMark a (σ (true,x i)) * colourMark a (σ (false,x j)))) / ∑ σ, W σ)
  simp_rw [← mul_div_assoc, Finset.mul_sum, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  apply div_nonneg _ hz
  rw [hswap]
  refine h.trans_eq (sum_congr rfl (fun σ _ => ?_))
  change W σ * ((∑ i, c i*colourMark a (σ (true,x i))) * ∑ j, c j*colourMark a (σ (false,x j))) = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
  ring

private theorem finite_reflected {q L : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type*} [Fintype ι] (x : ι → P L) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j * volumePair q β loc (true,x i) (false,x j) := by
  have : NeZero q := ⟨by omega⟩
  have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hg : 0 ≤ (q : ℝ) * (q-1 : ℝ) := mul_nonneg (by linarith) (by linarith)
  simp_rw [pair_colour_sum hq, ← mul_div_assoc, Finset.mul_sum, div_eq_mul_inv, ← Finset.sum_mul]
  apply mul_nonneg _ (inv_nonneg.mpr hg)
  calc
    0 ≤ ∑ a : Fin q, ∑ i, ∑ j, c i*c j * componentPair β a (true,x i) (false,x j) :=
      sum_nonneg (fun a _ => component_reflected hβ x c a)
    _ = _ := by rw [Finset.sum_comm]; exact sum_congr rfl (fun _ _ => Finset.sum_comm)

private theorem port_tendsto {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    (x y : Site) (hx : 0 < x 0) (hy : 0 < y 0) :
    Tendsto (fun L => volumePair q β loc (true,BondMirror.port L x) (false,BondMirror.port L y))
      atTop (𝓝 (canonicalFreePair q β (x-BondMirror.reflected y))) := by
  have hG := canonicalFreePair_stationary hq hβ x (BondMirror.reflected y)
  have hboth : ∀ᶠ L : ℕ in atTop,
      latticePair q β L x (BondMirror.reflected y) ≤
          volumePair q β loc (true,BondMirror.port L x) (false,BondMirror.port L y) ∧
      volumePair q β loc (true,BondMirror.port L x) (false,BondMirror.port L y) ≤
          latticePair q β (L+1) x (BondMirror.reflected y) := by
    filter_upwards [BondMirror.ev_cube x, BondMirror.ev_cube y, BondMirror.ev_cube (BondMirror.reflected y)]
      with L hX hY hY'
    let X : BoxSite L := ⟨x,hX⟩
    let Y : BoxSite L := ⟨y,hY⟩
    let Z : BoxSite L := ⟨BondMirror.reflected y,hY'⟩
    have ex : BondMirror.inner L X = (true,BondMirror.port L x) := Prod.ext (BondMirror.place_pos X hx)
      (by simp only [X, BondMirror.port, dite_eq_left hX]; rfl)
    have ey : BondMirror.inner L Y = (true,BondMirror.port L y) := Prod.ext (BondMirror.place_pos Y hy)
      (by simp only [Y, BondMirror.port, dite_eq_left hY]; rfl)
    have lx : loc (true,BondMirror.port L x) = x := by rw [← ex]; exact BondMirror.place_loc X
    have ly : loc (false,BondMirror.port L y) = BondMirror.reflected y := by
      rw [BondMirror.flip_loc, ← ey, show loc (BondMirror.inner L Y) = y from BondMirror.place_loc Y]
    have ez : BondMirror.inner L Z = (false,BondMirror.port L y) :=
      BondMirror.loc_inj ((BondMirror.place_loc Z).trans ly.symm)
    have hlo := volumePair_embed hq hβ Subtype.val loc (BondMirror.inner L) (fun t => BondMirror.place_loc t) X Z
    have hhi := volumePair_embed hq hβ loc Subtype.val (BondMirror.outer L) (fun _ => rfl)
      (true,BondMirror.port L x) (false,BondMirror.port L y)
    rw [volumePair_cube, ← latticePair_inside, ex, ez] at hlo
    rw [volumePair_cube, ← latticePair_inside] at hhi
    change _ ≤ latticePair q β (L+1) (loc (true,BondMirror.port L x)) (loc (false,BondMirror.port L y)) at hhi
    rw [lx,ly] at hhi
    exact ⟨hlo,hhi⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hG ((tendsto_add_atTop_iff_nat 1).mpr hG)
    (hboth.mono fun _ => And.left) (hboth.mono fun _ => And.right)

end IsingScaling.Potts.SiteBox.Shifted

namespace IsingScaling.Potts.SiteBox
open BondMirror (loc)

/-- Exact bond-plane reflection positivity at the plane x₀=1/2. The
source kernel is the canonical free Potts scalar on the whole cubic lattice. -/
theorem canonicalFreePair_axialBond_positive {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    Packet.SiteReflectedPositive (canonicalFreePair q β) (fun x => x 0 - 1) BondMirror.reflected := by
  intro ι _ x hx c
  have hx' (i) : 0 < x i 0 := by have hj : 0 ≤ x i 0 - 1 := hx i; omega
  have hm : Tendsto (fun L => ∑ i, ∑ j, c i*c j *
      Shifted.volumePair q β loc (true,BondMirror.port L (x i)) (false,BondMirror.port L (x j))) atTop
      (𝓝 (∑ i, ∑ j, c i*c j*canonicalFreePair q β (x i-BondMirror.reflected (x j)))) :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      tendsto_const_nhds.mul (Shifted.port_tendsto hq hβ (x i) (x j) (hx' i) (hx' j))))
  exact ge_of_tendsto' hm (fun L => Shifted.finite_reflected hq hβ (fun i => BondMirror.port L (x i)) c)

#print axioms canonicalFreePair_axialBond_positive

/-- The manuscript's face at x₀=−1/2, in the convention where the
positive side starts at coordinate zero. -/
theorem canonicalFreePair_axialShift_positive {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    Packet.SiteReflectedPositive (canonicalFreePair q β) (fun x => x 0)
      (fun x => ![-x 0-1,x 1,x 2]) := by
  intro ι _ x hx c
  let z (i : ι) : Site := ![x i 0 + 1, x i 1, x i 2]
  have hz (i) : 0 ≤ z i 0 - 1 := by simpa [z] using hx i
  have h := canonicalFreePair_axialBond_positive hq hβ z hz c
  have he (i j) : z i - BondMirror.reflected (z j) =
      x i - ![-x j 0-1,x j 1,x j 2] := by
    funext k
    fin_cases k
    · change x i 0 + 1 - (1 - (x j 0 + 1)) = x i 0 - (-x j 0-1)
      omega
    · rfl
    · rfl
  simpa only [he] using h

/-- The shifted diagonal plane x₀−x₁=−1 is a translated site mirror.
The change of variables is integer translation by the first coordinate vector. -/
theorem canonicalFreePair_diagonalShift_positive {q : ℕ} (hq : 2 ≤ q)
    {β : ℝ} (hβ : 0 ≤ β) :
    Packet.SiteReflectedPositive (canonicalFreePair q β) (fun x => x 0-x 1+1)
      (fun x => ![x 1-1,x 0+1,x 2]) := by
  intro ι _ x hx c
  let z (i : ι) : Site := ![x i 0 + 1,x i 1,x i 2]
  have hz (i) : 0 ≤ z i 0 - z i 1 := by
    change 0 ≤ x i 0 + 1 - x i 1
    have := hx i
    change 0 ≤ x i 0 - x i 1 + 1 at this
    omega
  have h := (canonicalFreePair_stationary hq hβ).diagonal_positive hq tendsto_id z hz c
  have he (i j) :
      z i - signedPerm (Equiv.swap 0 1) (fun _ => false) (z j) =
        x i - ![x j 1-1,x j 0+1,x j 2] := by
    funext k
    fin_cases k
    · change x i 0 + 1 - x j 1 = x i 0 - (x j 1-1)
      omega
    · rfl
    · rfl
  simpa only [he] using h

#print axioms canonicalFreePair_axialShift_positive
#print axioms canonicalFreePair_diagonalShift_positive
end IsingScaling.Potts.SiteBox
