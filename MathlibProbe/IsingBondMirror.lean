import MathlibProbe.IsingFiniteDomain
import MathlibProbe.IsingSpatialPacketDifferences

/-! The coordinate bond mirror at x₀=1/2 on the actual free rectangular
nearest-neighbor lattice, with the full cross-interface bond weight retained. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology BigOperators
namespace IsingScaling.BondMirror

abbrev T (L : ℕ) := ↥(Finset.Icc (-(L:ℤ)) (L:ℤ))
abbrev P (L : ℕ) := Fin (L+1) × T L × T L
abbrev V (L : ℕ) := Bool × P L

def loc {L : ℕ} (v : V L) : Site :=
  ![if v.1 then (v.2.1.val:ℤ)+1 else -(v.2.1.val:ℤ),v.2.2.1.val,v.2.2.2.val]

lemma loc_inj {L} : Function.Injective (loc (L:=L)) := by
  rintro ⟨b,i,u,v⟩ ⟨b',j,u',v'⟩ H
  have h0 := congrFun H 0
  have h1 := congrFun H 1
  have h2 := congrFun H 2
  simp only [loc,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
  have eu : u=u' := Subtype.ext h1
  have ev : v=v' := Subtype.ext h2
  subst u'; subst v'
  cases b <;> cases b' <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0
  all_goals first | (have hij : i=j := Fin.ext (by omega); subst j; rfl) | omega

lemma same_dist {L} (i j : P L) :
    latticeDistance (loc (false,i)) (loc (false,j)) =
      latticeDistance (loc (true,i)) (loc (true,j)) := by
  simp [latticeDistance,loc,Fin.sum_univ_three]; omega

lemma cross_dist {L} (b : Bool) (i j : P L) :
    latticeDistance (loc (b,i)) (loc (!b,j)) = 1 ↔ i=j ∧ i.1.val=0 := by
  constructor
  · intro H
    have h0 : i.1.val=0 ∧ j.1.val=0 ∧ i.2.1.val=j.2.1.val ∧ i.2.2.val=j.2.2.val := by
      cases b <;> simp [latticeDistance,loc,Fin.sum_univ_three] at H <;> omega
    exact ⟨Prod.ext (Fin.ext (by omega)) (Prod.ext (Subtype.ext h0.2.2.1) (Subtype.ext h0.2.2.2)),h0.1⟩
  · rintro ⟨rfl,h⟩
    cases b <;> simp [latticeDistance,loc,Fin.sum_univ_three,h]

private def spinProduct (a b : Bool) : Bool := a == b
private lemma spin_val (a b : Bool) : value (spinProduct a b) = value a * value b := by
  cases a <;> cases b <;> norm_num [value,spinProduct]
private lemma val_sq (a : Bool) : value a*value a=1 := by cases a <;> norm_num [value]

def spins {L} (η u : P L → Bool) (v : V L) : Bool :=
  if v.1 then u v.2 else spinProduct (u v.2) (η v.2)

def equivSpin {L} : (V L → Bool) ≃ (P L → Bool) × (P L → Bool) where
  toFun σ := (fun i => spinProduct (σ (true,i)) (σ (false,i)), fun i => σ (true,i))
  invFun q := spins q.1 q.2
  left_inv σ := by
    funext p
    rcases p with ⟨b,i⟩
    cases b
    · change spinProduct (σ (true,i)) (spinProduct (σ (true,i)) (σ (false,i))) = σ (false,i)
      cases σ (true,i) <;> cases σ (false,i) <;> rfl
    · rfl
  right_inv q := by
    apply Prod.ext
    · funext i
      change spinProduct (q.2 i) (spinProduct (q.2 i) (q.1 i)) = q.1 i
      cases q.2 i <;> cases q.1 i <;> rfl
    · rfl

private def J {L} (β : ℝ) (η : P L → Bool) (e : P L×P L) : ℝ :=
  if latticeDistance (loc (true,e.1)) (loc (true,e.2))=1
  then β/2*(1+value (η e.1)*value (η e.2)) else 0

private lemma J_nonneg {L} {β} (hβ : 0≤β) (η : P L → Bool) (e) : 0≤J β η e := by
  unfold J
  split_ifs
  · apply mul_nonneg (by positivity)
    cases η e.1 <;> cases η e.2 <;> norm_num [value]
  · exact le_rfl

private def seam {L} (β : ℝ) (η : P L → Bool) (i : P L) : ℝ :=
  if i.1.val=0 then β*value (η i) else 0

private def bonds (L) := Finset.univ.filter (fun e : V L×V L => latticeDistance (loc e.1) (loc e.2)=1)

lemma sum_halves {L} (f : V L → ℝ) :
    (∑ v, f v) = (∑ i : P L, f (true,i)) + ∑ i : P L, f (false,i) := by
  rw [Fintype.sum_prod_type,Fintype.sum_bool]

private lemma weight {L} (β : ℝ) (η u : P L → Bool) :
    bondWeight (bonds L) (fun _ => β/2) (spins η u) =
      Real.exp (∑ i, seam β η i) *
      Real.exp (∑ e : P L×P L, J β η e*(value (u e.1)*value (u e.2))) := by
  let a (v w : V L) := if latticeDistance (loc v) (loc w)=1 then
    β/2 * (value (spins η u v)*value (spins η u w)) else 0
  have hh (i j : P L) : a (true,i) (true,j) + a (false,i) (false,j) =
      J β η (i,j)*(value (u i)*value (u j)) := by
    simp only [a,spins,Bool.false_eq_true,ite_false,ite_true,J,same_dist,spin_val]
    split_ifs <;> ring
  have cross (i j : P L) : a (true,i) (false,j) + a (false,i) (true,j) =
      if j=i then seam β η i else 0 := by
    have h1 : latticeDistance (loc (true,i)) (loc (false,j)) = 1 ↔ i=j ∧ i.1.val=0 := cross_dist true i j
    have h2 : latticeDistance (loc (false,i)) (loc (true,j)) = 1 ↔ i=j ∧ i.1.val=0 := cross_dist false i j
    by_cases hij : j=i
    · subst j
      by_cases h : i.1.val=0
      · simp [a,spins,spin_val,h1,h2,h,seam]
        have hv := val_sq (u i); linear_combination β*value (η i)*hv
      · simp [a,h1,h2,h,seam]
    · simp [a,h1,h2,hij,Ne.symm hij]
  have rearr (i j : P L) :
      a (true,i) (true,j) + a (true,i) (false,j) +
      (a (false,i) (true,j)+a (false,i) (false,j)) =
      (if j=i then seam β η i else 0)+J β η (i,j)*(value (u i)*value (u j)) := by
    rw [← hh, ← cross]; ring
  rw [← Real.exp_add]
  apply congrArg Real.exp
  unfold bonds
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  change (∑ v, ∑ w, a v w) = _
  have hp : (∑ e : P L×P L, J β η e * (value (u e.1)*value (u e.2))) =
      ∑ i : P L, ∑ j : P L, J β η (i,j)*(value (u i)*value (u j)) := Fintype.sum_prod_type _
  rw [hp]
  simp only [sum_halves]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc _ = ∑ j, ((if j=i then seam β η i else 0)+J β η (i,j)*(value (u i)*value (u j))) :=
          Finset.sum_congr rfl fun j _ => by rw [← rearr]
       _ = _ := by simp [Finset.sum_add_distrib]

/-- Pair order across a coordinate bond plane on the exact finite induced
rectangle; occupied cross-interface bonds remain in the scalar seam factor. -/
theorem finite_same_side {L β} (hβ : 0≤β) (i j : P L) :
    volumePair β loc (true,i) (false,j) ≤ volumePair β loc (true,i) (true,j) := by
  classical
  let W (σ : V L → Bool) := bondWeight (bonds L) (fun _ => β/2) σ
  let H (σ : V L → Bool) := W σ * (value (σ (true,i)) *
    (value (σ (true,j))-value (σ (false,j))))
  have hH : 0 ≤ ∑ σ, H σ := by
    rw [← Equiv.sum_comp equivSpin.symm H, Fintype.sum_prod_type]
    apply Finset.sum_nonneg
    intro η _
    let c := (1-value (η j))*Real.exp (∑ k, seam β η k)
    have hc : 0≤c := by
      apply mul_nonneg _ (Real.exp_pos _).le
      cases η j <;> norm_num [value]
    have hterm (u : P L → Bool) : H (equivSpin.symm (η,u)) =
        c*((value (u i)*value (u j))*
          Real.exp (∑ e : P L×P L, J β η e*(value (u e.1)*value (u e.2)))) := by
      change H (spins η u) = _
      simp only [H,W,weight,spins,Bool.false_eq_true,ite_false,ite_true,spin_val,c]; ring
    simp_rw [hterm,← Finset.mul_sum]
    exact mul_nonneg hc (finite_pair_bond_sum_nonneg Finset.univ id (J β η) (J_nonneg hβ η) i j)
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  apply sub_nonneg.mp
  rw [← Finset.sum_sub_distrib]
  apply hH.trans_eq
  apply Finset.sum_congr rfl
  intro σ _
  dsimp [H,W,volumePair,bonds,bondScore]
  ring

def place {L} (x : BoxSite L) : V L := by
  have hx := x.property
  simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc] at hx
  have h0 := hx 0
  let i := if 0<x.val 0 then (x.val 0-1).toNat else (-x.val 0).toNat
  have hi : i<L+1 := by dsimp [i]; split_ifs <;> omega
  exact (decide (0<x.val 0),⟨i,hi⟩,⟨x.val 1,Finset.mem_Icc.mpr (hx 1)⟩,
    ⟨x.val 2,Finset.mem_Icc.mpr (hx 2)⟩)

lemma place_loc {L} (x : BoxSite L) : loc (place x) = x.val := by
  ext i
  fin_cases i
  · simp [loc,place]; split_ifs <;> omega
  · rfl
  · rfl

def inner (L : ℕ) : BoxSite L ↪ V L where
  toFun := place
  inj' := fun x y h => Subtype.ext <| (place_loc x).symm.trans ((congrArg loc h).trans (place_loc y))

def outer (L : ℕ) : V L ↪ BoxSite (L+1) where
  toFun p := ⟨loc p, by
    simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc]
    intro j
    obtain ⟨b,i,u,v⟩ := p
    have hi := i.isLt
    have hu := Finset.mem_Icc.mp u.property
    have hv := Finset.mem_Icc.mp v.property
    cases b <;> fin_cases j <;> simp [loc] <;> omega⟩
  inj' := fun _ _ h => loc_inj (congrArg Subtype.val h)

lemma place_pos {L} (x : BoxSite L) (hx : 0<x.val 0) : (place x).1=true := by
  simp [place,hx]

def reflected (v : Site) : Site := ![1-v 0,v 1,v 2]

lemma flip_loc {L} (j : P L) : loc (false,j) = reflected (loc (true,j)) := by
  ext a; fin_cases a <;> simp [loc,reflected]

lemma ev_cube (v : Site) : ∀ᶠ L : ℕ in atTop, v∈cube L := by
  filter_upwards [eventually_ge_atTop (∑ j, (v j).natAbs)] with L hL
  simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc]
  intro j
  have H := Finset.single_le_sum (f:=fun i => (v i).natAbs) (fun i _ => Nat.zero_le _) (mem_univ j)
  omega

/-- Infinite-volume bond-mirror comparison from genuine finite rectangular
Gibbs laws squeezed between two successive centered free cubes. -/
theorem same_side {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (x y : Site) (hx : 0<x 0) (hy : 0<y 0) :
    g (x-reflected y) ≤ g (x-y) := by
  have hG := hg.stationary_pair_limit hβ
  have hlim := (Filter.tendsto_add_atTop_iff_nat 1).mpr (hG x y)
  apply le_of_tendsto_of_tendsto (hG x (reflected y)) hlim
  filter_upwards [ev_cube x,ev_cube y,ev_cube (reflected y)] with L hX hY hY'
  let X : BoxSite L := ⟨x,hX⟩
  let Y : BoxSite L := ⟨y,hY⟩
  let Y' : BoxSite L := ⟨reflected y,hY'⟩
  let i := (place X).2
  let j := (place Y).2
  have h1 : inner L X = (true,i) := Prod.ext (place_pos X hx) rfl
  have h2 : inner L Y = (true,j) := Prod.ext (place_pos Y hy) rfl
  have h3 : inner L Y' = (false,j) := by
    apply loc_inj
    rw [show loc (inner L Y')=reflected y from place_loc _,flip_loc]
    have ho : loc (true,j)=y := by rw [← h2]; exact place_loc Y
    rw [ho]
  have hlo := volumePair_embed Subtype.val loc (inner L) (fun t => place_loc t) hβ X Y'
  have hhi := volumePair_embed loc Subtype.val (outer L) (fun _ => rfl) hβ (true,i) (true,j)
  rw [volumePair_cube,boxCorrelation_eq_freePair,h1,h3] at hlo
  rw [volumePair_cube,boxCorrelation_eq_freePair] at hhi
  change volumePair β loc (true,i) (true,j) ≤ freePair β (L+1) (loc (true,i)) (loc (true,j)) at hhi
  have hi : loc (true,i) = x := by rw [← h1]; exact place_loc X
  have hj : loc (true,j) = y := by rw [← h2]; exact place_loc Y
  rw [hi,hj] at hhi
  exact hlo.trans ((finite_same_side hβ i j).trans hhi)

/-- Unit-step transverse-uniform coordinate monotonicity of the original Gibbs
thermodynamic two-point function. No critical-temperature theorem is assumed. -/
theorem coordinate_antitone {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β) (b c : ℤ) :
    Antitone (fun k : ℕ => g ![(k:ℤ),b,c]) := by
  apply antitone_nat_of_succ_le
  intro k
  have H := same_side hg hβ ![(k:ℤ)+1,b,c] ![1,0,0] (by simp) (by norm_num)
  have h1 : (![(k:ℤ)+1,b,c]:Site)-reflected ![1,0,0] = ![((k+1:ℕ):ℤ),b,c] := by
    ext i; fin_cases i <;> simp [reflected]
  have h2 : (![(k:ℤ)+1,b,c]:Site)-![1,0,0] = ![(k:ℤ),b,c] := by
    ext i; fin_cases i <;> simp
  rwa [h1,h2] at H

private theorem product_gram {S I : Type*} [Fintype S] [DecidableEq I]
    (A B : I → ℝ) (U : I → S → ℝ) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (T : Finset I) (F : S → ℝ) :
    0 ≤ ∑ u, ∑ v, F u * F v * ∏ i ∈ T, (A i + B i * U i u * U i v) := by
  classical
  induction T using Finset.induction_on generalizing F with
  | empty =>
    simp only [Finset.prod_empty,mul_one,←Finset.mul_sum,←Finset.sum_mul]
    exact mul_self_nonneg _
  | @insert i T hi ih =>
    let K (u v : S) := ∏ a ∈ T, (A a + B a * U a u * U a v)
    let G (u : S) := F u * U i u
    have he : ∑ u, ∑ v, F u * F v * ∏ j ∈ insert i T, (A j + B j * U j u * U j v) =
        A i * (∑ u, ∑ v, F u*F v*K u v) + B i * (∑ u, ∑ v, G u*G v*K u v) := by
      simp only [Finset.prod_insert hi,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      dsimp only [K,G]; ring
    rw [he]
    exact add_nonneg (mul_nonneg (hA i) (ih F)) (mul_nonneg (hB i) (ih G))

private def halves (L : ℕ) : (V L → Bool) ≃ (P L → Bool) × (P L → Bool) where
  toFun σ := (fun i => σ (true,i), fun i => σ (false,i))
  invFun q v := if v.1 then q.1 v.2 else q.2 v.2
  left_inv σ := by funext ⟨b,i⟩; cases b <;> rfl
  right_inv q := by rcases q with ⟨u,v⟩; rfl

private def halfScore {L : ℕ} (β : ℝ) (u : P L → Bool) (e : P L × P L) : ℝ :=
  if latticeDistance (loc (true,e.1)) (loc (true,e.2)) = 1
  then β/2*(value (u e.1)*value (u e.2)) else 0

private def wallCoupling {L : ℕ} (β : ℝ) (i : P L) := if i.1.val=0 then β else 0

private theorem half_weight {L : ℕ} (β : ℝ) (u v : P L → Bool) :
    bondWeight (bonds L) (fun _ => β/2) ((halves L).symm (u,v)) =
      (Real.exp (∑ e, halfScore β u e) * Real.exp (∑ e, halfScore β v e)) *
       ∏ i, (Real.cosh (wallCoupling β i) +
         Real.sinh (wallCoupling β i) * value (u i) * value (v i)) := by
  let η i := spinProduct (u i) (v i)
  have hspin : (halves L).symm (u,v) = spins η u := by
    funext ⟨b,i⟩
    cases b <;> cases hu : u i <;> cases hv : v i <;> simp [η,halves,spins,spinProduct,hu,hv]
  have H (e : P L × P L) :
      J β η e*(value (u e.1)*value (u e.2)) = halfScore β u e + halfScore β v e := by
    simp only [J,halfScore,η,spin_val]
    split_ifs
    · cases u e.1 <;> cases u e.2 <;> cases v e.1 <;> cases v e.2 <;> norm_num [value] <;> ring
    · ring
  have Hwall (i : P L) : Real.exp (seam β η i) = Real.cosh (wallCoupling β i) +
      Real.sinh (wallCoupling β i) * value (u i) * value (v i) := by
    by_cases hi : i.1.val=0
    · cases hu : u i <;> cases hv : v i <;>
        simp [seam,η,spinProduct,wallCoupling,hi,hu,hv,value,←Real.cosh_add_sinh]
    · simp [seam,wallCoupling,hi]
  rw [hspin,weight]
  simp only [H,Finset.sum_add_distrib,Real.exp_add,Real.exp_sum,Hwall]
  ring

private theorem finite_reflection_form {L β} (hβ : 0 ≤ β) (F : (P L → Bool) → ℝ) :
    0 ≤ ∑ σ, bondWeight (bonds L) (fun _ => β/2) σ *
      (F (fun i => σ (true,i)) * F (fun i => σ (false,i))) := by
  let W (σ : V L → Bool) := bondWeight (bonds L) (fun _ => β/2) σ *
    (F (fun i => σ (true,i)) * F (fun i => σ (false,i)))
  let G (u : P L → Bool) := F u * Real.exp (∑ e, halfScore β u e)
  change 0 ≤ ∑ σ, W σ
  rw [←Equiv.sum_comp (halves L).symm W,Fintype.sum_prod_type]
  refine (product_gram (fun i : P L => Real.cosh (wallCoupling β i))
    (fun i => Real.sinh (wallCoupling β i)) (fun i u => value (u i))
    (fun i => (Real.cosh_pos _).le) (fun i => Real.sinh_nonneg_iff.mpr
      (by unfold wallCoupling; split <;> positivity)) Finset.univ G).trans_eq ?_
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  dsimp only [W]
  rw [half_weight]
  change G u * G v * _ = _ * (F u * F v)
  unfold G; ring

private theorem finite_reflected_positive {L β} (hβ : 0 ≤ β) {ι : Type*} [Fintype ι]
    (x : ι → P L) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * volumePair β loc (true,x i) (false,x j) := by
  classical
  let W (σ : V L → Bool) := bondWeight (bonds L) (fun _ => β/2) σ
  let F (u : P L → Bool) := ∑ i, c i * value (u (x i))
  have hf := finite_reflection_form hβ F
  have hz : 0 ≤ ∑ σ, W σ := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hswap (a : (V L → Bool) → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ σ, a σ i j) = ∑ σ, ∑ i, ∑ j, a σ i j := by
    calc _ = ∑ i, ∑ σ, ∑ j, a σ i j := sum_congr rfl (fun _ _ => sum_comm)
         _ = _ := sum_comm
  change 0 ≤ ∑ i, ∑ j, c i*c j * ((∑ σ, W σ *
      (value (σ (true,x i))*value (σ (false,x j)))) / ∑ σ, W σ)
  simp_rw [←mul_div_assoc,Finset.mul_sum]
  simp_rw [div_eq_mul_inv,←Finset.sum_mul]
  rw [←div_eq_mul_inv]
  apply div_nonneg _ hz
  rw [hswap]
  refine hf.trans_eq (Finset.sum_congr rfl (fun σ _ => ?_))
  change W σ * ((∑ i, c i*value (σ (true,x i))) * ∑ j, c j*value (σ (false,x j))) = _
  simp only [Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

def port (L : ℕ) (x : Site) : P L :=
  if hx : x ∈ cube L then (place (⟨x,hx⟩:BoxSite L)).2
  else (0,⟨0,by simp⟩,⟨0,by simp⟩)

private theorem port_tendsto {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (x y : Site) (hx : 0<x 0) (hy : 0<y 0) :
    Tendsto (fun L => volumePair β loc (true,port L x) (false,port L y)) atTop
      (𝓝 (g (x-reflected y))) := by
  have hG := hg.stationary_pair_limit hβ x (reflected y)
  have hboth : ∀ᶠ L : ℕ in atTop, freePair β L x (reflected y) ≤
      volumePair β loc (true,port L x) (false,port L y) ∧
      volumePair β loc (true,port L x) (false,port L y) ≤ freePair β (L+1) x (reflected y) := by
    filter_upwards [ev_cube x,ev_cube y,ev_cube (reflected y)] with L hX hY hY'
    let X : BoxSite L := ⟨x,hX⟩
    let Y : BoxSite L := ⟨y,hY⟩
    let Z : BoxSite L := ⟨reflected y,hY'⟩
    have ex : inner L X = (true,port L x) := Prod.ext (place_pos X hx)
      (by simp only [X,port,dite_eq_left hX]; rfl)
    have ey : inner L Y = (true,port L y) := Prod.ext (place_pos Y hy)
      (by simp only [Y,port,dite_eq_left hY]; rfl)
    have lx : loc (true,port L x) = x := by rw [←ex]; exact place_loc X
    have ly : loc (false,port L y) = reflected y := by
      rw [flip_loc,←ey,show loc (inner L Y) = y from place_loc Y]
    have ez : inner L Z = (false,port L y) := loc_inj ((place_loc Z).trans ly.symm)
    have hlo := volumePair_embed Subtype.val loc (inner L) (fun t => place_loc t) hβ X Z
    have hhi := volumePair_embed loc Subtype.val (outer L) (fun _ => rfl) hβ
      (true,port L x) (false,port L y)
    rw [volumePair_cube,boxCorrelation_eq_freePair,ex,ez] at hlo
    rw [volumePair_cube,boxCorrelation_eq_freePair] at hhi
    change _ ≤ freePair β (L+1) (loc (true,port L x)) (loc (false,port L y)) at hhi
    rw [lx,ly] at hhi
    exact ⟨hlo,hhi⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hG ((tendsto_add_atTop_iff_nat 1).mpr hG)
    (hboth.mono fun _ => And.left) (hboth.mono fun _ => And.right)

/-- Positive quadratic form at the bond plane x₀=1/2 for the original
ferromagnetic thermodynamic correlation. The finite representatives use
the true cross-interface bonds of the free rectangle. -/
theorem reflected_positive {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {ι : Type*} [Fintype ι] (x : ι → Site) (hx : ∀ i, 0 < x i 0) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * g (x i-reflected (x j)) := by
  have hm : Tendsto (fun L => ∑ i, ∑ j, c i*c j *
      volumePair β loc (true,port L (x i)) (false,port L (x j))) atTop
      (𝓝 (∑ i, ∑ j, c i*c j*g (x i-reflected (x j)))) :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      tendsto_const_nhds.mul (port_tendsto hg hβ (x i) (x j) (hx i) (hx j))))
  exact ge_of_tendsto' hm (fun L => finite_reflected_positive hβ (fun i => port L (x i)) c)

#print axioms reflected_positive

end IsingScaling.BondMirror

