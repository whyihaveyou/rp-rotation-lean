import MathlibProbe.IsingFreePairLimit

/-! Reflection comparisons and annular estimates for the physical free Gibbs
two-point function. The site-mirror folding retains the wall spins. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators Topology
namespace IsingScaling

theorem thermodynamic_even_axis_antitone {β : ℝ} (hβ : 0≤β) :
    Antitone (fun n : ℕ => thermodynamicTwoPoint β ![(2*(n:ℤ)),0,0]) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := axis_evenPacket_completeMonotone (thermodynamicTwoPoint_stationary hβ)
    (fun _ : Unit => (1:ℝ)) (fun _ => 0) (fun _ => 0) 1 n
  simpa [Function.iterate_one, Packet.diff, evenPacket, sub_nonneg] using h

namespace BoxSiteMirror
variable {L : ℕ} (M : BoxSiteMirror L)

abbrev ClosedSite := {x : BoxSite L // 0 ≤ M.tip x}

def fold (x : BoxSite L) : M.ClosedSite :=
  if hx : 0 ≤ M.tip x then ⟨x,hx⟩ else ⟨M.refl x, by rw [M.neg]; omega⟩

lemma fold_refl (x : BoxSite L) : M.fold (M.refl x) = M.fold x := by
  apply Subtype.ext
  by_cases hx : M.tip x = 0
  · rw [M.wall x hx]
  by_cases hpos : 0 < M.tip x
  · simp [fold,M.neg,M.invol, hpos.le, not_le.mpr hpos]
  · have hneg : M.tip x < 0 := by omega
    simp [fold,M.neg,not_le.mpr hneg,hneg.le]

private def prodSign (a b : Bool) : Bool := (a == b)

private lemma value_prodSign (a b : Bool) : value (prodSign a b) = value a * value b := by
  cases a <;> cases b <;> norm_num [value, prodSign]

def flipSign (η : M.Half) (x : BoxSite L) : Bool :=
  if hx : M.tip x < 0 then η ⟨M.refl x, by rw [M.neg]; omega⟩ else true

def gaugeSpin (u : M.ClosedSite → Bool) (η : M.Half) (x : BoxSite L) : Bool :=
  prodSign (u (M.fold x)) (M.flipSign η x)

def gaugeEquiv : Spin L ≃ M.Half × (M.ClosedSite → Bool) where
  toFun σ := (fun z => prodSign (σ z) (σ (M.refl z)), fun z => σ z)
  invFun q := M.gaugeSpin q.2 q.1
  left_inv σ := by
    funext x
    by_cases hx : 0 ≤ M.tip x
    · simp [gaugeSpin,fold,flipSign,hx,not_lt.mpr hx,prodSign]
    · have hn : M.tip x < 0 := by omega
      simp only [gaugeSpin,fold,flipSign,dite_eq_right hx,dite_eq_left hn,M.invol]
      cases σ (M.refl x) <;> cases σ x <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext z
      have hz := z.property
      simp only [gaugeSpin,fold,flipSign,M.neg,M.invol,dite_eq_left hz.le,
        dite_eq_right (not_lt.mpr hz.le),dite_eq_right (not_le.mpr (neg_lt_zero.mpr hz)),
        dite_eq_left (neg_lt_zero.mpr hz)]
      cases q.2 ⟨z,hz.le⟩ <;> cases q.1 z <;> rfl
    · funext z
      simp [gaugeSpin,fold,flipSign,z.property,not_lt.mpr z.property,prodSign]

private def effective (η : M.Half) (β : ℝ) (e : BoxSite L × BoxSite L) : ℝ :=
  if latticeDistance e.1 e.2 = 1 then (β/4) *
    (value (M.flipSign η e.1)*value (M.flipSign η e.2) +
      value (M.flipSign η (M.refl e.1))*value (M.flipSign η (M.refl e.2))) else 0

private lemma effective_nonneg (η : M.Half) {β : ℝ} (hβ : 0 ≤ β) (e : BoxSite L × BoxSite L) :
    0 ≤ M.effective η β e := by
  unfold effective
  split_ifs with he
  · apply mul_nonneg (by positivity)
    have aux (x y : BoxSite L) : -1 ≤ value (M.flipSign η x)*value (M.flipSign η y) := by
      cases M.flipSign η x <;> cases M.flipSign η y <;> norm_num [value]
    have hf (x : BoxSite L) (hx : 0≤M.tip x) : M.flipSign η x = true := by
      simp [flipSign,not_lt.mpr hx]
    by_cases h : 0 ≤ M.tip e.1 ∧ 0 ≤ M.tip e.2
    · rw [hf _ h.1,hf _ h.2]
      rw [show value true = (1:ℝ) by rfl]; linarith [aux (M.refl e.1) (M.refl e.2)]
    · have hxy : latticeDistance e.2 e.1 = latticeDistance e.1 e.2 := by
        unfold latticeDistance
        apply sum_congr rfl
        intro i _
        rw [show e.2.val i - e.1.val i = -(e.1.val i-e.2.val i) by omega, Int.natAbs_neg]
      have h1 := M.separated e.1 e.2
      have h2 := M.separated e.2 e.1
      rw [hxy] at h2
      have hx : 0≤M.tip (M.refl e.1) := by rw [M.neg]; omega
      have hy : 0≤M.tip (M.refl e.2) := by rw [M.neg]; omega
      rw [hf _ hx,hf _ hy]
      rw [show value true = (1:ℝ) by rfl]; linarith [aux e.1 e.2]
  · exact le_rfl

private def foldedPair (u : M.ClosedSite → Bool) (e : BoxSite L × BoxSite L) : ℝ :=
  value (u (M.fold e.1))*value (u (M.fold e.2))

private theorem gaugeWeight (u : M.ClosedSite → Bool) (η : M.Half) (β : ℝ) :
    gibbsWeight β L (M.gaugeSpin u η) =
      Real.exp (∑ e : BoxSite L × BoxSite L, M.effective η β e * M.foldedPair u e) := by
  let a (x y : BoxSite L) := if latticeDistance x y = 1 then
    value (M.gaugeSpin u η x)*value (M.gaugeSpin u η y) else 0
  have hsum : (∑ x, ∑ y, a (M.refl x) (M.refl y)) = ∑ x, ∑ y, a x y := by
    simp_rw [fun x => Equiv.sum_comp M.refl (a (M.refl x))]
    exact Equiv.sum_comp M.refl (fun x => ∑ y, a x y)
  have he (x y : BoxSite L) :
      M.effective η β (x,y)*M.foldedPair u (x,y) = (β/4)*(a x y + a (M.refl x) (M.refl y)) := by
    dsimp [effective,foldedPair,a,gaugeSpin]
    simp only [M.dist,M.fold_refl,value_prodSign]
    split_ifs <;> ring
  unfold gibbsWeight interaction
  congr 1
  rw [Fintype.sum_prod_type]
  simp_rw [he, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  change β*((∑ x, ∑ y, a x y)/2) = β/4 * _
  ring

/-- Same-side Gibbs correlation dominates its reflected endpoint. Both spins
can lie on the wall. The statement is for an actual free cubic Gibbs law. -/
theorem same_side_pair_ge {β : ℝ} (hβ : 0≤β) (x y : BoxSite L)
    (hx : 0≤M.tip x) (hy : 0≤M.tip y) :
    boxCorrelation β L x (M.refl y) ≤ boxCorrelation β L x y := by
  classical
  let H (σ : Spin L) := gibbsWeight β L σ * value (σ x) * (value (σ y)-value (σ (M.refl y)))
  have hH : 0 ≤ ∑ σ : Spin L, H σ := by
    rw [← Equiv.sum_comp M.gaugeEquiv.symm H, Fintype.sum_prod_type]
    apply Finset.sum_nonneg
    intro η _
    let d := 1-value (M.flipSign η (M.refl y))
    have hd : 0 ≤ d := by
      dsimp only [d]; cases M.flipSign η (M.refl y) <;> norm_num [value]
    have hpos (u : M.ClosedSite → Bool) (z : BoxSite L) (hz : 0≤M.tip z) :
        value (M.gaugeSpin u η z) = value (u (M.fold z)) := by
      simp [gaugeSpin, flipSign, not_lt.mpr hz, prodSign]
    have hterm (u : M.ClosedSite → Bool) : H (M.gaugeEquiv.symm (η,u)) =
        d*((value (u (M.fold x))*value (u (M.fold y))) *
          Real.exp (∑ e : BoxSite L × BoxSite L, M.effective η β e * M.foldedPair u e)) := by
      change H (M.gaugeSpin u η) = _
      dsimp only [H]
      rw [M.gaugeWeight,hpos u x hx,hpos u y hy]
      simp only [gaugeSpin,value_prodSign,M.fold_refl,d]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    exact mul_nonneg hd (finite_pair_bond_sum_nonneg Finset.univ
      (fun e : BoxSite L × BoxSite L => (M.fold e.1,M.fold e.2)) (M.effective η β)
      (M.effective_nonneg η hβ) (M.fold x) (M.fold y))
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  apply sub_nonneg.mp
  rw [← Finset.sum_sub_distrib]
  apply hH.trans_eq
  apply Finset.sum_congr rfl
  intro σ _
  dsimp [H]
  ring

end BoxSiteMirror

private lemma eventually_in_cube (x : Site) : ∀ᶠ L : ℕ in atTop, x ∈ cube L := by
  filter_upwards [eventually_ge_atTop (∑ j, (x j).natAbs)] with L hL
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _) (mem_univ i)
  omega

theorem IsFreePairLimit.same_side_pair_ge {β G} (hG : IsFreePairLimit β G) (hβ : 0≤β)
    (t : Site → ℤ) (r : Site → Site) (M : ∀ L, BoxSiteMirror L)
    (ht : ∀ L (z : BoxSite L), (M L).tip z = t z)
    (hr : ∀ L (z : BoxSite L), ((M L).refl z).val = r z)
    (x y : Site) (hx : 0≤t x) (hy : 0≤t y) : G x (r y) ≤ G x y := by
  apply le_of_tendsto_of_tendsto (hG _ _) (hG _ _)
  filter_upwards [eventually_in_cube x, eventually_in_cube y] with L hL hL'
  let X : BoxSite L := ⟨x,hL⟩
  let Y : BoxSite L := ⟨y,hL'⟩
  have hX : 0≤(M L).tip X := (ht _ _).symm ▸ hx
  have hY : 0≤(M L).tip Y := (ht _ _).symm ▸ hy
  simpa only [boxCorrelation_eq_freePair,hr,X,Y] using (M L).same_side_pair_ge hβ X Y hX hY

private lemma swap01_vec (x y z : ℤ) :
    signedPerm (Equiv.swap 0 1) (fun _ => false) ![x,y,z] = ![y,x,z] := by
  funext i
  fin_cases i <;> rfl

private lemma swap12_vec (x y z : ℤ) :
    signedPerm (Equiv.swap 1 2) (fun _ => false) ![x,y,z] = ![x,z,y] := by
  funext i
  fin_cases i <;> rfl

private lemma axis_refl_vec (x y z : ℤ) :
    signedPerm (Equiv.refl _) (fun i => decide (i=0)) ![x,y,z] = ![-x,y,z] := by
  funext i
  fin_cases i <;> rfl

private lemma vec_sub (a b c d e f : ℤ) :
    (![a,b,c]:Site)-![d,e,f] = ![a-d,b-e,c-f] := by
  funext i; fin_cases i <;> rfl

/-- Folding a nonnegative pair of horizontal displacements toward a single
axis only decreases the true free-limit two-point function. -/
theorem IsFreeTwoPoint.diagonal_fold {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {a b : ℤ} (ha : 0≤a) (hb : 0≤b) (c : ℤ) :
    g ![a+b,0,c] ≤ g ![a,b,c] := by
  have h := (hg.stationary_pair_limit hβ).same_side_pair_ge hβ
    (fun v => v 0-v 1) (signedPerm (Equiv.swap 0 1) (fun _ => false))
    diagonalSiteMirror (fun _ _ => rfl) (fun _ _ => rfl)
    ![a,0,0] ![0,-b,-c] (by simpa using ha) (by simpa using hb)
  change g (![a,0,0] - _) ≤ g (![a,0,0] - ![0,-b,-c]) at h
  simpa only [swap01_vec,vec_sub,zero_sub,sub_zero,sub_neg_eq_add,neg_neg,zero_add] using h

/-- The axis comparison two steps at a time includes both parity classes. -/
theorem IsFreeTwoPoint.axis_extend {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {l m : ℤ} (hl : 0≤l) (hm : 0≤m) : g ![l+2*m,0,0] ≤ g ![l,0,0] := by
  have h := (hg.stationary_pair_limit hβ).same_side_pair_ge hβ
    (fun v => v 0) (signedPerm (Equiv.refl _) (fun i => decide (i=0)))
    axisSiteMirror (fun _ _ => rfl) (fun _ _ => rfl)
    ![l+m,0,0] ![m,0,0] (by simpa using add_nonneg hl hm) hm
  change g (![l+m,0,0] - _) ≤ g (![l+m,0,0] - ![m,0,0]) at h
  simpa only [axis_refl_vec,vec_sub,sub_neg_eq_add,sub_self,add_sub_cancel_right,
    show l+m+m=l+2*m by ring] using h

/-- Manhattan axial lower envelope in a positive octant. -/
theorem IsFreeTwoPoint.axis_lower_envelope {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {a b c : ℤ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    g ![a+b+c,0,0] ≤ g ![a,b,c] := by
  have hs : g ![a+b,c,0] = g ![a+b,0,c] := by
    simpa only [swap12_vec] using freeLimit_signedPerm hg (Equiv.swap 1 2)
      (fun _ => false) ![a+b,0,c]
  exact ((hg.diagonal_fold hβ (add_nonneg ha hb) hc 0).trans_eq hs).trans (hg.diagonal_fold hβ ha hb c)

/-- Count an octant sublattice with the prescribed parity. All its
correlations dominate the axial value, by two site folds and the axial
same-parity comparison. -/
theorem IsFreeTwoPoint.axial_mass_count {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (m k R : ℕ) (hk : 6*m+1≤k) (hR : 2*m+1≤R) :
    ((m+1:ℕ):ℝ)^3 * g ![(k:ℤ),0,0] ≤ susceptibility g R := by
  classical
  let I := Fin 3 → Fin (m+1)
  let z (i : I) (j : Fin 3) : ℤ :=
    2*((i j).val:ℤ) + (if j=0 then ((k%2:ℕ):ℤ) else 0)
  let e : I ↪ Site := ⟨z, by
    intro i i' hz
    funext j
    apply Fin.ext
    have h := congrFun hz j
    dsimp only [z] at h
    omega⟩
  have hem (i : I) : e i ∈ cube R := by
    simp only [cube,Fintype.mem_piFinset,Finset.mem_Icc]
    intro j
    have hi := (i j).isLt
    change -(R:ℤ) ≤ z i j ∧ z i j ≤ (R:ℤ)
    dsimp only [z]
    split_ifs <;> omega
  have hh (i : I) : g ![(k:ℤ),0,0] ≤ g (e i) := by
    have ha := (i 0).isLt
    have hb := (i 1).isLt
    have hc := (i 2).isLt
    let d : ℤ := (k/2:ℕ) - ((i 0).val:ℤ) - ((i 1).val:ℤ) - ((i 2).val:ℤ)
    have hd : 0≤d := by dsimp [d]; omega
    have hz (j : Fin 3) : 0 ≤ z i j := by dsimp [z]; split_ifs <;> omega
    have hz' : e i = ![z i 0,z i 1,z i 2] := by funext j; fin_cases j <;> rfl
    have H := hg.axis_extend hβ (add_nonneg (add_nonneg (hz 0) (hz 1)) (hz 2)) hd
    have hsum : z i 0 + z i 1 + z i 2 + 2*d = (k:ℤ) := by simp [z,d]; omega
    rw [hsum] at H
    rw [hz']
    exact H.trans (hg.axis_lower_envelope hβ (hz 0) (hz 1) (hz 2))
  have hpos := (hg.positive_cube_mass hβ).1
  calc _ = ∑ _i : I, g ![(k:ℤ),0,0] := by simp [I, nsmul_eq_mul]
       _ ≤ ∑ i : I, g (e i) := Finset.sum_le_sum fun i _ => hh i
       _ = ∑ x ∈ Finset.univ.map e, g x := by simp
       _ ≤ susceptibility g R := Finset.sum_le_sum_of_subset_of_nonneg
           (fun x hx => by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx; exact hem i)
           (fun x _ _ => hpos x)

/-- Actual all-scale cube estimate with a universal numerical constant. -/
theorem IsFreeTwoPoint.axial_susceptibility_density {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R : ℕ) (hk : 0<k) (hR : 0<R) :
    ((min k R:ℕ):ℝ)^3 * g ![(k:ℤ),0,0] ≤ 216 * susceptibility g R := by
  let s := min k R
  let m := (s-1)/6
  have hs : 0<s := lt_min hk hR
  have hsk : s≤k := min_le_left _ _
  have hsR : s≤R := min_le_right _ _
  have hm : s≤6*(m+1) := by dsimp [m]; omega
  have hm' : (s:ℝ) ≤ 6*((m+1:ℕ):ℝ) := by exact_mod_cast hm
  have HC := hg.axial_mass_count hβ m k R (by dsimp [m]; omega) (by dsimp [m]; omega)
  have hgp := (hg.positive_cube_mass hβ).1 ![(k:ℤ),0,0]
  calc _ ≤ (6*((m+1:ℕ):ℝ))^3 * g ![(k:ℤ),0,0] :=
         mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hm' _) hgp
       _ = 216 * (((m+1:ℕ):ℝ)^3 * g ![(k:ℤ),0,0]) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left HC (by norm_num)

private lemma tangential_sign_vec (x y z : ℤ) :
    signedPerm (Equiv.refl _) (fun i => decide (i≠0)) ![x,y,z] = ![x,-y,-z] := by
  funext i; fin_cases i <;> rfl

/-- A two-site reflected packet bounds a general transverse displacement
by the arithmetic mean of the two axial self-correlations. -/
theorem IsFreeTwoPoint.axis_packet_upper {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    {l n : ℤ} (hl : 0≤l) (hn : 0≤n) (b c : ℤ) :
    2*g ![l+n,b,c] ≤ g ![2*l,0,0] + g ![2*n,0,0] := by
  let X : Fin 2 → Site := ![![l,b,c], ![n,0,0]]
  let C : Fin 2 → ℝ := ![1,-1]
  have H := (hg.stationary_pair_limit hβ).axis_reflected_positive X
    (fun i => by fin_cases i; exact hl; exact hn) C
  change 0 ≤ ∑ i, ∑ j, C i*C j * g (X i - signedPerm _ _ (X j)) at H
  have hsign : g ![n+l,-b,-c] = g ![l+n,b,c] := by
    rw [add_comm n l]
    simpa only [tangential_sign_vec] using freeLimit_signedPerm hg (Equiv.refl _)
      (fun i => decide (i≠0)) ![l+n,b,c]
  simp only [Fin.sum_univ_two, C,X, Matrix.cons_val_zero, Matrix.cons_val_one,
    axis_refl_vec,vec_sub,sub_neg_eq_add,sub_zero,zero_sub,sub_self,
    ← two_mul,hsign,one_mul,neg_mul,mul_neg,neg_neg] at H
  linarith

/-- Uniform macroscopic point bound in each coordinate chart of the cube.
The two signed-permutation parameters range over all choices of axial
coordinate and its orientation. -/
theorem IsFreeTwoPoint.site_susceptibility_density {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R : ℕ) (hk : 2≤k) (hR : 0<R) (b c : ℤ)
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ((min k R:ℕ):ℝ)^3 * g (signedPerm p s ![(k:ℤ),b,c]) ≤ 1728 * susceptibility g R := by
  rw [freeLimit_signedPerm hg]
  let n : ℕ := k/2
  let d : ℕ := k%2
  have hkn : (n:ℤ)+(n+d)=k := by dsimp [n,d]; omega
  have hh := hg.axis_packet_upper hβ (show 0≤(n:ℤ) by positivity) (show 0≤(n:ℤ)+d by positivity) b c
  have hmore := hg.axis_extend hβ (show 0≤2*(n:ℤ) by positivity) (show 0≤(d:ℤ) by positivity)
  rw [← show 2*((n:ℤ)+d)=2*n+2*d by ring] at hmore
  rw [hkn] at hh
  have hle : g ![(k:ℤ),b,c] ≤ g ![2*(n:ℤ),0,0] := by linarith
  have hn : 0<2*n := by dsimp [n]; omega
  have hmin : min k R ≤ 2*min (2*n) R := by dsimp [n]; omega
  have hmin' : ((min k R:ℕ):ℝ) ≤ 2*((min (2*n) R:ℕ):ℝ) := by exact_mod_cast hmin
  have hax := hg.axial_susceptibility_density hβ (2*n) R hn hR
  push_cast at hax
  have hgp := (hg.positive_cube_mass hβ).1 ![(k:ℤ),b,c]
  calc _ ≤ (2*((min (2*n) R:ℕ):ℝ))^3 * g ![2*(n:ℤ),0,0] :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hmin' _) hle hgp (by positivity)
       _ = 8 * (((min (2*n) R:ℕ):ℝ)^3 * g ![2*(n:ℤ),0,0]) := by ring
       _ ≤ _ := by push_cast; linarith

end IsingScaling
