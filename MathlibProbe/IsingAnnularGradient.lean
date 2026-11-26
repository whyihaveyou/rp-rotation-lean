import MathlibProbe.IsingBondMirror

/-! Unit-step annular gradient estimates for actual free-limit correlations.
An oblique normal and the longitudinal axis control each transverse step. -/
noncomputable section
open Finset
open scoped BigOperators
namespace IsingScaling
namespace AnnularGradient
open NormalDifference

def weight (k R : ℕ) := ((min (2*k) R:ℕ):ℝ)^3 * (k+1:ℕ)
private lemma weight_nonneg (k R) : 0≤weight k R := by unfold weight; positivity

private theorem axial_two {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R : ℕ) (hk : 0<k) (hR : 0<R) (a b c : ℤ) (ha : 4*(k:ℤ)≤a) :
    weight k R * |g ![a,b,c] - g ![a+2,b,c]| ≤ 1728*susceptibility g R := by
  let w : Site := ![a-4*(k:ℤ),b,c]
  have hu := susceptibility_difference hg hβ .axis w 0 (by simp [tip,w]; omega)
    (by simp [tip]) 1 k (2*k) R hk hR (by omega)
  have he (m : ℕ) : kernel .axis g w 0 (2*m) = g ![2*(m:ℤ)+(a-4*k),b,c] := by
    apply congrArg g; ext i; fin_cases i <;> simp [w,step,NormalDifference.refl]
  simpa only [Function.iterate_one,Packet.diff,he,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,pow_one,show 2*(2*(k:ℤ))+(a-4*k)=a by ring,
    show 2*(2*(k:ℤ)+1)+(a-4*k)=a+2 by ring,weight] using hu

private theorem diagonal_two {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R : ℕ) (hk : 0<k) (hR : 0<R) (a b c : ℤ) (hab : 8*(k:ℤ)≤a-b) :
    weight k R * |g ![a,b,c] - g ![a+2,b-2,c]| ≤ 1728*susceptibility g R := by
  let w : Site := ![a-4*(k:ℤ),b+4*k,c]
  have hu := susceptibility_difference hg hβ .faceDiagonal w 0 (by simp [tip,w]; omega)
    (by simp [tip]) 1 k (2*k) R hk hR (by omega)
  have he (m : ℕ) : kernel .faceDiagonal g w 0 (2*m) =
      g ![2*(m:ℤ)+(a-4*k),-(2*(m:ℤ))+(b+4*k),c] := by
    apply congrArg g; ext i; fin_cases i <;> simp [w,step,NormalDifference.refl]
  simpa only [Function.iterate_one,Packet.diff,he,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,pow_one,show 2*(2*(k:ℤ))+(a-4*k)=a by ring,
    show 2*(2*(k:ℤ)+1)+(a-4*k)=a+2 by ring,
    show -(2*(2*(k:ℤ)))+(b+4*k)=b by ring,
    show -(2*(2*(k:ℤ)+1))+(b+4*k)=b-2 by ring,weight] using hu

private lemma swap01 {β g} (hg : IsFreeTwoPoint β g) (a b c : ℤ) : g ![a,b,c]=g ![b,a,c] := by
  have hv : signedPerm (Equiv.swap 0 1) (fun _=>false) ![a,b,c]=![b,a,c] := by ext i; fin_cases i <;> rfl
  exact (freeLimit_signedPerm hg _ _ _).symm.trans (congrArg g hv)
private lemma swap02 {β g} (hg : IsFreeTwoPoint β g) (a b c : ℤ) : g ![a,b,c]=g ![c,b,a] := by
  have hv : signedPerm (Equiv.swap 0 2) (fun _=>false) ![a,b,c]=![c,b,a] := by ext i; fin_cases i <;> rfl
  exact (freeLimit_signedPerm hg _ _ _).symm.trans (congrArg g hv)
private lemma signY {β g} (hg : IsFreeTwoPoint β g) (a b c : ℤ) : g ![a,-b,c]=g ![a,b,c] := by
  have hv : signedPerm (Equiv.refl _) (fun i=>decide (i=1)) ![a,b,c]=![a,-b,c] := by ext i; fin_cases i <;> rfl
  exact (congrArg g hv).symm.trans (freeLimit_signedPerm hg _ _ _)

theorem longitudinal {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R : ℕ) (hk : 0<k) (hR : 0<R) (a : ℕ) (b c : ℤ) (ha : 4*k≤a) :
    weight k R * |g ![(a:ℤ),b,c] - g ![(a:ℤ)+1,b,c]| ≤ 1728*susceptibility g R := by
  let F (m : ℕ) := g ![(m:ℤ),b,c]
  have hanti : Antitone F := BondMirror.coordinate_antitone hg hβ b c
  have h1 := hanti (show a≤a+1 by omega)
  have h2 := hanti (show a+1≤a+2 by omega)
  change weight k R * |F a-F (a+1)| ≤ _
  have hh := axial_two hg hβ k R hk hR a b c (by exact_mod_cast ha)
  change weight k R * |F a-F (a+2)| ≤ _ at hh
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  rw [abs_of_nonneg (sub_nonneg.mpr (h2.trans h1))] at hh
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left h2 _) (weight_nonneg ..)).trans hh

theorem transverse {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R : ℕ) (hk : 0<k) (hR : 0<R) (a b : ℕ) (c : ℤ) (ha : 8*k≤a) :
    weight k R * |g ![(a:ℤ),(b:ℤ),c]-g ![(a:ℤ),(b:ℤ)+1,c]| ≤ 3456*susceptibility g R := by
  let F (m : ℕ) := g ![(a:ℤ),(m:ℤ),c]
  have hanti : Antitone F := by
    intro m n hmn
    exact (swap01 hg a n c).le.trans (((BondMirror.coordinate_antitone hg hβ a c hmn)).trans (swap01 hg a m c).ge)
  have h1 := hanti (show b≤b+1 by omega)
  have h2 := hanti (show b+1≤b+2 by omega)
  have hdiag := diagonal_two hg hβ k R hk hR a (-(b:ℤ)) c (by omega)
  have hax := axial_two hg hβ k R hk hR a (-((b+2:ℕ):ℤ)) c (by exact_mod_cast (show 4*k≤a by omega))
  rw [show -(b:ℤ)-2 = -((b+2:ℕ):ℤ) by omega] at hdiag
  rw [signY hg, signY hg] at hdiag hax
  change weight k R * |F b-F (b+1)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  have htri := abs_sub_le (F b) (g ![(a:ℤ)+2,((b+2:ℕ):ℤ),c]) (F (b+2))
  rw [abs_sub_comm (g ![(a:ℤ)+2,((b+2:ℕ):ℤ),c])] at htri
  have ht := mul_le_mul_of_nonneg_left htri (weight_nonneg k R)
  have hmono := mul_le_mul_of_nonneg_left (sub_le_sub_left h2 (F b)) (weight_nonneg k R)
  rw [abs_of_nonneg (sub_nonneg.mpr (h2.trans h1))] at ht
  change _ * |F b - _| ≤ _ at hdiag
  change _ * |F (b+2) - _| ≤ _ at hax
  rw [mul_add] at ht
  linarith only [hmono,ht,hdiag,hax]

private def oct (a b c : ℕ) : Site := ![(a:ℤ),(b:ℤ),(c:ℤ)]
private lemma abs_coordinates {β g} (hg : IsFreeTwoPoint β g) (x : Site) :
    g x = g (oct (x 0).natAbs (x 1).natAbs (x 2).natAbs) := by
  let s (i : Fin 3) := decide (x i<0)
  have H : signedPerm (Equiv.refl _) s x = oct (x 0).natAbs (x 1).natAbs (x 2).natAbs := by
    ext j
    have aux (j : Fin 3) : signedPerm (Equiv.refl _) s x j = ((x j).natAbs:ℤ) := by
      change (if decide (x j<0) then -(x j) else x j) = _
      rw [Int.natCast_natAbs]
      by_cases hj : x j < 0
      · simp [hj,abs_of_neg hj]
      · simp [hj,abs_of_nonneg (le_of_not_gt hj)]
    fin_cases j <;> apply aux
  exact (freeLimit_signedPerm hg _ _ x).symm.trans (congrArg g H)

private lemma first_chart {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R a b c : ℕ) (hk : 0<k) (hR : 0<R) (hfar : 8*k≤max a (max b c)) :
    weight k R * |g (oct a b c)-g (oct (a+1) b c)| ≤ 3456*susceptibility g R := by
  rcases le_or_gt (8*k) a with ha | ha
  · have H := longitudinal hg hβ k R hk hR a b c (by omega)
    have hχ := (hg.positive_cube_mass hβ).2 R
    exact H.trans (by linarith)
  rcases le_or_gt (8*k) b with hb | hb
  · change weight k R * |g ![(a:ℤ),b,c]-g ![((a+1:ℕ):ℤ),b,c]| ≤ _
    rw [swap01 hg a b c, swap01 hg (a+1:ℕ) b c]
    exact transverse hg hβ k R hk hR b a c hb
  · have hc : 8*k≤c := by omega
    change weight k R * |g ![(a:ℤ),b,c]-g ![((a+1:ℕ):ℤ),b,c]| ≤ _
    rw [swap01 hg a b c, swap01 hg (a+1:ℕ) b c,swap02 hg b a c,swap02 hg b (a+1:ℕ) c]
    exact transverse hg hβ k R hk hR c a b hc

private lemma second_chart {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R a b c : ℕ) (hk : 0<k) (hR : 0<R) (hfar : 8*k≤max a (max b c)) :
    weight k R * |g (oct a b c)-g (oct a (b+1) c)| ≤ 3456*susceptibility g R := by
  change weight k R * |g ![(a:ℤ),b,c]-g ![(a:ℤ),((b+1:ℕ):ℤ),c]| ≤ _
  rw [swap01 hg a b c,swap01 hg a (b+1:ℕ) c]
  exact first_chart hg hβ k R b a c hk hR (by omega)

private lemma third_chart {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β)
    (k R a b c : ℕ) (hk : 0<k) (hR : 0<R) (hfar : 8*k≤max a (max b c)) :
    weight k R * |g (oct a b c)-g (oct a b (c+1))| ≤ 3456*susceptibility g R := by
  change weight k R * |g ![(a:ℤ),b,c]-g ![(a:ℤ),b,((c+1:ℕ):ℤ)]| ≤ _
  rw [swap02 hg a b c,swap02 hg a b (c+1:ℕ)]
  exact first_chart hg hβ k R c b a hk hR (by omega)

/-- A uniform bound for every nearest-neighbor increment on the actual lattice,
with a single lattice site of slack at the inner edge of the chart. -/
theorem adjacent {β g} (hg : IsFreeTwoPoint β g) (hβ : 0≤β) (k R : ℕ)
    (hk : 0<k) (hR : 0<R) (x y : Site) (hxy : latticeDistance x y=1)
    (hfar : ∃ i, 8*k+1≤(x i).natAbs) :
    weight k R * |g x-g y| ≤ 3456*susceptibility g R := by
  have H : 8*k+1 ≤ max (x 0).natAbs (max (x 1).natAbs (x 2).natAbs) := by
    rcases hfar with ⟨i,hi⟩; fin_cases i
    · exact hi.trans (le_max_left _ _)
    · exact hi.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact hi.trans ((le_max_right _ _).trans (le_max_right _ _))
  simp only [latticeDistance, Fin.sum_univ_three] at hxy
  let a := (x 0).natAbs
  let b := (x 1).natAbs
  let c := (x 2).natAbs
  let d := (y 0).natAbs
  let e := (y 1).natAbs
  let f := (y 2).natAbs
  have cmp (i : Fin 3) :
      (x i).natAbs ≤ (y i).natAbs + (x i-y i).natAbs ∧
      (y i).natAbs ≤ (x i).natAbs + (x i-y i).natAbs := by omega
  have h0 := cmp 0
  have h1 := cmp 1
  have h2 := cmp 2
  have hcases : (a=d ∧ b=e ∧ c=f) ∨ (a+1=d ∧ b=e ∧ c=f) ∨ (d+1=a ∧ b=e ∧ c=f) ∨
      (a=d ∧ b+1=e ∧ c=f) ∨ (a=d ∧ e+1=b ∧ c=f) ∨
      (a=d ∧ b=e ∧ c+1=f) ∨ (a=d ∧ b=e ∧ f+1=c) := by
    dsimp only [a,b,c,d,e,f]; omega
  rw [abs_coordinates hg x,abs_coordinates hg y]
  change weight k R * |g (oct a b c)-g (oct d e f)| ≤ _
  change 8*k+1 ≤ max a (max b c) at H
  rcases hcases with h|h|h|h|h|h|h
  · rw [h.1,h.2.1,h.2.2,sub_self,abs_zero,mul_zero]
    exact mul_nonneg (by norm_num) ((hg.positive_cube_mass hβ).2 R).le
  · rw [← h.1, ← h.2.1, ← h.2.2]; exact first_chart hg hβ k R a b c hk hR (by omega)
  · rw [← h.1, h.2.1,h.2.2,abs_sub_comm]; exact first_chart hg hβ k R d e f hk hR (by omega)
  · rw [← h.1, ← h.2.1, ← h.2.2]; exact second_chart hg hβ k R a b c hk hR (by omega)
  · rw [h.1, ← h.2.1, h.2.2,abs_sub_comm]; exact second_chart hg hβ k R d e f hk hR (by omega)
  · rw [← h.1, ← h.2.1, ← h.2.2]; exact third_chart hg hβ k R a b c hk hR (by omega)
  · rw [h.1, h.2.1, ← h.2.2,abs_sub_comm]; exact third_chart hg hβ k R d e f hk hR (by omega)

end AnnularGradient
end IsingScaling
