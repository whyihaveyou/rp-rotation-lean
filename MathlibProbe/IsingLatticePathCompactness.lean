import MathlibProbe.IsingAnnularCompactness

/-! Coordinate telescoping on the actual lattice mesh. -/
noncomputable section
open Set Filter
open scoped Topology
namespace IsingScaling.Packet

private lemma int_line_bound (F : ℤ → ℝ) (a b : ℤ) (C : ℝ)
    (h : ∀ j ∈ Icc (min a b) (max a b), dist (F j) (F (j+1)) ≤ C) :
    dist (F a) (F b) ≤ |(a:ℝ)-(b:ℝ)| * C := by
  have aux (l u : ℤ) (hlu : l≤u)
      (hs : ∀ j ∈ Icc l u, dist (F j) (F (j+1)) ≤ C) : dist (F l) (F u) ≤ ((u:ℝ)-l)*C := by
    have H (m : ℕ) : l+(m:ℤ)≤u → dist (F l) (F (l+(m:ℤ))) ≤ (m:ℝ)*C := by
      induction m with
      | zero => simp
      | succ m ih =>
        intro hm
        have h₀ : l+(m:ℤ)≤u := by omega
        have h₁ := hs (l+(m:ℤ)) ⟨by omega,h₀⟩
        have ht := dist_triangle (F l) (F (l+(m:ℤ))) (F (l+(m:ℤ)+1))
        rw [Nat.cast_succ, Nat.cast_succ, ←add_assoc]
        nlinarith [ih h₀]
    have he : (((u-l).toNat:ℕ):ℤ)=u-l := Int.toNat_of_nonneg (sub_nonneg.mpr hlu)
    have hev : (((u-l).toNat:ℕ):ℝ)=(u:ℝ)-l := by exact_mod_cast he
    simpa only [he,hev,add_sub_cancel] using H (u-l).toNat (by omega)
  rcases le_total a b with hab|hab
  · have H := aux a b hab (by simpa [min_eq_left hab,max_eq_right hab] using h)
    have hh : (a:ℝ)≤b := by exact_mod_cast hab
    simpa [abs_of_nonpos (sub_nonpos.mpr hh)] using H
  · have H := aux b a hab (by simpa [min_eq_right hab,max_eq_left hab] using h)
    have hh : (b:ℝ)≤a := by exact_mod_cast hab
    simpa [abs_of_nonneg (sub_nonneg.mpr hh),dist_comm (F a)] using H

private def boxWord (k l : Site) (i : Fin 3) (z : ℤ) : Site := fun j =>
  if j < i then l j else if j = i then z else k j

/-- The monotone coordinate path never leaves the smallest axis-aligned
box joining the two integer sites. -/
theorem grid_box_telescoping (F : Site → ℝ) (k l : Site) (C : ℝ)
    (hs : ∀ z : Site, (∀ j, z j ∈ Icc (min (k j) (l j)) (max (k j) (l j))) →
      ∀ i, dist (F z) (F (Function.update z i (z i+1))) ≤ C) :
    dist (F k) (F l) ≤ (∑ i, |(k i:ℝ)-(l i:ℝ)|)*C := by
  let p := boxWord k l
  have hh (i : Fin 3) :
      dist (F (p i (k i))) (F (p i (l i))) ≤ |(k i:ℝ)-(l i:ℝ)| * C := by
    apply int_line_bound (fun z => F (p i z)) (k i) (l i) C
    intro u hu
    have hb (j : Fin 3) : p i u j ∈ Icc (min (k j) (l j)) (max (k j) (l j)) := by
      dsimp only [p,boxWord]
      split_ifs with h hi
      · exact ⟨min_le_right ..,le_max_right ..⟩
      · exact hi ▸ hu
      · exact ⟨min_le_left ..,le_max_left ..⟩
    have he : Function.update (p i u) i (p i u i+1) = p i (u+1) := by
      funext j
      by_cases hij : j=i
      · subst j; simp [p,boxWord]
      · simp [p,boxWord,hij]
    exact he ▸ hs _ hb i
  have h0 : p 0 (k 0) = k := by ext j; fin_cases j <;> rfl
  have h1 : p 1 (k 1) = p 0 (l 0) := by ext j; fin_cases j <;> rfl
  have h2 : p 2 (k 2) = p 1 (l 1) := by ext j; fin_cases j <;> rfl
  have h3 : p 2 (l 2) = l := by ext j; fin_cases j <;> rfl
  have hA := hh 0; have hB := hh 1; have hC := hh 2
  rw [h0] at hA
  rw [h1] at hB
  rw [h2,h3] at hC
  rw [Fin.sum_univ_three]
  linarith [dist_triangle (F k) (F (p 0 (l 0))) (F (p 1 (l 1))),
    dist_triangle (F k) (F (p 1 (l 1))) (F l)]

private theorem grid_between {a b z : ℤ} {q r δ : ℝ} (hr : 0<r)
    (hz : z ∈ Icc (min a b) (max a b))
    (ha : |(a:ℝ)/r-q| < δ) (hb : |(b:ℝ)/r-q| < δ) : |(z:ℝ)/r-q| < δ := by
  have A := abs_lt.mp ha
  have B := abs_lt.mp hb
  refine abs_lt.mpr ?_
  rcases le_total a b with hab|hab
  · have H : a ≤ z ∧ z ≤ b := by simpa [min_eq_left hab,max_eq_right hab] using hz
    have hl : (a:ℝ)/r ≤ (z:ℝ)/r := by gcongr; exact_mod_cast H.1
    have hu : (z:ℝ)/r ≤ (b:ℝ)/r := by gcongr; exact_mod_cast H.2
    constructor <;> linarith
  · have H : b ≤ z ∧ z ≤ a := by simpa [min_eq_right hab,max_eq_left hab] using hz
    have hl : (b:ℝ)/r ≤ (z:ℝ)/r := by gcongr; exact_mod_cast H.1
    have hu : (z:ℝ)/r ≤ (a:ℝ)/r := by gcongr; exact_mod_cast H.2
    constructor <;> linarith

/-- Macroscopic compactness from bounds on physical primitive lattice
edges. Coordinatewise control of the neighborhood ensures the
telescoping path remains inside the region where that bound holds. -/
theorem extract_of_coordinate_bounds {g : Site → ℝ} {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (hval : ∀ x : Space, x ≠ 0 → ∃ B : ℝ, ∀ᶠ n in atTop,
      ‖normalization g (R n)*g (gridIndex (R n) x)‖ ≤ B)
    (hgrad : ∀ x : Space, x ≠ 0 → ∃ r C : ℝ, 0<r ∧ 0≤C ∧ ∀ᶠ n in atTop,
      ∀ z : Site, (∀ j, |(scaledSite (R n) z) j-x j| < r) → ∀ i : Fin 3,
        dist (normalization g (R n)*g z) (normalization g (R n)*g (Function.update z i (z i+1)))
          ≤ C/(R n:ℝ)) :
    ∃ (u : ℕ → ℕ) (f : Space → ℝ), StrictMono u ∧ OffOriginLimit g (R ∘ u) f := by
  apply extract_of_site_oscillation hR hval
  intro x hx ε he
  obtain ⟨r,C,hr,hC,hgrad'⟩ := hgrad x hx
  let δ := min r (ε/(8*(C+1)))
  have hδ : 0<δ := lt_min hr (by positivity)
  have hδr : δ≤r := min_le_left .. 
  have hδε := (le_div_iff₀ (show 0<8*(C+1) by positivity)).mp (min_le_right r (ε/(8*(C+1))))
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hR.eventually_ge_atTop 1,hgrad'] with n hn hG
  intro k l hk hl
  let t : ℝ := R n
  have ht : 0<t := by dsimp [t]; exact_mod_cast (show 0<R n by omega)
  have hc (a : Site) (ha : dist (scaledSite (R n) a) x < δ) (i : Fin 3) :
      |(a i:ℝ)/t-x i| < δ := (PiLp.norm_apply_le (scaledSite (R n) a-x) i).trans_lt (by
        simpa only [dist_eq_norm] using ha)
  have hlength (i : Fin 3) : |(k i:ℝ)-(l i:ℝ)| ≤ 2*δ*t := by
    apply (div_le_iff₀ ht).mp
    rw [←abs_of_pos ht,←abs_div,sub_div]
    have hl' := hc l hl i
    rw [abs_sub_comm] at hl'
    exact (abs_sub_le _ (x i) _).trans (by linarith [hc k hk i])
  have hs := grid_box_telescoping (fun z => normalization g (R n)*g z) k l (C/t)
    (fun z hz => hG z (fun j => (grid_between ht (hz j) (hc k hk j) (hc l hl j)).trans_le hδr))
  calc
    _ ≤ _ := hs
    _ ≤ (6*δ*t)*(C/t) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg hC ht.le)
      rw [Fin.sum_univ_three]
      linarith [hlength 0,hlength 1,hlength 2]
    _ = 6*δ*C := by field_simp
    _ < ε := by
      change δ*(8*(C+1)) ≤ ε at hδε
      nlinarith [mul_nonneg hδ.le hC]

#print axioms extract_of_coordinate_bounds
end IsingScaling.Packet
