import MathlibProbe.IsingAxialMomentPropagation

/-! A lower bound on the normalized axial spin correlation from the mass
of the actual dyadic susceptibility shell. -/
noncomputable section
open Filter
open scoped Topology
namespace IsingScaling
open Packet

/-- At every sufficiently large radius where the shell has relative mass
at least ε, its lower axial endpoint carries normalized correlation at
least ε/250. No growth limit is assumed for the susceptibility. -/
theorem IsFreeTwoPoint.eventually_shell_axial_floor {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in atTop,
      1 + ε ≤ susceptibility g (2*R) / susceptibility g R →
      c ≤ normalization g R * g (Pi.single 0 ((2*(R/2) : ℕ) : ℤ)) := by
  classical
  refine ⟨ε/250, by positivity, ?_⟩
  have ha := hg.axial_antitone hβ
  obtain ⟨hg0, hχ⟩ := hg.positive_cube_mass hβ
  have hlim := hg.susceptibility_shell_radial_axis hβ 2 (by decide)
  filter_upwards [hlim.eventually_lt_const (show (0:ℝ) < ε/2 by positivity),
      eventually_ge_atTop 1] with r hsmall hr
  intro hshell
  let S := cube (2*r) \ cube r
  let y : Site := Pi.single 0 ((2*(r/2) : ℕ) : ℤ)
  have hsum : (∑ x ∈ S, g (radialAxisSite x)) ≤
      125*(r:ℝ)^3*g y := by
    calc
      _ ≤ ∑ _x ∈ S, g y := by
        apply Finset.sum_le_sum
        intro x hx
        have hrx := siteRadius_outside (Finset.mem_sdiff.mp hx).2
        have ht : 2*(r/2) ≤ r := by omega
        have hd := ha (le_trans ht (Nat.le_floor hrx))
        have hx0 : 0 ≤ siteRadius x := norm_nonneg _
        simpa only [y,radialAxisSite,Int.natCast_floor_eq_floor hx0] using hd
      _ = (S.card:ℝ) * g y := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (hg0 y)
        have hc := shell_card_bound 2 r hr
        norm_num at hc
        exact hc
  have hpos := hχ r
  have herror := (div_lt_iff₀ hpos).1 hsmall
  have hgain := (le_div_iff₀ hpos).1 hshell
  have hup := (le_abs_self _).trans_lt herror
  change susceptibility g (2*r) - susceptibility g r -
    ∑ x ∈ S, g (radialAxisSite x) < ε/2 * susceptibility g r at hup
  change ε / 250 ≤ (r:ℝ)^3 / susceptibility g r * g y
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith only [hgain, hup, hsum]

#print axioms IsFreeTwoPoint.eventually_shell_axial_floor
end IsingScaling
