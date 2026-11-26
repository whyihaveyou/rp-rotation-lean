import MathlibProbe.IsingTwoPointAngularOscillation
import MathlibProbe.IsingBondMirror

/-! Unit-step axial transfer spectrum for the original zero-field free Ising
two-point function, and the positive kernel for the floored Euclidean shell. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace IsingScaling

/-- The shell polynomial evaluates all unit-step axial moments with their
actual lattice multiplicities. The polynomial also applies at 0 and 1. -/
def axialShellKernel (s r : ℕ) (t : Packet.UnitInterval) : ℝ :=
  ∑ x ∈ cube (s*r) \ cube r, (t:ℝ)^⌊siteRadius x⌋₊

theorem axialShellKernel_nonneg (s r : ℕ) (t : Packet.UnitInterval) :
    0 ≤ axialShellKernel s r t :=
  Finset.sum_nonneg fun _ _ => pow_nonneg t.property.1 _

/-- Site reflection supplies even shifts; the coordinate bond mirror
supplies the odd shifts of this same single-spin Hankel sequence. -/
theorem IsFreeTwoPoint.axial_hankel {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    Packet.HankelPositive (fun n => g ![(n:ℤ),0,0]) := by
  intro ι _ d c n
  let k := n/2
  by_cases hn : n%2=0
  · let x (i : ι) : Site := ![((k+d i:ℕ):ℤ),0,0]
    have hx (i : ι) : 0 ≤ x i 0 := by
      change 0 ≤ ((k+d i:ℕ):ℤ)
      positivity
    have h := (hg.stationary_pair_limit hβ).axis_reflected_positive x hx c
    have he (i j : ι) : x i-signedPerm (Equiv.refl _) (fun v => decide (v=0)) (x j) =
        ![((n+d i+d j:ℕ):ℤ),0,0] := by
      ext v
      fin_cases v
      · change ((k+d i:ℕ):ℤ) - -((k+d j:ℕ):ℤ) = ((n+d i+d j:ℕ):ℤ)
        dsimp [k]
        omega
      · rfl
      · rfl
    simp only [he] at h
    exact h
  · let x (i : ι) : Site := ![((k+1+d i:ℕ):ℤ),0,0]
    have hx (i : ι) : 0 < x i 0 := by
      change 0 < ((k+1+d i:ℕ):ℤ)
      omega
    have he (i j : ι) : x i - BondMirror.reflected (x j) =
        ![((n+d i+d j:ℕ):ℤ),0,0] := by
      ext v
      fin_cases v
      · change ((k+1+d i:ℕ):ℤ) - (1-((k+1+d j:ℕ):ℤ)) = ((n+d i+d j:ℕ):ℤ)
        dsimp [k]
        omega
      · rfl
      · rfl
    simpa only [he] using BondMirror.reflected_positive hg hβ x hx c

/-- A common probability measure for all integer-time axial correlations,
including the zeroth moment at a coincident pair. -/
theorem IsFreeTwoPoint.axial_spectrum {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, IsProbabilityMeasure (μ : Measure Packet.UnitInterval) ∧
      ∀ n : ℕ, g (Pi.single 0 (n:ℤ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval) := by
  have hb : ∀ n : ℕ, |g ![(n:ℤ),0,0]| ≤ 1 := by
    intro n
    simpa only [sub_zero] using (hg.stationary_pair_limit hβ).abs_le_one ![(n:ℤ),0,0] 0
  obtain ⟨μ, hm⟩ := Packet.hausdorff_moments _ (fun k =>
    Packet.completeMonotone_of_hankel k (hg.axial_hankel hβ) ⟨1,hb⟩)
  have H (n : ℕ) : g (Pi.single 0 (n:ℤ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval) := by
    have he : (![(n:ℤ),0,0] : Site) = Pi.single 0 (n:ℤ) := by
      ext v
      fin_cases v <;> simp
    simpa only [he] using (hm n).symm
  have hg0 : g 0 = 1 := tendsto_nhds_unique (hg 0)
    (by simp only [freeTwoPoint_zero]; exact tendsto_const_nhds)
  have hmass : 1 = ((μ:Measure Packet.UnitInterval) Set.univ).toReal := by
    simpa [hg0, measureReal_def] using H 0
  refine ⟨μ,⟨?_⟩,H⟩
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    congrArg ENNReal.ofReal hmass.symm

private theorem shellIntegral_of_moments {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) (μ : FiniteMeasure Packet.UnitInterval)
    (hm : ∀ n : ℕ, g (Pi.single 0 (n:ℤ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval)) :
    (∀ s r : ℕ, (∑ x ∈ cube (s*r) \ cube r, g (radialAxisSite x)) =
      ∫ t, axialShellKernel s r t ∂(μ:Measure Packet.UnitInterval)) ∧
    ∀ s : ℕ, 1 ≤ s → Tendsto (fun r : ℕ => susceptibility g (s*r) / susceptibility g r -
      (1+(∫ t, axialShellKernel s r t ∂(μ:Measure Packet.UnitInterval)) / susceptibility g r))
      atTop (𝓝 0) := by
  have hsum (s r : ℕ) : (∑ x ∈ cube (s*r) \ cube r, g (radialAxisSite x)) =
      ∫ t, axialShellKernel s r t ∂(μ:Measure Packet.UnitInterval) := by
    unfold axialShellKernel
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro x _
      have hx : 0 ≤ siteRadius x := norm_nonneg _
      simpa only [radialAxisSite,Int.natCast_floor_eq_floor hx] using hm ⌊siteRadius x⌋₊
    · intro x _
      exact (continuous_subtype_val.pow ⌊siteRadius x⌋₊).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine ⟨hsum,?_⟩
  intro s hs
  have hh := hg.susceptibility_shell_radial_axis hβ s hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hh.congr
  intro r
  have hp := (hg.positive_cube_mass hβ).2 r
  rw [hsum,Real.norm_eq_abs,←abs_of_pos hp,←abs_div]
  congr 1
  rw [abs_of_pos hp]
  field_simp [hp.ne']
  ring

/-- The same measure represents the precise floored-radius sum on every
discrete shell and gives the full-sequence asymptotic at each fixed dilation. -/
theorem IsFreeTwoPoint.susceptibility_axialShell_spectrum {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) :
    ∃ μ : FiniteMeasure Packet.UnitInterval, IsProbabilityMeasure (μ : Measure Packet.UnitInterval) ∧
      (∀ n : ℕ, g (Pi.single 0 (n:ℤ)) = ∫ t, (t:ℝ)^n ∂(μ:Measure Packet.UnitInterval)) ∧
      (∀ s r : ℕ, (∑ x ∈ cube (s*r) \ cube r, g (radialAxisSite x)) =
        ∫ t, axialShellKernel s r t ∂(μ:Measure Packet.UnitInterval)) ∧
      ∀ s : ℕ, 1 ≤ s → Tendsto (fun r : ℕ => susceptibility g (s*r) / susceptibility g r -
        (1+(∫ t, axialShellKernel s r t ∂(μ:Measure Packet.UnitInterval)) / susceptibility g r))
        atTop (𝓝 0) := by
  obtain ⟨μ,hprob,hm⟩ := hg.axial_spectrum hβ
  exact ⟨μ,hprob,hm,shellIntegral_of_moments hg hβ μ hm⟩

#print axioms IsFreeTwoPoint.axial_spectrum
#print axioms IsFreeTwoPoint.susceptibility_axialShell_spectrum

end IsingScaling
