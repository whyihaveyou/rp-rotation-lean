import MathlibProbe.RotorXYGinibre
import MathlibProbe.RotorFreeUniqueExhaustion

/-! # Fourier moments of the embedded free XY Gibbs law

Once all tested sites belong to a finite domain, its exterior fill drops out of
the Fourier integral. The physical sphere marginal and the induced half-weighted
directed bond sum then identify it with the finite Ginibre comparison.
-/

noncomputable section
open Filter Finset MeasureTheory
open scoped InnerProductSpace Topology ProbabilityTheory
namespace IsingScaling.Rotor.XY
open PressureSelection PressureSelection.LocalGibbs PressureSelection.FreeExhaustion

local instance : MeasurableSpace Circle := borel _
local instance : BorelSpace Circle := ⟨rfl⟩

/-- A finite list of lattice sites with its signed integer charges in the physical XY field. -/
def listedCharacter {I : Type*} [Fintype I] (a : I → Site) (m : I → ℤ) (s : SpinField 2) : ℂ :=
  (chargeCharacter a m (phase ∘ s) : ℂ)

private theorem domain_graphRead (β : ℝ) (D : Finset Site) (fill : SpinField 2)
    (F : (D → Circle) → ℝ) (hF : Continuous F) :
    (∫ s : SpinField 2, F (fun i : D => phase (s i.val)) ∂(freeDomainLaw 2 β D fill : Measure _)) =
      graphPhaseRead (fun e : D × D => if latticeDistance e.1.val e.2.val = 1 then β/2 else 0) F := by
  let H (x y : D) := nearestCoupling β (y.val-x.val)
  let μ := Measure.pi (fun _ : D => SiteReflection.surfacePrior 2)
  have hr : Continuous (D.restrict : SpinField 2 → WindowSpin 2 D) := continuous_pi fun i => continuous_apply i.val
  have hf : Continuous (fun s : D → Spin 2 => F (phase ∘ s)) :=
    hF.comp (continuous_pi fun i => continuous_phase.comp (continuous_apply i))
  have he (s : D → Spin 2) : energy H s = ∑ e : D × D,
      (if latticeDistance e.1.val e.2.val = 1 then β/2 else 0) * ⟪(s e.1).val,(s e.2).val⟫_ℝ := by
    simp only [energy,Fintype.sum_prod_type,Finset.sum_div,H,nearestCoupling_at_pair]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  calc
    _ = ∫ s : D → Spin 2, F (phase ∘ s) ∂(sphereGibbs 2 H : Measure _) := by
      rw [←freeDomain_marginal 2 β D fill,integral_map hr.measurable.aemeasurable hf.aestronglyMeasurable] <;> rfl
    _ = _ := by
      change (∫ s, F (phase ∘ s) ∂(μ.tilted (energy H))) = _
      rw [integral_tilted]
      simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div,he,graphPhaseRead] <;> rfl

private theorem domainCharacter_real_eq {I : Type*} [Fintype I] (β : ℝ) (D : Finset Site)
    (a : I → D) (m : I → ℤ) (fill : SpinField 2) :
    (∫ s, (listedCharacter (fun i => (a i).val) m s).re ∂(freeDomainLaw 2 β D fill : Measure _)) =
      finiteFourierMoment (fun x : D => x.val) β a m :=
  domain_graphRead β D fill (fun s => (chargeCharacter a m s : ℂ).re)
    (Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_chargeCharacter a m)))

/-- Any two exterior fills give ordered real Fourier reads on nested induced regions. -/
theorem domainCharacter_real_mono {I : Type*} [Fintype I] {β : ℝ} (hβ : 0 ≤ β)
    {D E : Finset Site} (hDE : D ⊆ E) (a : I → D) (m : I → ℤ) (fillD fillE : SpinField 2) :
    (∫ s, (listedCharacter (fun i => (a i).val) m s).re ∂(freeDomainLaw 2 β D fillD : Measure _)) ≤
      ∫ s, (listedCharacter (fun i => (a i).val) m s).re ∂(freeDomainLaw 2 β E fillE : Measure _) := by
  let inc : D ↪ E := ⟨fun x => ⟨x.val,hDE x.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun y : E => y.val) h)⟩
  exact (domainCharacter_real_eq β D a m fillD).le.trans
    ((finiteFourierMoment_embed Subtype.val Subtype.val inc (fun _ _ => rfl) hβ a m).trans
      (domainCharacter_real_eq β E (inc ∘ a) m fillE).ge)

/-- The sine Fourier read vanishes for every charged test contained in a free domain. -/
theorem domainCharacter_im_eq_zero {I : Type*} [Fintype I] (β : ℝ) (D : Finset Site)
    (a : I → D) (m : I → ℤ) (fill : SpinField 2) :
    (∫ s, (listedCharacter (fun i => (a i).val) m s).im ∂(freeDomainLaw 2 β D fill : Measure _)) = 0 :=
  (domain_graphRead β D fill (fun s => (chargeCharacter a m s : ℂ).im)
    (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_chargeCharacter a m)))).trans
    (graphPhaseRead_im_eq_zero _ a m)

/-- A real character integral in a fixed free domain varies continuously with
the inverse temperature, and increases on the ferromagnetic half-line. -/
theorem domainCharacter_real_temperature {I : Type*} [Fintype I] (D : Finset Site)
    (a : I → D) (m : I → ℤ) (fill : SpinField 2) :
    let M := fun β : ℝ =>
      ∫ s, (listedCharacter (fun i => (a i).val) m s).re ∂(freeDomainLaw 2 β D fill : Measure _)
    Continuous M ∧ MonotoneOn M (Set.Ici 0) := by
  dsimp only
  simp_rw [domainCharacter_real_eq]
  constructor
  · let μ := Measure.pi (fun _ : D => SiteReflection.surfacePrior 2)
    let E (β : ℝ) (s : D → Spin 2) := ∑ e : D × D,
      (if latticeDistance e.1.val e.2.val = 1 then β/2 else 0) * ⟪(s e.1).val, (s e.2).val⟫_ℝ
    let F (s : D → Spin 2) := (chargeCharacter a m (phase ∘ s) : ℂ).re
    have hE : Continuous E.uncurry := by
      apply continuous_finsetSum
      intro e _
      by_cases h : latticeDistance e.1.val e.2.val = 1 <;> simp only [h, ite_true, ite_false] <;> fun_prop
    have hF : Continuous F := Complex.continuous_re.comp (continuous_subtype_val.comp
      ((continuous_chargeCharacter a m).comp (continuous_pi fun i => continuous_phase.comp (continuous_apply i))))
    change Continuous (fun β => (∫ s, Real.exp (E β s) * F s ∂μ) / ∫ s, Real.exp (E β s) ∂μ)
    apply Continuous.div
    · simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
        (μ := μ) (f := fun β s => Real.exp (E β s) * F s)
        (hE.rexp.mul (hF.comp continuous_snd)) isCompact_univ
    · simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
        (μ := μ) (f := fun β s => Real.exp (E β s)) hE.rexp isCompact_univ
    · intro β
      exact (integral_exp_pos ((hE.rexp.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).ne'
  · intro β hβ γ _ hle
    apply graphFourierMoment_mono
    · intro e
      split_ifs <;> linarith [show 0 ≤ β from hβ]
    · intro e
      split_ifs <;> linarith

#print axioms domainCharacter_real_mono
#print axioms domainCharacter_im_eq_zero
#print axioms domainCharacter_real_temperature
end IsingScaling.Rotor.XY
