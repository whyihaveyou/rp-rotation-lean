import MathlibProbe.RawLatticeOscillation
import MathlibProbe.ModelPacketTangentExistence
import MathlibProbe.PottsCanonicalSpatialRotation
import MathlibProbe.PottsCanonicalShiftedMirror

/-! # Rotating two independently rounded original lattice points

For each subsequence extract the same off-origin spatial density and measure.
Their radiality identifies the limits at two rotated positions. Compactness of
a Euclidean annulus also allows both directions to move without converging.
The canonical free Potts kernel supplies the physical bond and site forms.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace IsingScaling.RawLatticeOscillation
open IsingRotation Packet SpatialEnvelope

/-- Direct comparison along the whole input sequence of scales with
independent rounding at the two nonzero macroscopic positions. -/
theorem angular_of_localOscillation {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ}
    (src : NormalizedPacketSource g R delay) (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1)
    (hpos : StationaryPositive g) {C : ℝ} {D r₀ : ℕ}
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀)
    (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization g (R n) * (g (k n)-g (l n))) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro a ha
  let src' : NormalizedPacketSource g (R ∘ a) delay :=
    ⟨src.moments,src.cubic,fun j => src.cube_pos (a j)⟩
  obtain ⟨b,μ,f,hb',_,_,hsp,_,rot⟩ := ModelPackets.exists_rotational_tangent_of_localOscillation
    src' hn hb hpos hC hD hosc (hR.comp ha)
  have hK := hsp x hx _ ((hk.comp ha).comp hb'.tendsto_atTop)
  have hOx := (map_ne_zero_iff O O.injective).2 hx
  have hL := hsp (O x) hOx _ ((hl.comp ha).comp hb'.tendsto_atTop)
  refine ⟨b,?_⟩
  simpa only [Function.comp_apply,mul_sub,(rot O).2 x hx,sub_self] using hK.sub hL

/-- Uniform annular readout. The two directions may vary; their Euclidean
radii differ by o(1) and the first stays away from the origin. -/
theorem annular_of_localOscillation {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ}
    (src : NormalizedPacketSource g R delay) (hn : ∀ z, 0 ≤ g z) (hb : ∀ z, g z ≤ 1)
    (hpos : StationaryPositive g) {C : ℝ} {D r₀ : ℕ}
    (hC : 0 ≤ C) (hD : 2 ≤ D) (hosc : LocalOscillation g C D r₀)
    (hR : Tendsto R atTop atTop) {k l : ℕ → Site} {a B : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0) := by
  let K := Metric.closedBall (0:Space) B
  let V (n : ℕ) := (scaledSite (R n) (k n),scaledSite (R n) (l n))
  have hm (n : ℕ) : V n ∈ K ×ˢ K := by
    simpa only [Set.mem_prod,V,K,Metric.mem_closedBall,dist_zero_right] using And.intro (hk n).2 (hl n)
  apply tendsto_of_subseq_tendsto
  intro u hu
  obtain ⟨⟨x,y⟩,_,v,hv,hxy⟩ := ((isCompact_closedBall (0:Space) B).prod
    (isCompact_closedBall (0:Space) B)).tendsto_subseq (x:=V ∘ u) (fun n => hm _)
  have hseq := hu.comp hv.tendsto_atTop
  have hx := (continuous_fst.tendsto (x,y)).comp hxy
  have hy := (continuous_snd.tendsto (x,y)).comp hxy
  have hxpos : a ≤ ‖x‖ := ge_of_tendsto' hx.norm (fun n => (hk _).1)
  have hne : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hxpos)
  have he : ‖x‖ = ‖y‖ := sub_eq_zero.mp (tendsto_nhds_unique (hx.norm.sub hy.norm) (hrad.comp hseq))
  let O := (Submodule.span ℝ ({x-y} : Set Space))ᗮ.reflection
  have hO : O x = y := Submodule.reflection_sub he
  let src' : NormalizedPacketSource g (R ∘ u ∘ v) delay :=
    ⟨src.moments,src.cubic,fun j => src.cube_pos (u (v j))⟩
  refine ⟨v,angular_of_localOscillation src' hn hb hpos hC hD hosc (hR.comp hseq) O hne hx ?_⟩
  rw [hO]
  exact hy

/-- An additive angular readout becomes a genuine quotient statement when
the comparison point has a positive susceptibility-normalized lower bound. -/
theorem quotient_of_normalized_defect {g : Site → ℝ} {R : ℕ → ℕ} {k l : ℕ → Site}
    (h : Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c)
    (hf : ∀ᶠ n in atTop, c ≤ normalization g (R n) * g (k n)) :
    Tendsto (fun n => g (l n)/g (k n)) atTop (𝓝 1) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hu : Tendsto (fun n => |normalization g (R n) * (g (k n)-g (l n))| / c) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_div] using h.abs.div_const c
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => dist_nonneg)
  filter_upwards [hf] with n hn
  let A := normalization g (R n)
  let a := g (k n)
  let b := g (l n)
  have hp : 0 < A*a := hc.trans_le hn
  have hA : A ≠ 0 := left_ne_zero_of_mul hp.ne'
  have ha : a ≠ 0 := right_ne_zero_of_mul hp.ne'
  have he : b/a-1 = -(A*(a-b))/(A*a) := by field_simp [hA,ha]; ring
  change dist (b/a) 1 ≤ |A*(a-b)| / c
  rw [Real.dist_eq,he,abs_div,abs_neg,abs_of_pos hp]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hc hn

end IsingScaling.RawLatticeOscillation

namespace IsingScaling.Potts.SiteBox
open NormalDifference Packet RawLatticeOscillation

/-- The unit-scale artifice is absent: this holds for the very same canonical
free-boundary Gibbs simplex correlation at every displacement. -/
theorem canonicalFreePair_raw_localOscillation {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β) :
    SpatialEnvelope.LocalOscillation (canonicalFreePair q β) 96 16 40 := by
  let g := canonicalFreePair q β
  have h := canonicalFreePair_stationary hq hβ
  have forms (d : PacketNormal) : SiteReflectedPositive g (tip d) (NormalDifference.refl d) := by
    cases d with
    | axis =>
      have he : NormalDifference.refl .axis = signedPerm (Equiv.refl _) (fun i => decide (i=0)) := by
        funext z i; fin_cases i <;> rfl
      rw [he]
      intro ι _ x hx c
      exact h.axis_positive hq tendsto_id x hx c
    | faceDiagonal =>
      have he : NormalDifference.refl .faceDiagonal = signedPerm (Equiv.swap 0 1) (fun _ => false) := by
        funext z i; fin_cases i <;> rfl
      rw [he]
      intro ι _ x hx c
      exact h.diagonal_positive hq tendsto_id x hx c
  exact localOscillation_of_site_bond (h.abs_le_one hq) h.signedPerm_invariant forms
    (canonicalFreePair_axialBond_positive hq hβ)

/-- All diverging integer radius sequences and independent nearest-lattice
roundings, for the original canonical integer-q Potts pair. -/
theorem canonicalFreePair_raw_angular {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization (canonicalFreePair q β) (R n) *
      (canonicalFreePair q β (k n)-canonicalFreePair q β (l n))) atTop (𝓝 0) := by
  have h := canonicalFreePair_stationary hq hβ
  exact angular_of_localOscillation (canonicalFreePair_normalizedPacketSource hq hβ R)
    (h.ferromagnetic_nonneg hq hβ) (fun z => (le_abs_self _).trans (h.abs_le_one hq z))
    (h.stationaryPositive hq tendsto_id) (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ))
    (canonicalFreePair_raw_localOscillation hq hβ) hR O hx hk hl

/-- Both lattice directions can vary across the sequence inside a fixed
compact annulus. Only their Euclidean radius difference must vanish. -/
theorem canonicalFreePair_raw_angular_annulus {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (hβ : 0 ≤ β)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {k l : ℕ → Site} {a B : ℝ} (ha : 0 < a)
    (hk : ∀ n, a ≤ ‖scaledSite (R n) (k n)‖ ∧ ‖scaledSite (R n) (k n)‖ ≤ B)
    (hl : ∀ n, ‖scaledSite (R n) (l n)‖ ≤ B)
    (hrad : Tendsto (fun n => ‖scaledSite (R n) (k n)‖ - ‖scaledSite (R n) (l n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => normalization (canonicalFreePair q β) (R n) *
      (canonicalFreePair q β (k n)-canonicalFreePair q β (l n))) atTop (𝓝 0) := by
  have h := canonicalFreePair_stationary hq hβ
  exact annular_of_localOscillation (canonicalFreePair_normalizedPacketSource hq hβ R)
    (h.ferromagnetic_nonneg hq hβ) (fun z => (le_abs_self _).trans (h.abs_le_one hq z))
    (h.stationaryPositive hq tendsto_id) (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ))
    (canonicalFreePair_raw_localOscillation hq hβ) hR ha hk hl hrad

#print axioms canonicalFreePair_raw_angular
#print axioms canonicalFreePair_raw_angular_annulus
#print axioms RawLatticeOscillation.quotient_of_normalized_defect

end IsingScaling.Potts.SiteBox
