import MathlibProbe.RawLatticeAngularReadout
import MathlibProbe.ModelPacketPhysicalRotation

/-! # Theorem A' : the pointwise lattice comparison for an abstract kernel

Hypotheses: `|g| ≤ 1`, `g ≥ 0`, `g 0 > 0`, cubic symmetry, positive
definiteness, the two site-mirror forms and the axial bond-mirror form.
No Gibbs measure enters.  This is the composition of the package lemmas
`gridPacket_spectrum_of_site_reflection`, `localOscillation_of_site_bond`
and `angular_of_localOscillation`. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace IsingScaling.AbstractKernel
open IsingRotation Packet SpatialEnvelope RawLatticeOscillation

private theorem zero_mem (L : ℕ) : (0 : Site) ∈ cube L := by
  simp [cube, Fintype.mem_piFinset]

theorem susceptibility_pos {g : Site → ℝ} (hn : ∀ z, 0 ≤ g z) (h0 : 0 < g 0) (R : ℕ) :
    0 < susceptibility g R :=
  h0.trans_le (Finset.single_le_sum (fun z _ => hn z) (zero_mem R))

theorem raw_angular {g : Site → ℝ} (hb : ∀ z, |g z| ≤ 1) (hn : ∀ z, 0 ≤ g z)
    (h0 : 0 < g 0) (hc : CubicKernel g) (hpos : StationaryPositive g)
    (haxis : SiteReflectedPositive g (fun v => v 0)
      (signedPerm (Equiv.refl _) (fun l => decide (l = 0))))
    (hdiag : SiteReflectedPositive g (fun v => v 0 - v 1)
      (signedPerm (Equiv.swap 0 1) (fun _ => false)))
    (bond : AxialBondForm g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (O : Space ≃ₗᵢ[ℝ] Space)
    {x : Space} (hx : x ≠ 0) {k l : ℕ → Site}
    (hk : Tendsto (fun n => scaledSite (R n) (k n)) atTop (𝓝 x))
    (hl : Tendsto (fun n => scaledSite (R n) (l n)) atTop (𝓝 (O x))) :
    Tendsto (fun n => normalization g (R n) * (g (k n) - g (l n))) atTop (𝓝 0) := by
  have src : NormalizedPacketSource g R :=
    ⟨fun d {_} _ c x y => gridPacket_spectrum_of_site_reflection hb haxis hdiag d c x y,
      hc, fun n => susceptibility_pos hn h0 (R n)⟩
  have forms (d : PacketNormal) :
      SiteReflectedPositive g (NormalDifference.tip d) (NormalDifference.refl d) := by
    cases d with
    | axis =>
      have he : NormalDifference.refl .axis =
          signedPerm (Equiv.refl _) (fun i => decide (i = 0)) := by
        funext z i; fin_cases i <;> rfl
      rw [he]
      intro ι _ x hx c
      exact haxis x hx c
    | faceDiagonal =>
      have he : NormalDifference.refl .faceDiagonal =
          signedPerm (Equiv.swap 0 1) (fun _ => false) := by
        funext z i; fin_cases i <;> rfl
      rw [he]
      intro ι _ x hx c
      exact hdiag x hx c
  exact angular_of_localOscillation src hn (fun z => (le_abs_self _).trans (hb z)) hpos
    (by norm_num : 0 ≤ (96:ℝ)) (by norm_num : 2 ≤ (16:ℕ))
    (localOscillation_of_site_bond hb hc forms bond) hR O hx hk hl

end IsingScaling.AbstractKernel

#print axioms IsingScaling.AbstractKernel.raw_angular
