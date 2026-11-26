import MathlibProbe.IsingPacketScaling

/-! A lattice site-reflection form gives every time moment of the actual
transverse packet on its even-layer mesh. The kernel is a function of the
difference of physical lattice sites. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace IsingScaling.Packet

/-- The signed two-point site-reflection form for a stationary real kernel. -/
def SiteReflectedPositive (g : Site → ℝ) (t : Site → ℤ) (r : Site → Site) : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → Site), (∀ i, 0 ≤ t (x i)) → ∀ c : ι → ℝ,
    0 ≤ ∑ i, ∑ j, c i * c j * g (x i - r (x j))

/-- Finite-volume reflection positivity passes to a stationary two-site
limit. An eventually nonnegative form suffices for each fixed set of sites. -/
theorem siteReflectedPositive_of_tendsto {g : Site → ℝ}
    {G : ℕ → Site → Site → ℝ} {t : Site → ℤ} {r : Site → Site}
    (hlim : ∀ x y, Tendsto (fun L => G L x y) atTop (𝓝 (g (x-y))))
    (hform : ∀ {ι : Type} [Fintype ι] (x : ι → Site), (∀ i, 0 ≤ t (x i)) →
      ∀ c : ι → ℝ, ∀ᶠ L : ℕ in atTop,
        0 ≤ ∑ i, ∑ j, c i * c j * G L (x i) (r (x j))) :
    SiteReflectedPositive g t r := by
  intro ι _ x hx c
  apply ge_of_tendsto _ (hform x hx c)
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    tendsto_const_nhds.mul (hlim _ _)

/-- The two source positions in every time Hankel matrix come from one
reflected half-lattice list. Boundedness controls the odd differences. -/
theorem completeMonotone_of_site_reflection {g : Site → ℝ}
    (hbound : ∀ z, |g z| ≤ 1)
    (t : Site → ℤ) (r : Site → Site) (hpos : SiteReflectedPositive g t r)
    {ι : Type} [Fintype ι] (X : ℕ → ι → Site) (hX : ∀ p i, 0 ≤ t (X p i))
    (K : ℕ → ι → ι → ℝ) (hK : ∀ p q i j, g (X p i - r (X q j)) = K (p+q) i j)
    (c : ι → ℝ) (k n : ℕ) : 0 ≤ (diff^[k]) (IsingScaling.evenPacket c K) n := by
  classical
  apply Packet.completeMonotone_of_hankel
  · intro J _ d γ s
    let T (j : J × ι) := X (s + 2*d j.1) j.2
    let b (j : J × ι) := γ j.1 * c j.2
    have hp := hpos T (fun _ => hX _ _) b
    simp only [Fintype.sum_prod_type, T, b, hK] at hp
    refine hp.trans_eq ?_
    simp only [IsingScaling.evenPacket, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [show s+2*d i+(s+2*d j) = 2*(s+d i+d j) by omega]
    ring
  · refine ⟨∑ i, ∑ j, |c i| * |c j|, ?_⟩
    intro s
    unfold IsingScaling.evenPacket
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    have hB := hbound (X (2*s) i - r (X 0 j))
    rw [hK, add_zero] at hB
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_right (by positivity) hB

/-- Moments along (2n,0,0) with transverse offsets (0,x_i,y_i). -/
theorem axis_gridPacket_spectrum_of_site_reflection {g : Site → ℝ}
    (hbound : ∀ z, |g z| ≤ 1)
    (hpos : SiteReflectedPositive g (fun v => v 0)
      (signedPerm (Equiv.refl _) (fun l => decide (l = 0))))
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure UnitInterval)) = gridPacket false g c x y n := by
  apply hausdorff_moments
  intro k n
  change 0 ≤ (diff^[k]) (IsingScaling.evenPacket c (fun m i j =>
    g ![(m:ℤ), x i-x j, y i-y j])) n
  let X (p : ℕ) (i : ι) : Site := ![(p:ℤ), x i, y i]
  apply completeMonotone_of_site_reflection (g := g) hbound (fun w => w 0)
    (signedPerm (Equiv.refl _) (fun l => decide (l = 0))) hpos X
  · intro p i
    change 0 ≤ (p:ℤ)
    omega
  · intro p q i j
    apply congrArg g
    funext l
    fin_cases l
    · change (p:ℤ) - -(q:ℤ) = ((p+q:ℕ):ℤ)
      omega
    · rfl
    · rfl

/-- Moments along (2n,-2n,0) with transverse offsets (x_i,x_i,y_i). -/
theorem diagonal_gridPacket_spectrum_of_site_reflection {g : Site → ℝ}
    (hbound : ∀ z, |g z| ≤ 1)
    (hpos : SiteReflectedPositive g (fun v => v 0-v 1)
      (signedPerm (Equiv.swap 0 1) (fun _ => false)))
    {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure UnitInterval)) = gridPacket true g c x y n := by
  apply hausdorff_moments
  intro k n
  change 0 ≤ (diff^[k]) (IsingScaling.evenPacket c (fun m i j =>
    g ![x i-x j+(m:ℤ), x i-x j-(m:ℤ), y i-y j])) n
  let X (p : ℕ) (i : ι) : Site := ![x i + (p:ℤ), x i - (p:ℤ), y i]
  apply completeMonotone_of_site_reflection (g := g) hbound (fun w => w 0 - w 1)
    (signedPerm (Equiv.swap 0 1) (fun _ => false)) hpos X
  · intro p i
    change 0 ≤ (x i + (p:ℤ)) - (x i - (p:ℤ))
    omega
  · intro p q i j
    apply congrArg g
    funext l
    fin_cases l
    · change (x i + (p:ℤ)) - (x j - (q:ℤ)) = x i - x j + ((p+q:ℕ):ℤ)
      omega
    · change (x i - (p:ℤ)) - (x j + (q:ℤ)) = x i - x j - ((p+q:ℕ):ℤ)
      omega
    · rfl

/-- The two representative normals of the cubic action. The output is one
positive finite measure for every entire normal-time sequence. -/
theorem gridPacket_spectrum_of_site_reflection {g : Site → ℝ}
    (hbound : ∀ z, |g z| ≤ 1)
    (haxis : SiteReflectedPositive g (fun v => v 0)
      (signedPerm (Equiv.refl _) (fun l => decide (l = 0))))
    (hdiag : SiteReflectedPositive g (fun v => v 0-v 1)
      (signedPerm (Equiv.swap 0 1) (fun _ => false)))
    (diagonal : Bool) {ι : Type} [Fintype ι] (c : ι → ℝ) (x y : ι → ℤ) :
    ∃ μ : FiniteMeasure UnitInterval, ∀ n,
      (∫ t, (t:ℝ)^n ∂(μ : Measure UnitInterval)) = gridPacket diagonal g c x y n := by
  cases diagonal
  · exact axis_gridPacket_spectrum_of_site_reflection hbound haxis c x y
  · exact diagonal_gridPacket_spectrum_of_site_reflection hbound hdiag c x y

#print axioms siteReflectedPositive_of_tendsto
#print axioms gridPacket_spectrum_of_site_reflection

end IsingScaling.Packet
