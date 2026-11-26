import MathlibProbe.IsingPacketScaling
import MathlibProbe.IsingFreePairLimit
import MathlibProbe.TwoPointAngularRotation

/-! Annular convergence of the lattice two-point function supplies the
positive-time convergence used by the packet spectral construction. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace IsingScaling.Packet
open IsingRotation

def normalization (g : Site → ℝ) (R : ℕ) : ℝ := (R:ℝ)^3 / susceptibility g R

def OffOriginLimit (g : Site → ℝ) (R : ℕ → ℕ) (f : Space → ℝ) : Prop :=
  ∀ v : Space, v ≠ 0 → ∀ q : ℕ → Site,
    Tendsto (fun n => scaledSite (R n) (q n)) atTop (𝓝 v) →
    Tendsto (fun n => normalization g (R n) * g (q n)) atTop (𝓝 (f v))

/-- Signed cubic permutations on the physical displacement variable. -/
def CubicKernel (g : Site → ℝ) : Prop :=
  ∀ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (x : Site), g (signedPerm p s x) = g x

/-- Discrete data on the sequence defining the actual cube normalization.
The fixed microscopic inward offset accommodates finite supported spin
marks. A single-site mark uses zero delay. -/
structure NormalizedPacketSource (g : Site → ℝ) (R : ℕ → ℕ) (delay : ℕ := 0) : Prop where
  moments : HasDelayedGridPacketMoments g delay
  cubic : CubicKernel g
  cube_pos : ∀ n, 0 < susceptibility g (R n)

theorem normalizedPacketSource_of_free {β : ℝ} {g : Site → ℝ}
    (hβ : 0 ≤ β) (hg : IsFreeTwoPoint β g) (R : ℕ → ℕ) : NormalizedPacketSource g R :=
  ⟨gridPacketMoments_of_freePair (hg.stationary_pair_limit hβ), freeLimit_signedPerm hg,
    fun n => (hg.positive_cube_mass hβ).2 (R n)⟩

/-- Displacements along the two reflected lattice geometries in units of
two layers. The diagonal parametrization keeps the actual Euclidean
length of (1,-1,0), rather than replacing it by the unit normal. -/
def packetVector (diagonal : Bool) (t x y : ℝ) : Space :=
  match diagonal with
  | true => xyz (x+2*t) (x-2*t) y
  | false => xyz (2*t) x y

def packetSite (diagonal : Bool) (k : ℕ) (x y : ℤ) : Site :=
  match diagonal with
  | true => ![x+(2*k:ℕ), x-(2*k:ℕ), y]
  | false => ![(2*k:ℕ), x, y]

def roundPoint (r : ℕ) (x : ℝ) : ℤ :=
  (⌊max x 0 * r⌋₊ : ℤ) - (⌊max (-x) 0 * r⌋₊ : ℤ)

private theorem roundPoint_tendsto {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) (x : ℝ) :
    Tendsto (fun n => (roundPoint (R n) x : ℝ)/(R n:ℝ)) atTop (𝓝 x) := by
  have hp (a : ℝ) (ha : 0 ≤ a) := (tendsto_nat_floor_mul_div_atTop ha).comp
    (tendsto_natCast_atTop_atTop.comp hR)
  have hh := (hp _ (le_max_right x 0)).sub (hp _ (le_max_right (-x) 0))
  have he : max x 0 - max (-x) 0 = x := by
    cases le_total x 0 with
    | inl h => simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    | inr h => simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  simpa only [roundPoint, Int.cast_sub, Int.cast_natCast, sub_div, Function.comp_apply, he] using hh

theorem packetVector_ne (d : Bool) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    packetVector d t x y ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Space => v 0) h
  have h1 := congrArg (fun v : Space => v 1) h
  cases d
  · change 2*t = 0 at h0
    linarith
  · change x+2*t = 0 at h0
    change x-2*t = 0 at h1
    linarith

theorem delayed_packetSite_tendsto {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (d : Bool) {t : ℝ} (ht : 0 < t) (x₁ x₂ y₁ y₂ : ℝ) (delay : ℕ) :
    Tendsto (fun n => scaledSite (R n) (packetSite d (⌊t*R n⌋₊+delay)
      (roundPoint (R n) x₁-roundPoint (R n) x₂) (roundPoint (R n) y₁-roundPoint (R n) y₂)))
      atTop (𝓝 (packetVector d t (x₁-x₂) (y₁-y₂))) := by
  have hT₀ := (tendsto_nat_floor_mul_div_atTop ht.le).comp (tendsto_natCast_atTop_atTop.comp hR)
  have hd := (tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hR)).const_mul (delay:ℝ)
  have hT : Tendsto (fun n => ((⌊t*R n⌋₊+delay:ℕ):ℝ)/(R n:ℝ)) atTop (𝓝 t) := by
    simpa only [Nat.cast_add,add_div,div_eq_mul_inv,add_mul,mul_zero,add_zero,Function.comp_apply] using hT₀.add hd
  have h2 := hT.const_mul (2:ℝ)
  have hx := (roundPoint_tendsto hR x₁).sub (roundPoint_tendsto hR x₂)
  have hy := (roundPoint_tendsto hR y₁).sub (roundPoint_tendsto hR y₂)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro i
  cases d <;> fin_cases i
  · simpa [packetSite,packetVector,xyz,Function.comp_def,mul_div_assoc] using h2
  · simpa [packetSite,packetVector,xyz,sub_div] using hx
  · simpa [packetSite,packetVector,xyz,sub_div] using hy
  · simpa [packetSite,packetVector,xyz,sub_div,add_div,Function.comp_def,mul_div_assoc] using hx.add h2
  · simpa [packetSite,packetVector,xyz,sub_div,Function.comp_def,mul_div_assoc] using hx.sub h2
  · simpa [packetSite,packetVector,xyz,sub_div] using hy

theorem packetSite_tendsto {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (d : Bool) {t : ℝ} (ht : 0 < t) (x₁ x₂ y₁ y₂ : ℝ) :
    Tendsto (fun n => scaledSite (R n) (packetSite d ⌊t*R n⌋₊
      (roundPoint (R n) x₁-roundPoint (R n) x₂) (roundPoint (R n) y₁-roundPoint (R n) y₂)))
      atTop (𝓝 (packetVector d t (x₁-x₂) (y₁-y₂))) :=
  delayed_packetSite_tendsto hR d ht x₁ x₂ y₁ y₂ 0

def finiteTimePacket {ι : Type} [Fintype ι] (f : Space → ℝ) (d : Bool)
    (c x y : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * f (packetVector d t (x i-x j) (y i-y j))

/-- Every fixed finite real packet in a locally uniform off-origin spatial
limit has a positive energy measure on positive normal times. No spectral
representation, scale ratio, or zero-time bound is an input. -/
theorem finiteTimePacket_laplace_of_moments {g : Site → ℝ} {R : ℕ → ℕ} {delay : ℕ}
    (hmom : HasDelayedGridPacketMoments g delay) (hχ : ∀ n, 0 < susceptibility g (R n)) (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    {ι : Type} [Fintype ι] (c x y : ι → ℝ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = finiteTimePacket f d c x y t := by
  let A (n : ℕ) := normalization g (R n)
  have hA (n) : 0 ≤ A n := div_nonneg (by positivity) (hχ n).le
  let Cn (n : ℕ) (i : ι) := Real.sqrt (A n) * c i
  let X (n : ℕ) (i : ι) := roundPoint (R n) (x i)
  let Y (n : ℕ) (i : ι) := roundPoint (R n) (y i)
  apply scaled_packet_laplace_of_moments hmom d (fun _ => ι) Cn X Y R hR
    (finiteTimePacket f d c x y)
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    apply continuousOn_const.mul
    apply hf.comp _ (fun t ht => packetVector_ne d ht _ _)
    cases d <;> apply Continuous.continuousOn <;> apply continuous_xyz <;> fun_prop
  · intro t ht
    have hk (n : ℕ) : gridPacket d g (Cn n) (X n) (Y n) (⌊t*R n⌋₊+delay) =
        ∑ i, ∑ j, (c i*c j) * (A n*g
          (packetSite d (⌊t*R n⌋₊+delay) (X n i-X n j) (Y n i-Y n j))) := by
      have hw (i j : ι) (v : Site) : Cn n i * Cn n j * g v =
          c i*c j*(A n*g v) := by
        calc _ = c i*c j*((Real.sqrt (A n))^2*g v) := by dsimp [Cn]; ring
             _ = _ := by rw [Real.sq_sqrt (hA n)]
      cases d <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply Finset.sum_congr rfl <;>
        intro j _ <;> exact hw i j _
    simp_rw [hk]
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hsp _ (packetVector_ne d ht _ _) _ (delayed_packetSite_tendsto hR d ht _ _ _ _ delay)).const_mul _

theorem finiteTimePacket_laplace {β : ℝ} {g : Site → ℝ} (hβ : 0 ≤ β)
    (hg₀ : IsFreeTwoPoint β g)
    {R : ℕ → ℕ} (hR : Tendsto R atTop atTop) {f : Space → ℝ}
    (hf : ContinuousOn f {0}ᶜ) (hsp : OffOriginLimit g R f) (d : Bool)
    {ι : Type} [Fintype ι] (c x y : ι → ℝ) :
    ∃ ρ : Measure ℝ≥0, ∀ t : ℝ, 0 < t →
      Integrable (fun E : ℝ≥0 => Real.exp (-t*(E:ℝ))) ρ ∧
      (∫ E : ℝ≥0, Real.exp (-t*(E:ℝ)) ∂ρ) = finiteTimePacket f d c x y t :=
  finiteTimePacket_laplace_of_moments (gridPacketMoments_of_freePair (hg₀.stationary_pair_limit hβ))
    (fun n => (hg₀.positive_cube_mass hβ).2 (R n)) hR hf hsp d c x y

end IsingScaling.Packet
