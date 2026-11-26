import MathlibProbe.IsingAxialShellSpectrum

/-! Propagation of a lower ratio for finite Hausdorff moment measures. -/

noncomputable section
open MeasureTheory

namespace IsingScaling

/-- For a nonnegative variable, the differences of its first and its
    k-th power relative to a nonnegative threshold have the same sign. -/
private theorem power_threshold (z q : ℝ) (hz : 0 ≤ z) (hq : 0 ≤ q) (k : ℕ) :
    q^k * (z^2 - q*z) ≤ z^(k+2) - q*z^(k+1) := by
  have hp : 0 ≤ (z-q)*(z^k-q^k) := by
    rcases le_total q z with h | h
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (pow_le_pow_left₀ hq h k))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (pow_le_pow_left₀ hz h k))
  have := mul_nonneg hz hp
  rw [pow_add, pow_add, pow_one]
  nlinarith only [this]

/-- A finite Hausdorff spectrum propagates a lower first-to-second moment
    ratio to every two consecutive moments of the same arithmetic progression. -/
theorem axial_moment_step_ratio (μ : FiniteMeasure Packet.UnitInterval) (h : ℕ)
    (a : ℕ → ℝ)
    (ha : ∀ n : ℕ, a n = ∫ t, (t : ℝ) ^ (n*h) ∂(μ : Measure Packet.UnitInterval))
    {q : ℝ} (hq : 0 ≤ q) (hbase : q * a 1 ≤ a 2) (k : ℕ) :
    q * a (k+1) ≤ a (k+2) := by
  let z : Packet.UnitInterval → ℝ := fun t => (t : ℝ)^h
  have hz (t) : 0 ≤ z t := pow_nonneg t.property.1 h
  have hi (n : ℕ) : Integrable (fun t => z t ^ n) (μ : Measure Packet.UnitInterval) :=
    ((continuous_subtype_val.pow h).pow n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ha' (n : ℕ) : (∫ t, z t^n ∂(μ : Measure Packet.UnitInterval)) = a n := by
    rw [ha]
    simp only [z, ← pow_mul, Nat.mul_comm h n]
  have hl := (hi 2).sub ((hi 1).const_mul q)
  have hr := (hi (k+2)).sub ((hi (k+1)).const_mul q)
  have H := integral_mono (hl.const_mul (q^k)) hr
    (fun t => by
      change q^k * (z t^2 - q*z t^1) ≤ z t^(k+2) - q*z t^(k+1)
      simpa only [pow_one] using power_threshold (z t) q (hz t) hq k)
  change (∫ t, q^k * (z t^2 - q*z t^1) ∂(μ : Measure Packet.UnitInterval)) ≤
    ∫ t, z t^(k+2) - q*z t^(k+1) ∂(μ : Measure Packet.UnitInterval) at H
  rw [integral_const_mul, integral_sub (hi 2) ((hi 1).const_mul q),
    integral_sub (hi (k+2)) ((hi (k+1)).const_mul q),
    integral_const_mul, integral_const_mul, ha', ha', ha', ha'] at H
  linarith only [H, mul_nonneg (pow_nonneg hq k) (sub_nonneg.mpr hbase)]

/-- The physical two-point function is decreasing along the positive axis. -/
theorem IsFreeTwoPoint.axial_antitone {β : ℝ} {g : Site → ℝ} (hg : IsFreeTwoPoint β g)
    (hβ : 0 ≤ β) : Antitone (fun n : ℕ => g (Pi.single 0 (n : ℤ))) := by
  obtain ⟨μ, _, hm⟩ := hg.axial_spectrum hβ
  have hi (n : ℕ) : Integrable (fun t : Packet.UnitInterval => (t : ℝ)^n)
      (μ : Measure Packet.UnitInterval) :=
    (continuous_subtype_val.pow n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  intro i j hij
  change g (Pi.single 0 (j : ℤ)) ≤ g (Pi.single 0 (i : ℤ))
  rw [hm, hm]
  exact integral_mono (hi j) (hi i) fun t =>
    pow_le_pow_of_le_one t.property.1 t.property.2 hij

/-- If the two-to-one moment ratio exceeds q at spacing h, each further
    h-step costs at most one additional factor of q in the lower bound. -/
theorem IsFreeTwoPoint.axial_step_propagation {β : ℝ} {g : Site → ℝ}
    (hg : IsFreeTwoPoint β g) (hβ : 0 ≤ β) (h : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbase : q * g (Pi.single 0 (h : ℤ)) ≤ g (Pi.single 0 ((2*h : ℕ) : ℤ)))
    (k : ℕ) : q^k * g (Pi.single 0 (h : ℤ)) ≤ g (Pi.single 0 (((k+1)*h : ℕ) : ℤ)) := by
  obtain ⟨μ, _, hm⟩ := hg.axial_spectrum hβ
  let a := fun i : ℕ => g (Pi.single 0 ((i*h : ℕ) : ℤ))
  have hab : q * a 1 ≤ a 2 := by simpa only [a, one_mul] using hbase
  have hh := axial_moment_step_ratio μ h a (fun i => hm (i*h)) hq hab
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      q^(k+1) * g (Pi.single 0 (h : ℤ)) = q * (q^k * g (Pi.single 0 (h : ℤ))) := by ring
      _ ≤ q * a (k+1) := mul_le_mul_of_nonneg_left ih hq
      _ ≤ a (k+2) := hh k

#print axioms axial_moment_step_ratio
#print axioms IsFreeTwoPoint.axial_antitone
#print axioms IsFreeTwoPoint.axial_step_propagation

end IsingScaling
