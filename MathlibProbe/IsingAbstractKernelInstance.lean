import MathlibProbe.ModelPacketPhysicalRotation
import MathlibProbe.BinarySpinModelRotation

/-! # The Ising pair as an instance of the abstract kernel theorem

`ModelPackets.isotropic_of_site_forms` (Theorem A of the manuscript) is applied
in the package to the Potts and sphere-spin kernels.  Here the free Ising pair
at inverse temperature `β` is identified with the canonical free `q = 2`
simplex pair at `2β`, so the Ising tangents are covered by the same abstract
theorem, independently of the Messager--Miracle-Sole route. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace IsingScaling.AbstractKernelInstance
open Potts.SiteBox ModelPackets

theorem canonical_two_eq {β : ℝ} (hβ : 0 ≤ β) :
    canonicalFreePair 2 (2 * β) = thermodynamicTwoPoint β := by
  funext z
  have hb : (0 : ℝ) ≤ 2 * β := by positivity
  have h1 := canonicalFreePair_stationary (q := 2) le_rfl hb z 0
  have h2 := BinarySpin.potts_thermodynamic_limit hb z 0
  have h := tendsto_nhds_unique h1 h2
  rw [BinarySpin.potts_thermodynamic_eq] at h
  simpa [sub_zero, mul_div_cancel_left₀ β (two_ne_zero : (2:ℝ) ≠ 0)] using h

theorem ising_isotropic_via_kernel {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) {μ : Measure Space} [IsLocallyFiniteMeasure μ]
    (hv : VaguePairLimit (thermodynamicTwoPoint β) R μ) : IsotropicPairMeasure μ := by
  rw [← canonical_two_eq hβ] at hv
  exact canonicalFreePair_isotropic (q := 2) le_rfl (by positivity) hR hv

theorem ising_exists_isotropic_via_kernel {β : ℝ} (hβ : 0 ≤ β) {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop) :
    ∃ (u : ℕ → ℕ) (μ : Measure Space), StrictMono u ∧ IsLocallyFiniteMeasure μ ∧
      VaguePairLimit (thermodynamicTwoPoint β) (R ∘ u) μ ∧ IsotropicPairMeasure μ := by
  rw [← canonical_two_eq hβ]
  exact canonicalFreePair_exists_isotropic_tangent (q := 2) le_rfl (by positivity) hR

end IsingScaling.AbstractKernelInstance

#print axioms IsingScaling.AbstractKernelInstance.ising_isotropic_via_kernel
#print axioms IsingScaling.AbstractKernelInstance.ising_exists_isotropic_via_kernel
