# Universal rotational invariance of two-point functions in cubic lattice models — Lean formalization

This repository contains the Lean 4 formalization accompanying the paper
*Universal rotational invariance of two-point functions in cubic lattice models: Ising, Potts and O(N)*.

The central result (Theorem B(i) of the paper) is an abstract theorem: if
`g : ℤ³ → ℝ` is nonnegative, invariant under the 48 signed permutations,
positive definite, and reflection positive for the two site mirrors
`x₁ = 0` and `x₁ = x₂`, then every susceptibility-normalized vague limit of
`χ_R⁻¹ ∑ₓ g(x) δ_{x/R}` is invariant under `O(3)`, with an atom at the origin
and a continuous radial density elsewhere. Adding reflection positivity across
the bond plane `x₁ = 1/2` gives the lattice-point version (Theorem B(ii)). The
Ising, Potts/random-cluster, XY, Heisenberg and general `O(N)` two-point
functions are instances.

## Build

Requirements: [elan](https://github.com/leanprover/elan); the toolchain
`leanprover/lean4:v4.34.0-rc2` is selected by `lean-toolchain`.

```sh
lake exe cache get      # download the Mathlib build cache
lake build              # builds the 188 modules of MathlibProbe
python3 scripts/check_paper_statements.py
python3 scripts/check_model_endpoints.py
```

`check_paper_statements.py` elaborates every declaration listed in Appendix C
(Table 2) of the paper and fails unless each one depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
`check_model_endpoints.py` typechecks 50 statements specialized to the physical
models and checks the axioms of 105 further named results.

## Statements and declarations

All declarations are in the namespace `IsingScaling`.

| Paper | Lean declaration | Module |
|---|---|---|
| Theorem B(i) | `ModelPackets.isotropic_of_site_forms`, `ModelPackets.exists_isotropic_of_site_forms` | `ModelPacketPhysicalRotation` |
| Theorem B(ii) | `AbstractKernel.raw_angular` | `AbstractKernelPointwise` |
| Corollary 2.2 | `Packet.gridPacket_spectrum_of_site_reflection` | `ReflectedLatticePacket` |
| Proposition 2.7 | `RawLatticeOscillation.localOscillation_of_site_bond` | `RawLatticeOscillation` |
| Section 5 | `Packet.ParitySmoothing.normalizedPacketSource`, `Packet.ParitySmoothing.localOscillation_of_site_forms` | `RotorPacketParitySmoothing`, `ModelPacketSmoothedOscillation` |
| Corollary 4.4 | `RawLatticeOscillation.angular_of_localOscillation`, `annular_of_localOscillation` | `RawLatticeAngularReadout` |
| Proposition 6.2 | `Packet.siteReflectedPositive_of_tendsto` | `ReflectedLatticePacket` |
| Theorem A (Ising) | `AbstractKernelInstance.ising_isotropic_via_kernel`; also `IsTwoPointTangent.rotation_invariant` | `IsingAbstractKernelInstance`, `IsingTwoPointRotation` |
| Theorem C (Potts, FK) | `Potts.SiteBox.canonicalFreePair_isotropic`, `canonicalFreePair_raw_angular`, `Potts.FreeBond.freeLaw_tangent` | `ModelPacketPhysicalRotation`, `RawLatticeAngularReadout`, `PottsFreeBondState` |
| Theorem D(i) (XY) | `Rotor.XY.graphPair_mono`, `Rotor.XY.canonicalFreeGibbs_raw_angular` | `RotorXYGinibre`, `RotorXYFreeGibbsRotation` |
| Theorem D(ii) (Heisenberg) | `Rotor.HeisenbergField.PhysicalRotation.sharp_rotation`, `rounded_rotation` | `RotorHeisenbergPhysicalRotation` |
| Theorem D(iii) (all N) | `Rotor.PressureSelection.ONFamily.exists_on_family_rotation_full` | `RotorONAllNRotation` |
| Theorem D(iv) | `Rotor.PressureSelection.HighTemperature.exists_unique_nearest_gibbs_tanh` | `RotorHighTemperatureUniqueness` |
| Corollary 6.11, Appendix B | `Rotor.IsStationaryFreeCubePairLimit.surface_isotropic`, `raw_angular_even_lattice` | `ModelPacketPhysicalRotation`, `RotorStationaryRawAngular` |

## Scope

For Theorem D(ii) the formal statement concerns every accumulation point of the
positive-field free states as the field tends to zero; the identification of
this limit with the fixed-boundary state (Proposition 6.9 of the paper) is
proved in the paper. The lattice-point statement of Appendix B is formalized on
`(2ℤ)³`, and on `ℤ³` under the additional hypothesis that the bond-centred
rectangles have the same limit.

## License and citation

The code is released under the Creative Commons Attribution 4.0 International
license (`LICENSE`). Citation metadata are in `CITATION.cff`; archived releases
receive a DOI through Zenodo.
