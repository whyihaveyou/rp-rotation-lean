"""Check the Lean declarations listed in Appendix C of the paper.

The script elaborates every declaration of Table 2 and prints its transitive
axioms.  It fails unless each declaration exists and depends only on
`propext`, `Classical.choice` and `Quot.sound`.

Usage (from the repository root, after `lake build`):
    python3 scripts/check_paper_statements.py
"""

from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

# (statement in the paper, fully qualified Lean name)
DECLARATIONS = [
    ("Theorem B(i)", "IsingScaling.ModelPackets.isotropic_of_site_forms"),
    ("Theorem B(i)", "IsingScaling.ModelPackets.exists_isotropic_of_site_forms"),
    ("Theorem B(ii)", "IsingScaling.AbstractKernel.raw_angular"),
    ("Corollary 2.2", "IsingScaling.Packet.gridPacket_spectrum_of_site_reflection"),
    ("Proposition 2.7", "IsingScaling.RawLatticeOscillation.localOscillation_of_site_bond"),
    ("Section 5", "IsingScaling.Packet.ParitySmoothing.normalizedPacketSource"),
    ("Section 5", "IsingScaling.Packet.ParitySmoothing.localOscillation_of_site_forms"),
    ("Corollary 4.4", "IsingScaling.RawLatticeOscillation.angular_of_localOscillation"),
    ("Corollary 4.4", "IsingScaling.RawLatticeOscillation.annular_of_localOscillation"),
    ("Proposition 6.2", "IsingScaling.Packet.siteReflectedPositive_of_tendsto"),
    ("Theorem A", "IsingScaling.AbstractKernelInstance.ising_isotropic_via_kernel"),
    ("Theorem A", "IsingScaling.AbstractKernelInstance.ising_exists_isotropic_via_kernel"),
    ("Theorem A (MMS route)", "IsingScaling.IsTwoPointTangent.rotation_invariant"),
    ("Theorem C", "IsingScaling.Potts.SiteBox.canonicalFreePair_isotropic"),
    ("Theorem C", "IsingScaling.Potts.SiteBox.canonicalFreePair_raw_angular"),
    ("Theorem C", "IsingScaling.Potts.SiteBox.canonicalFreePair_axialBond_positive"),
    ("Theorem C", "IsingScaling.Potts.EdwardsSokal.simplex_correlation_eq_connectivity"),
    ("Theorem C", "IsingScaling.Potts.EdwardsSokal.free_connectivity_mono"),
    ("Theorem C", "IsingScaling.Potts.FreeBond.freeLaw_tangent"),
    ("Theorem C", "IsingScaling.Potts.FreeBond.exhaustion_tendsto_freeLaw"),
    ("Theorem D(i)", "IsingScaling.Rotor.XY.graphPair_mono"),
    ("Theorem D(i)", "IsingScaling.Rotor.XY.canonicalFreePair_raw_angular"),
    ("Theorem D(i)", "IsingScaling.Rotor.XY.canonicalFreeGibbs_raw_angular"),
    ("Theorem D(ii)", "IsingScaling.Rotor.HeisenbergField.FerromagneticLeeYang.partition_ne_zero"),
    ("Theorem D(ii)", "IsingScaling.Rotor.HeisenbergField.PhysicalRotation.exists_vanishing_limit"),
    ("Theorem D(ii)", "IsingScaling.Rotor.HeisenbergField.PhysicalRotation.sharp_rotation"),
    ("Theorem D(ii)", "IsingScaling.Rotor.HeisenbergField.PhysicalRotation.rounded_rotation"),
    ("Theorem D(iii)", "IsingScaling.Rotor.PressureSelection.ONFamily.exists_on_family_rotation_full"),
    ("Theorem D(iv)", "IsingScaling.Rotor.PressureSelection.HighTemperature.exists_unique_nearest_gibbs_tanh"),
    ("Corollary 6.11", "IsingScaling.Rotor.IsStationaryFreeCubePairLimit.surface_isotropic"),
    ("Appendix B", "IsingScaling.Rotor.IsStationaryFreeCubePairLimit.raw_angular_even_lattice"),
]


def main() -> int:
    probe = "import MathlibProbe\n" + "\n".join(f"#print axioms {name}" for _, name in DECLARATIONS) + "\n"
    run = subprocess.run(["lake", "env", "lean", "--stdin"], input=probe, cwd=PROJECT,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        sys.stderr.write(run.stdout)
        return run.returncode
    found = {}
    for name, report in re.findall(
            r"^'([\w.']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
            run.stdout, re.MULTILINE):
        found[name] = {a.strip() for a in report.split(",") if a.strip()}
    failed = False
    for statement, name in DECLARATIONS:
        axioms = found.get(name)
        ok = axioms is not None and axioms <= STANDARD
        failed |= not ok
        shown = "missing" if axioms is None else ", ".join(sorted(axioms)) or "none"
        print(f"{'PASS' if ok else 'FAIL'}  {statement:<22} {name}  [{shown}]")
    print(f"{len(DECLARATIONS)} declarations checked; "
          + ("all use only standard axioms." if not failed else "FAILURES above."))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
