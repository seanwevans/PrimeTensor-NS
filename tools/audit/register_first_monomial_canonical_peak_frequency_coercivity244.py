#!/usr/bin/env python3
"""Register exact kinetic-carrier/frequency-resolved physical H³ coercivity results."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource"
    "SpectralFiniteAnnulusPDECanonicalPeakFrequencyCoercivity244"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3Path_spectralSupSquare_le_lowPlusHigh244",
    "h3Path_physicalSpectralSupSquare_le_kineticPlusHigh244",
    "h3Path_physicalSpectralSupSquare_radiusDissipation244",
    "h3Path_physicalSpectralPeak_halfMassHigh244",
    "h3Path_physicalSpectralPeak_halfDissipation244",
    "h3Path_radialSobolevCeiling_le_four_sixth244",
    "h3Path_physicalPeak_sixthThreshold_forces_dissipation244",
    "h3Path_cofinalSpectralPeaks_eventualRadiusDissipation244",
    "h3Path_disjointPeakHeightWidthCost_summable244",
    "h3Path_disjointPeakHeightWidthCost_tendsto_zero244",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    source = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", source, re.M):
        raise SystemExit("Proof placeholder or axiom forbidden")
    for theorem in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(theorem) + r"\b", source, re.M):
            raise SystemExit(f"Missing theorem: {theorem}")
    new_import = "import " + MODULE
    lines = ROOT.read_text().splitlines()
    if new_import not in lines:
        ROOT.write_text("\n".join(lines + [new_import]) + "\n")
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith("import ")] + [new_import]))
    rest = [x for x in lines if not x.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        name = "PrimeTensor.FirstMonomialTriad." + theorem
        for statement in ("#check " + name, "#print axioms " + name):
            if statement not in rest:
                rest.append(statement)
    revised = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if revised != original:
        AUDIT.write_text(revised)
    print(f"Registered {len(THEOREMS)} physical spectral-peak frequency-coercivity theorems.")


if __name__ == "__main__":
    main()
