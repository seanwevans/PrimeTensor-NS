#!/usr/bin/env python3
"""Register canonical width physical source maxima -> simultaneous H3/state peaks."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalWidthJointH3State244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3Path_projectedSourceThreshold_forces_jointH3Spectral244",
    "h3Path_noL2Trace_finiteDissipation_canonicalWidth_jointH3StatePeaks244",
    "h3Path_fixedSourceMaximizers_forces_jointH3SpectralTendsto244",
    "h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    src = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", src, re.M):
        raise SystemExit("Unproved placeholder or axiom")
    for theorem in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(theorem) + r"\b", src, re.M):
            raise SystemExit(f"Missing theorem: {theorem}")
    new_import = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if new_import not in root:
        ROOT.write_text("\n".join(root + [new_import]) + "\n")
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")] + [new_import]))
    rest = [line for line in lines if not line.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        name = "PrimeTensor.FirstMonomialTriad." + theorem
        for check in ("#check " + name, "#print axioms " + name):
            if check not in rest:
                rest.append(check)
    revised = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if revised != original:
        AUDIT.write_text(revised)
    print(f"Registered {len(THEOREMS)} canonical joint H3/state theorems.")

if __name__ == "__main__":
    main()
