#!/usr/bin/env python3
"""Register the physical H3 fourth-power cost of canonical minimal annuli."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorEnergyFourth244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = ('h3Path_actualLowRadialDissipation_le_threeSpectralSup244', 'h3Path_scalarCriticalOuter_cubicCrossing_forces_energyFourth244', 'h3Path_exactAnchorCriticalOuter_forces_physicalEnergyFourth244', 'h3Path_exactAnchorCanonicalWidth_forces_eventualEnergyFourth244', 'h3Path_noL2Trace_exactAnchorCanonicalWidth_energyFourth244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    src = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", src, re.M):
        raise SystemExit("Proof placeholder or axiom")
    for theorem in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(theorem) + r"\b", src, re.M):
            raise SystemExit(f"Missing theorem: {theorem}")
    new_import = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if new_import not in root_lines:
        ROOT.write_text("\n".join(root_lines + [new_import]) + "\n")
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")] + [new_import]))
    rest = [line for line in lines if not line.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        full_name = "PrimeTensor.FirstMonomialTriad." + theorem
        for statement in ("#check " + full_name, "#print axioms " + full_name):
            if statement not in rest:
                rest.append(statement)
    new = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if new != old:
        AUDIT.write_text(new)
    print(f"Registered {len(THEOREMS)} exact-anchor fourth-energy theorems")

if __name__ == "__main__":
    main()
