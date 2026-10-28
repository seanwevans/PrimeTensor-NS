#!/usr/bin/env python3
"""Register the exact-anchor cofinal critical-width PDE bridge."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorCofinal244'
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ANCHOR = Path("PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorSource244.lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = ('h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244', 'h3Path_exactAnchorCriticalWidth_forces_physicalEnergySource244', 'h3Path_exactAnchorCanonicalIndex_physicalAmplification244')

def main():
    for path in (SOURCE, ANCHOR, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    contents = [SOURCE.read_text(), ANCHOR.read_text()]
    for data in contents:
        if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", data, re.M):
            raise SystemExit("Proof placeholder or axiom found")
    for name in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(name) + r"\b", contents[0], re.M):
            raise SystemExit(f"Missing theorem: {name}")
    if "h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244" not in contents[1]:
        raise SystemExit("Missing strengthened source constructor")
    new_import = "import " + MODULE
    lines = ROOT.read_text().splitlines()
    if new_import not in lines:
        ROOT.write_text("\n".join(lines + [new_import]) + "\n")
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")] + [new_import]))
    rest = [line for line in lines if not line.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        full_name = "PrimeTensor.FirstMonomialTriad." + name
        for statement in ("#check " + full_name, "#print axioms " + full_name):
            if statement not in rest:
                rest.append(statement)
    new = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if new != old:
        AUDIT.write_text(new)
    print(f"Registered {len(THEOREMS)} exact-anchor cofinal theorems")

if __name__ == "__main__":
    main()
