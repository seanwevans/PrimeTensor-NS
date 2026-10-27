#!/usr/bin/env python3
"""Register the same-witness canonical high-radial dissipation-cost lemmas."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialDissipationCost244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3Path_highRadialMass_le_fullDissipationAt244",
    "h3Path_highRadialMassEscape_forces_dissipationPeaks244",
    "h3Path_disjointHighRadialMassFloors_finiteDissipationCost244",
    "h3Path_finiteHeightBudget_forces_widthCollapse244",
    "h3Path_disjointHighRadialMassEscape_forces_widthCollapse244",
    "h3Path_noL2Trace_canonicalWidth_highRadialDissipationPeaks244",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    source = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", source, re.M):
        raise SystemExit("Unproved placeholder or axiom")
    for theorem in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(theorem) + r"\b", source, re.M):
            raise SystemExit(f"Missing theorem: {theorem}")
    new_import = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if new_import not in root:
        ROOT.write_text("\n".join(root + [new_import]) + "\n")
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
    print(f"Registered {len(THEOREMS)} canonical high-radial dissipation-cost theorems.")

if __name__ == "__main__":
    main()
