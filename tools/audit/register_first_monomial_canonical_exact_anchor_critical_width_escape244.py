#!/usr/bin/env python3
"""Register canonical exact-anchor critical-width energy and dissipation escape."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorCriticalWidthEscape244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3Path_strictMono_canonicalRadiusCube_escape244",
    "h3Path_scalar_cubicFourthCost_forces_energyEscape244",
    "h3Path_scalar_energyEscape_forces_threeSpectralEscape244",
    "h3Path_noL2Trace_exactAnchorCriticalWidth_anchorAmplification244",
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing file: {p}")
    text = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", text, re.M):
        raise SystemExit("Unproved placeholder or axiom")
    for th in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(th) + r"\b", text, re.M):
            raise SystemExit(f"Missing theorem: {th}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    existing = AUDIT.read_text()
    lines = existing.splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith("import ")] + [imp]))
    rest = [ln for ln in lines if not ln.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for th in THEOREMS:
        fullname = "PrimeTensor.FirstMonomialTriad." + th
        for cmd in ("#check " + fullname, "#print axioms " + fullname):
            if cmd not in rest:
                rest.append(cmd)
    updated = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if updated != existing:
        AUDIT.write_text(updated)
    print(f"Registered {len(THEOREMS)} exact-anchor critical-width escape theorems")

if __name__ == "__main__":
    main()
