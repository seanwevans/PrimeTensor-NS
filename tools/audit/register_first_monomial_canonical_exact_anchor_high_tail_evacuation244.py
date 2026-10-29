#!/usr/bin/env python3
"""Register exact physical high-tail evacuation from canonical PDE cliffs."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHighTailEvacuation244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3Path_physicalHighTail_outerPartition244",
    "h3Path_physicalPDE_cliff_forces_highTailEvacuation244",
    "h3Path_exactAnchorPDE_dip_forces_highTailEvacuation244",
    "h3Path_scalar_lowBudget_highTail_anchorLower244",
    "h3Path_noL2Trace_exactAnchor_persistentCharge_highTailEvacuation244",
)
DEFS = (
    "h3PathCubicAnnulusOuterLowLinearRate244",
    "h3PathCubicAnnulusOuterLowQuadraticRate244",
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing file: {p}")
    content = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", content, re.M):
        raise SystemExit("Unproved placeholder or axiom")
    for name in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(name) + r"\b", content, re.M):
            raise SystemExit(f"Missing theorem: {name}")
    for name in DEFS:
        if not re.search(r"^\s*(?:noncomputable\s+)?def\s+" + re.escape(name) + r"\b", content, re.M):
            raise SystemExit(f"Missing definition: {name}")
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
    for name in DEFS + THEOREMS:
        full = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + full, "#print axioms " + full):
            if cmd not in rest:
                rest.append(cmd)
    updated = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if updated != existing:
        AUDIT.write_text(updated)
    print(f"Registered {len(THEOREMS)} theorems and {len(DEFS)} definitions")

if __name__ == "__main__":
    main()
