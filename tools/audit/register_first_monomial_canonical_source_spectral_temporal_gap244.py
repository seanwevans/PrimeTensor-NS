#!/usr/bin/env python3
"""Register canonical Fourier bilinear source difference and spectral temporal gap."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceSpectralTemporalGap244'
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = ('h3Path_rawLerayFourier_diagonal_sub_eq244', 'h3Path_rawLerayFourier_diagonal_sub_norm_le244', 'h3Path_sourceHigh_forces_anchorSpectralOrDisplacement244', 'h3Path_spectralPeakEscape_anchorOrDisplacement244', 'h3Path_boundedSpectralAnchor_forces_displacementEscape244', 'h3Path_boundedSpectralDisplacement_forces_anchorEscape244', 'h3Path_noL2Trace_canonicalWidth_spectralAnchorOrDisplacement244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing file: {p}")
    src = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", src, re.M):
        raise SystemExit("Found proof placeholder")
    for theorem in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(theorem) + r"\b", src, re.M):
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
        for s in ("#check " + name, "#print axioms " + name):
            if s not in rest:
                rest.append(s)
    result = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if original != result:
        AUDIT.write_text(result)
    print(f"Registered {len(THEOREMS)} spectral temporal-gap theorems")

if __name__ == "__main__":
    main()
