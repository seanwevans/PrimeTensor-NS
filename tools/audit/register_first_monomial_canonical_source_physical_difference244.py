#!/usr/bin/env python3
"""Register physical inverse-Fourier source differences and same-witness bound."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourcePhysicalDifference244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3Path_fromFourierRealL2_sub244",
    "h3Path_realPartFourierL2_sub244",
    "h3Path_physicalRawFourierDecoder_sub244",
    "h3Path_physicalRawFourierDecoder_norm_le244",
    "h3Path_physicalLeray_spectralSub_norm_le244",
    "h3Path_physicalLaplacian_spectralSub_norm_le244",
    "h3Path_physicalProjectedSpectralSource_sub_norm_le244",
    "h3Path_actualProjectedSource_temporalSub_norm_le_spectral244",
    "h3Path_noL2Trace_canonicalWidth_physicalSourceSpectralTemporalBound244",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing file: {path}")
    src = SOURCE.read_text()
    if re.search(r"^\s*(?:sorry|admit|axiom)(?:\s|$)", src, re.M):
        raise SystemExit("Unproved placeholder or axiom")
    for th in THEOREMS:
        if not re.search(r"^\s*theorem\s+" + re.escape(th) + r"\b", src, re.M):
            raise SystemExit(f"Missing theorem: {th}")
    new_import = "import " + MODULE
    current = ROOT.read_text().splitlines()
    if new_import not in current:
        ROOT.write_text("\n".join(current+[new_import])+"\n")
    orig = AUDIT.read_text()
    lines = orig.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")]+[new_import]))
    rest = [line for line in lines if not line.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for th in THEOREMS:
        name = "PrimeTensor.FirstMonomialTriad." + th
        for check in ("#check " + name,"#print axioms " + name):
            if check not in rest:
                rest.append(check)
    result = "\n".join(imports+[""]+rest).rstrip()+"\n"
    if result != orig:
        AUDIT.write_text(result)
    print(f"Registered {len(THEOREMS)} physical inverse-Fourier difference theorems.")

if __name__ == "__main__":
    main()
