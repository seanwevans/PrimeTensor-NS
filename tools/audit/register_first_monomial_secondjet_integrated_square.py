#!/usr/bin/env python3
"""Idempotently register the integrated Fréchet-coordinate energy bridge."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetIntegratedFrechetSquare"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalPoint3_fderiv_integral_sq_le_card_mul_partials",
    "lowNormalSchwartz_integral_physicalFrechet_sq_le_coordinateMass",
    "lowNormalRealSchwartz_secondJet_integratedFrechet_sq_le_thirdJetMass",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    body = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in body:
            raise SystemExit(f"Missing theorem: {name}")
    imp = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text("\n".join(root_lines + [imp]) + "\n")
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in audit_lines if s.startswith("import ")] + [imp]))
    audit_body = [s for s in audit_lines if not s.startswith("import ")]
    while audit_body and not audit_body[0].strip():
        audit_body.pop(0)
    for name in NAMES:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + fq, "#print axioms " + fq):
            if cmd not in audit_body:
                audit_body.append(cmd)
    result = "\n".join(imports + [""] + audit_body).rstrip() + "\n"
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print("Registered integrated second-jet Frechet-coordinate square comparison")

if __name__ == "__main__":
    main()
