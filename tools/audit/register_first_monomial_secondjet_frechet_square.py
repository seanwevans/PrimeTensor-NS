#!/usr/bin/env python3
"""Idempotently register the honest sup-norm Fréchet/coordinate square bridge."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetFrechetCoordinateSquare"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalPoint3_fderiv_sq_le_card_mul_partial_sq",
    "lowNormalRealSchwartz_secondJet_physicalFrechet_sq_le_thirdJetSquares",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    code = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in code:
            raise SystemExit(f"Missing theorem: {name}")
    imp = "import " + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text("\n".join(lines + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    body = [s for s in lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + fq, "#print axioms " + fq):
            if cmd not in body:
                body.append(cmd)
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print("Registered second-jet pointwise Frechet-coordinate square bound")

if __name__ == "__main__":
    main()
