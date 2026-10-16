#!/usr/bin/env python3
"""Idempotently register the coefficient-one Schwartz L4 interpolation theorem."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzQuarticL2L6"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalSchwartz_cube",
    "lowNormalSchwartz_cube_apply",
    "lowNormalSchwartz_integral_fourth_sq_le_second_mul_sixth",
    "lowNormalSchwartz_family_integral_fourth_sq_le_second_mul_sixth",
    "lowNormalRealSchwartz_secondJets_quartic_sq_le_E2_mul_sixth",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    code = SOURCE.read_text()
    for name in NAMES:
        if name not in code:
            raise SystemExit(f"Missing public declaration: {name}")
    imp = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text("\n".join(root_lines + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")] + [imp]))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for command in ("#check " + qualified, "#print axioms " + qualified):
            if command not in body:
                body.append(command)
    new = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != new:
        AUDIT.write_text(new)
    print("Registered actual Schwartz quartic L2/L6 interpolation")

if __name__ == "__main__":
    main()
