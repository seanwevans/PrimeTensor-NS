#!/usr/bin/env python3
"""Idempotently register the real Schwartz adjacent-energy IBP audit."""
from pathlib import Path

MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentEnergyIBP")
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalSchwartz_lineDeriv_integral_mul_eq_neg",
    "lowNormalSchwartz_lineDeriv_square_by_parts",
    "lowNormalRealSchwartzH3Energy1_by_parts",
    "lowNormalRealSchwartzH3Energy2_by_parts",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing: {path}")
    for name in NAMES:
        if f"theorem {name}" not in SOURCE.read_text():
            raise SystemExit(f"Missing theorem: {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] + [imp]
    ))
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
    print("Registered real Schwartz adjacent-energy integration by parts")


if __name__ == "__main__":
    main()
