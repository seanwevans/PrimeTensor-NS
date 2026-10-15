#!/usr/bin/env python3
"""Idempotently register unconditional physical Schwartz cubic interpolation."""
from pathlib import Path

MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3SchwartzUnconditionalLogConvex")
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "criticalHalf_relaxedAdjacentCauchy_implies_cubicLogConvex",
    "lowNormalRealSchwartzH3Energy_unconditional_cubicLogConvex",
    "criticalHalf_relaxedLogConvex_balancedScale_energyUpper",
    "lowNormalRealSchwartzH3Energy_unconditional_balancedScale_upper",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
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
    target = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != target:
        AUDIT.write_text(target)
    print("Registered unconditional real Schwartz H3 cubic interpolation")

if __name__ == "__main__":
    main()
