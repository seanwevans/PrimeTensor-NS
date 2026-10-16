#!/usr/bin/env python3
"""Idempotently register the exact critical-half seventh-power algebra."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3CriticalHalfSeventhPowerClosure"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "criticalHalf_seventhPower_holderSobolev_closure",
    "criticalHalf_seventhPower_to_quadraticEnergy",
    "lowNormalRealSchwartz_criticalHalf_of_seventhPowerAnalyticInputs",
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
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text("\n".join(root_lines + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] + [imp]
    ))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + qualified, "#print axioms " + qualified):
            if cmd not in body:
                body.append(cmd)
    new = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != new:
        AUDIT.write_text(new)
    print("Registered exact critical-half seventh-power algebra")

if __name__ == "__main__":
    main()
