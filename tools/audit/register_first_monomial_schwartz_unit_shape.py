#!/usr/bin/env python3
"""Register the exact positive-endpoint to unit-endpoint shape reduction."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzUnitShapeReduction"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalRealSchwartz_unitEndpoints_intermediate_le_one",
    "lowNormalRealSchwartz_unitEndpoints_quadratic_le_four",
    "lowNormalRealSchwartz_positiveEndpoints_ratioBound_iff_unitEndpoints",
    "lowNormalRealSchwartz_unitEndpoints_ratio_le_iff_monomial",
    "lowNormalRealSchwartz_uniform_forces_unitEndpoints_ratioBound",
    "lowNormalRealSchwartz_unitEndpoints_ratioExcess_rulesOut_uniform",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    text = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in text:
            raise SystemExit(f"Missing theorem: {name}")
    imp = "import " + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text("\n".join(roots + [imp]) + "\n")
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
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print("Registered exact unit-endpoint Schwartz shape reduction")


if __name__ == "__main__":
    main()
