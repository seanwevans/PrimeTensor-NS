#!/usr/bin/env python3
"""Idempotently register intrinsic Schwartz shape ratios and orbit normalization."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3SchwartzShapeOrbitNormalization"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalRealSchwartz_sharpShapeDenominator",
    "lowNormalRealSchwartz_sharpShapeRatio",
    "lowNormalRealSchwartz_sharpShapeDenominator_real_smul",
    "lowNormalRealSchwartz_sharpShapeDenominator_dilation",
    "lowNormalRealSchwartz_sharpShapeRatio_real_smul",
    "lowNormalRealSchwartz_sharpShapeRatio_dilation",
    "lowNormalRealSchwartz_positiveEndpoints_exist_unitOrbitRepresentative",
    "lowNormalRealSchwartz_sharpShapeRatio_excess_rulesOut_uniform",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        kind = "noncomputable def" if name in NAMES[:2] else "theorem"
        if f"{kind} {name}" not in source:
            raise SystemExit(f"Missing declaration: {name}")
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
    print("Registered intrinsic Schwartz shape ratio and normalized orbit")


if __name__ == "__main__":
    main()
