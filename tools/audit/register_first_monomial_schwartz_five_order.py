#!/usr/bin/env python3
"""Register exact five-order Schwartz interpolation and audit its axioms."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3SchwartzFiveOrderInterpolation"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "criticalHalf_fiveOrder_adjacentCauchy_implies_quartic",
    "lowNormalRealSchwartzH3Energy_fiveOrder_sharpQuarticInterpolation",
    "lowNormalRealSchwartzH3Energy2_sq_le_E0_mul_topDissipation",
    "lowNormalRealSchwartzH3Energy1_pow_four_le_E0_cube_mul_topDissipation",
    "lowNormalRealSchwartzH3Energy3_pow_four_le_E0_mul_topDissipation_cube",
    "lowNormalRealSchwartzH3Energy3_pos_implies_topDissipation_pos",
    "lowNormalRealSchwartz_positiveEndpoints_shapeDenominator_pos",
    "lowNormalRealSchwartz_unitEndpoints_fiveOrder_corridor",
)


def main() -> None:
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing theorem: {name}")
    new_import = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if new_import not in root_lines:
        ROOT.write_text("\n".join(root_lines + [new_import]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] + [new_import]
    ))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + qualified, "#print axioms " + qualified):
            if cmd not in body:
                body.append(cmd)
    result = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print("Registered exact five-order Schwartz interpolation")


if __name__ == "__main__":
    main()
