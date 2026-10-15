#!/usr/bin/env python3
"""Idempotent registration for unconditional complete adjacent H3 Cauchy sums."""
from pathlib import Path

MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentJointCauchy")
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalRealSchwartzH3Energy1_sq_le_joint_diagonal",
    "lowNormalRealSchwartzH3Energy2_diagonal_le_full",
    "lowNormalRealSchwartzH3Energy1_sq_le_axisCard_mul_E0_E2",
    "lowNormalRealSchwartzH3Energy2_sq_le_joint_diagonal",
    "lowNormalRealSchwartzH3Energy3_diagonal_le_full",
    "lowNormalRealSchwartzH3Energy2_sq_le_axisCard_mul_E1_E3",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    content = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in content:
            raise SystemExit(f"Missing theorem: {name}")
    import_line = "import " + MODULE
    roots = ROOT.read_text().splitlines()
    if import_line not in roots:
        ROOT.write_text("\n".join(roots + [import_line]) + "\n")
    raw = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in raw if s.startswith("import ")] + [import_line]))
    body = [s for s in raw if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        target = "PrimeTensor.FirstMonomialTriad." + name
        for prefix in ("#check ", "#print axioms "):
            line = prefix + target
            if line not in body:
                body.append(line)
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print("Registered six unconditional joint Schwartz adjacent-energy contracts")

if __name__ == "__main__":
    main()
