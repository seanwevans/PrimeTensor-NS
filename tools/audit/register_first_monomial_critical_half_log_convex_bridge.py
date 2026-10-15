#!/usr/bin/env python3
"""Register the division-free log-convex/balanced-shape bridge idempotently."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3CriticalHalfLogConvexBridge"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "criticalHalf_adjacentCauchy_implies_cubicLogConvex",
    "criticalHalf_balancedScale_energyPolynomial_upper",
    "criticalHalf_balancedScale_polynomialNecessary",
    "lowNormalRealSchwartz_solenoidalBalancedShape_necessary",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing theorem contract: {name}")
    module_import = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if module_import not in root_lines:
        ROOT.write_text("\n".join(root_lines + [module_import]) + "\n")
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in audit_lines if line.startswith("import ")] +
        [module_import]
    ))
    body = [line for line in audit_lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for command in ("#check " + qualified, "#print axioms " + qualified):
            if command not in body:
                body.append(command)
    AUDIT.write_text("\n".join(imports + [""] + body).rstrip() + "\n")
    print("Registered conditional log-convex and balanced-shape bridge")


if __name__ == "__main__":
    main()
