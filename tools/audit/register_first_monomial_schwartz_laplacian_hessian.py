#!/usr/bin/env python3
"""Idempotently register the actual Schwartz Laplacian/Hessian identities."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3SchwartzLaplacianHessianContraction"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalSchwartz_axisLaplacian",
    "lowNormalSchwartz_axisLaplacian_sq_integral_eq_hessian",
    "lowNormalRealSchwartzH3Energy2_eq_sum_axisLaplacian_sq",
    "lowNormalRealSchwartzH3Energy3_eq_sum_firstJet_axisLaplacian_sq",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        kind = "noncomputable def" if name == NAMES[0] else "theorem"
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
    result = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print("Registered actual 27/81-slot Schwartz Laplacian/Hessian identities")


if __name__ == "__main__":
    main()
