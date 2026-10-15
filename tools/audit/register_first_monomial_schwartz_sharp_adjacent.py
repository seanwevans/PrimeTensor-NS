#!/usr/bin/env python3
"""Idempotently register both actual coefficient-one Schwartz interpolation modules."""
from pathlib import Path

PREFIX = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
MODULES = (
    PREFIX + "FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentPairing",
    PREFIX + "FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentCauchy",
)
CONTRACTS = {
    MODULES[0]: (
        "lowNormalSchwartz_axisLaplacianMap",
        "lowNormalSchwartz_axisLaplacianMap_apply",
        "lowNormalSchwartz_firstSquares_eq_neg_laplacian_pair",
        "lowNormalRealSchwartzH3Energy1_eq_neg_sum_laplacian_pair",
        "lowNormalRealSchwartzH3Energy2_eq_neg_firstJet_laplacian_pair",
    ),
    MODULES[1]: (
        "lowNormalRealSchwartzH3Energy1_sq_le_E0_mul_E2",
        "lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3",
        "lowNormalRealSchwartzH3Energy_sharp_cubicLogConvex",
        "lowNormalRealSchwartzH3Energy_sharp_balancedScale_upper",
    ),
}
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")


def main():
    for path in (ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    for module in MODULES:
        source = Path(module.replace(".", "/") + ".lean")
        if not source.is_file():
            raise SystemExit(f"Missing Lean source: {source}")
        data = source.read_text()
        for name in CONTRACTS[module]:
            if not any(f"{kind} {name}" in data for kind in
                       ("noncomputable def", "theorem", "@[simp] theorem")):
                raise SystemExit(f"Missing Lean declaration: {name}")
    root_lines = ROOT.read_text().splitlines()
    for module in MODULES:
        imp = "import " + module
        if imp not in root_lines:
            root_lines.append(imp)
    root_result = "\n".join(root_lines).rstrip() + "\n"
    if ROOT.read_text() != root_result:
        ROOT.write_text(root_result)
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] +
        ["import " + module for module in MODULES]
    ))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for module in MODULES:
        for name in CONTRACTS[module]:
            qualified = "PrimeTensor.FirstMonomialTriad." + name
            for command in ("#check " + qualified, "#print axioms " + qualified):
                if command not in body:
                    body.append(command)
    audit_result = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != audit_result:
        AUDIT.write_text(audit_result)
    print("Registered exact coefficient-one physical Schwartz H3 interpolation")


if __name__ == "__main__":
    main()
