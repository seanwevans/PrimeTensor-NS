#!/usr/bin/env python3
"""Idempotent registration of the actual-dilation Jacobian theorems."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3ActualDilationJacobian"
)
IMPORT = "import " + MODULE
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
SRC = Path("PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/") / (MODULE.rsplit(".", 1)[-1] + ".lean")
NAMES = [
    "lowNormalH3Fourier_finrank_three",
    "lowNormalH3Fourier_integral_comp_positive_smul",
    "lowNormalSchwartzDilation_integral_sq",
    "lowNormalSchwartzDilation_integral_sq_lineDeriv",
    "lowNormalSchwartzDilation_integral_sq_twoLineDerivs",
    "lowNormalSchwartzDilation_integral_sq_threeLineDerivs",
    "lowNormalSchwartzDilation_integral_sq_fourLineDerivs",
]


def register(path: Path) -> None:
    if not path.is_file():
        raise SystemExit(f"Missing required root/audit file: {path}")
    original = path.read_text()
    if IMPORT in original.splitlines():
        return
    path.write_text(original.rstrip("\n") + "\n" + IMPORT + "\n")


def main() -> None:
    if not SRC.is_file():
        raise SystemExit(f"Missing new Lean source: {SRC}")
    source = SRC.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Expected theorem missing from new source: {name}")
    register(ROOT)
    register(AUDIT)
    audit = AUDIT.read_text()
    lines = []
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for command in ("#check", "#print axioms"):
            line = f"{command} {qualified}"
            if line not in audit.splitlines():
                lines.append(line)
    if lines:
        AUDIT.write_text(audit.rstrip("\n") + "\n\n" + "\n".join(lines) + "\n")
    print("Registered actual Schwartz dilation Jacobian and theorem contracts")


if __name__ == "__main__":
    main()
