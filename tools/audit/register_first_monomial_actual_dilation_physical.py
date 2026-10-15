#!/usr/bin/env python3
"""Idempotently register the Point3 dilation and physical divergence theorems."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3ActualDilationPhysical"
)
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
SRC = Path(MODULE.replace(".", "/") + ".lean")
NAMES = (
    "lowNormalH3Point3ToFourier_smul",
    "lowNormalRealSchwartzPoint3Velocity_dilation_apply",
    "lowNormalRealSchwartzPoint3Velocity_spatial_d_dilation",
    "lowNormalRealSchwartzPoint3Velocity_divergence_dilation",
    "lowNormalRealSchwartzPoint3Velocity_divergence_zero_dilation",
)


def ensure_line(path: Path, line: str):
    if not path.is_file():
        raise SystemExit(f"Required file is missing: {path}")
    lines = path.read_text().splitlines()
    if line not in lines:
        path.write_text("\n".join(lines + [line]) + "\n")


def main():
    if not SRC.is_file():
        raise SystemExit(f"Missing Lean module: {SRC}")
    source = SRC.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing theorem contract: {name}")
    ensure_line(ROOT, "import " + MODULE)
    # Audits contain #check commands, so imports must precede those commands.
    # Normalize pre-existing appended imports as well, without dropping any.
    if not AUDIT.is_file():
        raise SystemExit(f"Required audit file is missing: {AUDIT}")
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in audit_lines if line.startswith("import ")] +
        ["import " + MODULE]
    ))
    body = [line for line in audit_lines if not line.startswith("import ")]
    AUDIT.write_text("\n".join(imports + [""] + body).rstrip() + "\n")
    for name in NAMES:
        qname = "PrimeTensor.FirstMonomialTriad." + name
        ensure_line(AUDIT, "#check " + qname)
        ensure_line(AUDIT, "#print axioms " + qname)
    print("Registered Point3 dilation and physical solenoidality theorems")


if __name__ == "__main__":
    main()
