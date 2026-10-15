#!/usr/bin/env python3
"""Idempotent registration of actual critical-half fixed-profile contracts."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3ActualCriticalHalfProfile"
)
IMPORT = "import " + MODULE
SRC = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalRealSchwartzH3Energy0_nonneg",
    "lowNormalRealSchwartzH3Energy1_nonneg",
    "lowNormalRealSchwartzH3Energy2_nonneg",
    "lowNormalRealSchwartzH3Energy3_nonneg",
    "lowNormalRealSchwartzH3TopDissipation_nonneg",
    "lowNormalRealSchwartzH3EnergyQuadratic_eq_sum",
    "lowNormalRealSchwartzH3EnergyQuadratic_dilation",
    "lowNormalRealSchwartzH3Energy_eq_one_add_quadratic",
    "lowNormalRealSchwartzH3EnergyQuadratic_nonneg",
    "lowNormalRealSchwartz_criticalHalf_squared_dilation_of_scalar",
    "lowNormalRealSchwartz_exists_criticalHalf_squared_dilation_coefficient",
    "lowNormalRealSchwartz_exists_criticalHalf_dilation_coefficient",
)


def append_unique(path: Path, entries: list[str]):
    if not path.is_file():
        raise SystemExit(f"Missing required file: {path}")
    lines = path.read_text().splitlines()
    for entry in entries:
        if entry not in lines:
            lines.append(entry)
    new_text = "\n".join(lines).rstrip() + "\n"
    if path.read_text() != new_text:
        path.write_text(new_text)


def main():
    if not SRC.is_file():
        raise SystemExit(f"Missing new Lean module: {SRC}")
    source = SRC.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing theorem contract: {name}")
    append_unique(ROOT, [IMPORT])
    if not AUDIT.is_file():
        raise SystemExit(f"Missing audit file: {AUDIT}")
    original = AUDIT.read_text()
    lines = original.splitlines()
    # Imports must appear before all #check/#print commands.
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] + [IMPORT]
    ))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    merged = "\n".join(imports + [""] + body).rstrip() + "\n"
    if merged != original:
        AUDIT.write_text(merged)
    commands = []
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        commands.extend(["#check " + qualified, "#print axioms " + qualified])
    append_unique(AUDIT, commands)
    print("Registered actual critical-half fixed-profile theorems")


if __name__ == "__main__":
    main()
