#!/usr/bin/env python3
"""Idempotently register genuine H3 Schwartz dilation finite-sum theorems."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3ActualDilationEnergySums"
)
IMPORT = "import " + MODULE
SRC = Path("PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/") / (
    MODULE.rsplit(".", 1)[-1] + ".lean"
)
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = [
    "lowNormalRealSchwartzH3Energy0_dilation",
    "lowNormalRealSchwartzH3Energy1_dilation",
    "lowNormalRealSchwartzH3Energy2_dilation",
    "lowNormalRealSchwartzH3Energy3_dilation",
    "lowNormalRealSchwartzH3TopDissipation_dilation",
    "lowNormalRealSchwartzH3Energy_dilation",
]


def register_import(path: Path) -> None:
    lines = path.read_text().splitlines()
    if IMPORT in lines:
        return
    if path == AUDIT:
        # Lean import declarations must precede the audit's #check commands.
        pos = next((i for i, line in enumerate(lines)
                    if line.startswith("#check") or line.startswith("#print")),
                   len(lines))
        lines.insert(pos, IMPORT)
    else:
        lines.append(IMPORT)
    path.write_text("\n".join(lines).rstrip("\n") + "\n")


def main() -> None:
    if not SRC.is_file():
        raise SystemExit(f"Missing new Lean source: {SRC}")
    source = SRC.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing required theorem: {name}")
    for path in (ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing registration target: {path}")
        register_import(path)
    lines = AUDIT.read_text().splitlines()
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for command in ("#check", "#print axioms"):
            line = command + " " + qualified
            if line not in lines:
                lines.append(line)
    AUDIT.write_text("\n".join(lines).rstrip("\n") + "\n")
    print("Registered the actual H3 Schwartz energy and dissipation dilation sums")


if __name__ == "__main__":
    main()
