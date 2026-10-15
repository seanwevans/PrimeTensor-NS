#!/usr/bin/env python3
"""Idempotently register the genuine two-parameter H3 shape invariant."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3CriticalHalfBalancedShape"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = [
    "lowNormalRealSchwartzH3Energy0_real_smul",
    "lowNormalRealSchwartzH3Energy3_real_smul",
    "lowNormalRealSchwartz_criticalHalfBalancedExcess_real_smul",
    "lowNormalRealSchwartz_criticalHalfBalancedExcess_dilation",
    "lowNormalRealSchwartz_Point3Solenoidal_dilation",
    "lowNormalRealSchwartz_positiveBalancedExcess_real_smul",
    "lowNormalRealSchwartz_positiveBalancedExcess_dilation",
]
DEFINITION = "lowNormalRealSchwartz_criticalHalfBalancedExcess"


def main() -> None:
    if not SOURCE.is_file():
        raise SystemExit(f"Missing source: {SOURCE}")
    source = SOURCE.read_text()
    if f"def {DEFINITION}" not in source:
        raise SystemExit(f"Definition contract missing: {DEFINITION}")
    for name in THEOREMS:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Theorem contract missing: {name}")
    for path in (ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing registration destination: {path}")

    root = ROOT.read_text().splitlines()
    imp = "import " + MODULE
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")

    audit = AUDIT.read_text().splitlines()
    if imp not in audit:
        pos = next((i for i, line in enumerate(audit) if line.startswith("#")), len(audit))
        audit.insert(pos, imp)
    for name in [DEFINITION, *THEOREMS]:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check", "#print axioms"):
            line = f"{cmd} {qualified}"
            if line not in audit:
                audit.append(line)
    rewritten = "\n".join(audit).rstrip("\n") + "\n"
    if rewritten != AUDIT.read_text():
        AUDIT.write_text(rewritten)
    print("Registered balanced H3 Schwartz shape scaling contracts")


if __name__ == "__main__":
    main()
