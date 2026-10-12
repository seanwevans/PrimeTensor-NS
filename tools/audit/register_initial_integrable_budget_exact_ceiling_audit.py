#!/usr/bin/env python3
"""Idempotently register exact kinetic ceiling and deficit audit declarations."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialIntegrableBudgetExactKineticCeiling")
CHECKS = [
    "h3Audit_initialIntegrableBudget_cofinalApproximateAnchors",
    "h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling",
    "h3Audit_initialIntegrableBudget_globalPhysicalNormCeiling",
    "h3Audit_initialHilbert_selfPairDeficit_of_kineticCeiling",
    "h3Audit_initialSubcriticalBudget_physicalSelfPairDeficit",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run at repository root")
    import_stmt = "import " + MODULE
    if import_stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Exact positive kinetic ceiling from an initial L1 budget.\n")
            f.write(import_stmt + "\n")
    existing = set(CONTRACTS.read_text().splitlines())
    missing = [x for x in CHECKS if "#check " + x not in existing]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Initial L1 budget: exact positive kinetic ceiling and self-pair deficit.\n")
            for decl in missing:
                f.write("#check " + decl + "\n")
                f.write("#print axioms " + decl + "\n")
    print(f"Exact kinetic ceiling: added {len(missing)} theorem checks")

if __name__ == "__main__":
    main()
