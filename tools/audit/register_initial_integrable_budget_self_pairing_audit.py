#!/usr/bin/env python3
"""Idempotently register initial L1 kinetic budget + sampled self-pair audit."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialIntegrableBudgetSelfPairing")
CHECKS = [
    "h3Audit_initialIntegrableKineticBudget_rightLimitUpper",
    "h3Audit_initialStrongHilbertLimit_eq_of_integrableBudget_selfPairSequence",
    "H3AuditInitialIntegrableKineticBudgetSelfPairingTrace",
    "h3Audit_initialSubcriticalIntegrableBudgetSelfPairing_identifies_physicalAndKineticRate",
]

def main():
    if not (ROOT.is_file() and CONTRACTS.is_file()):
        raise SystemExit("Run from PrimeTensor-NS root")
    imp = "import " + MODULE
    if imp not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Initial L1 kinetic budget and self-pair: default build and audit.\n")
            f.write(imp + "\n")
    lines = set(CONTRACTS.read_text().splitlines())
    missing = [x for x in CHECKS if "#check " + x not in lines]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Initial integrable kinetic budget and self-pairing trace.\n")
            for x in missing:
                f.write("#check " + x + "\n")
                if not x.startswith("H3Audit"):
                    f.write("#print axioms " + x + "\n")
    print(f"Initial kinetic budget audit: {len(missing)} new checks")

if __name__ == "__main__":
    main()
