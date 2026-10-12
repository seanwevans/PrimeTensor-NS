#!/usr/bin/env python3
"""Idempotently register direct initial strong L² trace/kinetic audit."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialEnergySelfPairingStrongTrace")
CHECKS = [
    "h3Audit_initialEnergySelfPairing_squaredDefect_le",
    "h3Audit_initialHilbert_strong_of_energyCeiling_selfPairing",
    "h3Audit_initialBudget_selfPairing_physicalSquaredDefect",
    "h3Audit_initialBudget_selfPairing_implies_physicalAndKineticRightTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run at the PrimeTensor-NS repository root")
    imp = "import " + MODULE
    if imp not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Direct initial physical strong L2 trace from kinetic budget and self pairing.\n")
            f.write(imp + "\n")
    current = set(CONTRACTS.read_text().splitlines())
    missing = [x for x in CHECKS if "#check " + x not in current]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Direct kinetic-budget + one-vector self-pairing strong initial trace.\n")
            for x in missing:
                f.write("#check " + x + "\n")
                f.write("#print axioms " + x + "\n")
    print(f"Direct initial strong trace: {len(missing)} new checks")

if __name__ == "__main__":
    main()
