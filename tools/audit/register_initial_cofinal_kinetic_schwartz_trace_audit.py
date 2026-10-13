#!/usr/bin/env python3
"""Idempotently register cofinal kinetic sequence / Schwartz initial trace audit."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialCofinalKineticSchwartzTrace")
CHECKS = [
    "h3Audit_initialScalarCofinalApproximateAnchors_of_sequence",
    "h3Audit_initialCofinalApproximateKineticSequence_exactCeiling",
    "h3Audit_initialCofinalKinetic_SchwartzWeak_physicalAndKineticTrace",
    "h3Audit_initialCofinalKinetic_SchwartzScalarFTC_physicalAndKineticTrace",
    "h3Audit_initialCofinalKinetic_SchwartzDerivativeSequence_physicalAndKineticTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run at the PrimeTensor-NS repository root")
    stmt = "import " + MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Initial Schwartz physical L2 trace from one approximate kinetic sequence.\n")
            f.write(stmt + "\n")
    old = set(CONTRACTS.read_text().splitlines())
    missing = [d for d in CHECKS if "#check " + d not in old]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- One right-zero approximate kinetic sequence, strong initial Schwartz trace.\n")
            for d in missing:
                f.write("#check " + d + "\n")
                f.write("#print axioms " + d + "\n")
    print(f"Cofinal kinetic Schwartz initial trace: {len(missing)} new theorem checks")

if __name__ == "__main__":
    main()
