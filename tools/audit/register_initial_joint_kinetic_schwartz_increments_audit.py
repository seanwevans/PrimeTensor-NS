#!/usr/bin/env python3
"""Idempotent audit integration of joint sampled kinetic/Schwartz increments."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialJointKineticSchwartzIncrements")
CHECKS = [
    "h3Audit_initialScalarPositiveIncrements_anchoredFTC_of_sequence",
    "H3AuditInitialSchwartzScalarPositiveIncrementsOn",
    "h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_jointSequence",
    "h3Audit_initialJointKineticSchwartzSequence_sampledStrongTrace",
    "H3AuditInitialJointKineticSchwartzIncrementData",
    "h3Audit_initialJointKineticSchwartzIncrements_physicalAndKineticRightTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from PrimeTensor-NS root")
    stmt = "import " + MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Joint sampled kinetic and Schwartz weak initial trace via positive-time increments.\n")
            f.write(stmt + "\n")
    current = set(CONTRACTS.read_text().splitlines())
    missing = [x for x in CHECKS if "#check " + x not in current]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Joint sampled weak/kinetic data with scalar positive-time increments.\n")
            for x in missing:
                f.write("#check " + x + "\n")
                if not x.startswith("H3Audit"):
                    f.write("#print axioms " + x + "\n")
    print(f"Joint kinetic/Schwartz increments: {len(missing)} new checks")

if __name__ == "__main__":
    main()
