#!/usr/bin/env python3
"""Idempotently register frequent kinetic + testwise Schwartz initial trace."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialFrequentKineticTestwiseSchwartzIncrements")
CHECKS = [
    "h3Audit_initialFrequentScalarSequence_cofinalApproximateAnchors",
    "h3Audit_initialFrequentKineticSequence_exactPositiveCeiling",
    "h3Audit_initialFrequentKineticSequence_eventualUpper",
    "h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_testwiseSequences",
    "h3Audit_initialSchwartzPositiveIncrements_syncTestwiseWeakToSequence",
    "H3AuditInitialFrequentKineticTestwiseSchwartzIncrementData",
    "h3Audit_initialFrequentTestwiseData_implies_jointKineticSchwartzData",
    "h3Audit_initialFrequentKineticTestwiseIncrements_physicalAndKineticRightTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from PrimeTensor-NS repository root")
    stmt = "import " + MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Frequent kinetic samples and independently sampled Schwartz initial tests.\n")
            f.write(stmt + "\n")
    previous = set(CONTRACTS.read_text().splitlines())
    missing = [x for x in CHECKS if "#check " + x not in previous]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Frequent kinetic/testwise Schwartz initial trace bridge.\n")
            for item in missing:
                f.write("#check " + item + "\n")
                if not item.startswith("H3Audit"):
                    f.write("#print axioms " + item + "\n")
    print(f"Frequent kinetic + testwise Schwartz: added {len(missing)} checks")

if __name__ == "__main__":
    main()
