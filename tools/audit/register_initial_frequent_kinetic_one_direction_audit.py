#!/usr/bin/env python3
"""Idempotently register frequent kinetic + single self-pairing scalar audit."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialFrequentKineticOneDirectionIncrements")
CHECKS = [
    "h3Audit_initialOneDirectionPositiveIncrements_selfPairRightTrace",
    "h3Audit_initialPhysicalCeilingAndSelfPair_rightTraces",
    "H3AuditInitialFrequentKineticOneDirectionIncrementData",
    "h3Audit_initialOneDirectionIncrements_physicalSquaredError",
    "h3Audit_initialFrequentKineticOneDirection_physicalAndKineticRightTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from PrimeTensor-NS repository root")
    stmt = "import " + MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- One initial-data scalar direction with frequent kinetic samples.\n")
            f.write(stmt + "\n")
    previous = set(CONTRACTS.read_text().splitlines())
    missing = [d for d in CHECKS if "#check " + d not in previous]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Single physical initial self-pair scalar increments and energy.\n")
            for decl in missing:
                f.write("#check " + decl + "\n")
                if not decl.startswith("H3Audit"):
                    f.write("#print axioms " + decl + "\n")
    print(f"Frequent kinetic one-direction audit: added {len(missing)} checks")

if __name__ == "__main__":
    main()
