#!/usr/bin/env python3
"""Idempotent root import / contract checks for Schwartz Bochner transfer."""
from pathlib import Path
ROOT=Path("PrimeTensor.lean")
CONTRACTS=Path("tools/audit/Contracts.lean")
MODULE=("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
        "OneComponentInitialSchwartzBochnerOneDirectionTransfer")
CHECKS=[
    "h3Audit_initialSchwartzBochner_extends_hilbertIncrement",
    "h3Audit_initialBochner_intervalInner_comm",
    "h3Audit_initialSchwartzBochner_allPhysicalScalarIncrements",
    "H3AuditInitialFrequentKineticSchwartzBochnerData",
    "h3Audit_initialSchwartzBochner_implies_oneDirectionData",
    "h3Audit_initialSchwartzBochner_physicalAndKineticRightTrace",
]
def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from PrimeTensor-NS root")
    stmt="import "+MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Transfer Schwartz-tested Bochner momentum to initial physical vector.\n")
            f.write(stmt+"\n")
    old=set(CONTRACTS.read_text().splitlines())
    missing=[x for x in CHECKS if "#check "+x not in old]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Initial Schwartz Bochner momentum to one-vector scalar FTC.\n")
            for x in missing:
                f.write("#check "+x+"\n")
                if not x.startswith("H3Audit"):
                    f.write("#print axioms "+x+"\n")
    print(f"Schwartz Bochner one-direction transfer: {len(missing)} new checks")
if __name__=="__main__":
    main()
