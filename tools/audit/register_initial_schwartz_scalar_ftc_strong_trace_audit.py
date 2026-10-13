#!/usr/bin/env python3
"""Idempotently register scalar Schwartz weak-FTC strong initial trace."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialSchwartzScalarFTCStrongTrace")
CHECKS = [
    "H3AuditInitialSchwartzAnchoredScalarFTCOn",
    "h3Audit_initialSchwartzAnchoredScalarFTC_weakRightTrace",
    "h3Audit_initialSchwartzAnchoredScalarFTC_of_derivativeAndSequence",
    "h3Audit_initialBudget_SchwartzScalarFTC_strongPhysicalAndKineticTrace",
    "h3Audit_initialBudget_SchwartzDerivativeSequence_strongPhysicalAndKineticTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from the PrimeTensor-NS repository root")
    statement = "import " + MODULE
    if statement not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Test-dependent initial Schwartz scalar FTC and strong physical trace.\n")
            f.write(statement + "\n")
    prior = set(CONTRACTS.read_text().splitlines())
    missing = [d for d in CHECKS if "#check " + d not in prior]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Initial weak Schwartz scalar FTC and strong physical L2 trace.\n")
            for d in missing:
                f.write("#check " + d + "\n")
                if not d.startswith("H3Audit"):
                    f.write("#print axioms " + d + "\n")
    print(f"Initial Schwartz scalar FTC audit: added {len(missing)} checks")

if __name__ == "__main__":
    main()
