#!/usr/bin/env python3
"""Idempotently register initial Schwartz weak/kinetic strong trace audit."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialSchwartzWeakEnergyStrongTrace")
CHECKS = [
    "h3Audit_initialHilbert_approxProbeSquaredDefect_le",
    "h3Audit_initialHilbert_strong_of_denseWeak_energyCeiling",
    "H3AuditInitialSchwartzRightWeakTrace",
    "h3Audit_initialBudget_SchwartzWeak_implies_physicalAndKineticRightTrace",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from PrimeTensor-NS repository root")
    stmt = "import " + MODULE
    if stmt not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- Physical strong initial trace from dense Schwartz weak initial data.\n")
            f.write(stmt + "\n")
    previous = set(CONTRACTS.read_text().splitlines())
    missing = [decl for decl in CHECKS if "#check " + decl not in previous]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Physical dense Schwartz weak initial data plus kinetic energy.\n")
            for decl in missing:
                f.write("#check " + decl + "\n")
                if not decl.startswith("H3Audit"):
                    f.write("#print axioms " + decl + "\n")
    print(f"Schwartz weak/kinetic strong trace: {len(missing)} new checks")

if __name__ == "__main__":
    main()
