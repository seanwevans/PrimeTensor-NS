#!/usr/bin/env python3
"""Idempotently register the kinetic self-pairing module and contract checks."""
from pathlib import Path

root = Path("PrimeTensor.lean")
contracts = Path("tools/audit/Contracts.lean")
module = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialKineticSelfPairingIdentification")
decls = [
    "h3Audit_initialHilbert_energyCorrelation_defectBudget",
    "h3Audit_initialHilbert_identify_of_kineticCeiling_and_selfPairing",
    "H3AuditInitialKineticCeilingSelfPairingTrace",
    "h3Audit_initialSubcriticalSelfPairing_identifies_physicalAndKineticRate",
]

def main():
    if not (root.is_file() and contracts.is_file()):
        raise SystemExit("Run from PrimeTensor-NS repository root")

    lines = root.read_text().splitlines()
    statement = "import " + module
    if statement not in lines:
        with root.open("a") as f:
            f.write("\n-- Physical initial energy/correlation: default build and theorem audit.\n")
            f.write(statement + "\n")
        print("Added root import")
    else:
        print("Root import already present")

    lines = contracts.read_text().splitlines()
    missing = [decl for decl in decls if "#check " + decl not in lines]
    if missing:
        with contracts.open("a") as f:
            f.write("\n-- Fixed initial self-pairing + kinetic energy trace criterion.\n")
            for decl in missing:
                f.write("#check " + decl + "\n")
                if not decl.startswith("H3Audit"):
                    f.write("#print axioms " + decl + "\n")
    print(f"Added {len(missing)} checks")

if __name__ == "__main__":
    main()
