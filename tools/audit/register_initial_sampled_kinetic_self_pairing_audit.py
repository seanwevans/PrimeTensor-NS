#!/usr/bin/env python3
"""Idempotently add the sampled kinetic/self-pairing module to the audit."""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
          "OneComponentInitialSampledKineticSelfPairing")
CHECKS = [
    "h3Audit_initialStrongHilbertLimit_eq_of_sampledKineticSelfPairing",
    "H3AuditInitialSampledKineticSelfPairingTrace",
    "h3Audit_initialSubcriticalSampledKineticSelfPairing_identifies_physicalAndKineticRate",
]

def main():
    if not ROOT.is_file() or not CONTRACTS.is_file():
        raise SystemExit("Run from repository root (PrimeTensor.lean required)")
    decl = "import " + MODULE
    if decl not in ROOT.read_text().splitlines():
        with ROOT.open("a") as f:
            f.write("\n-- One-sequence initial kinetic/correlation criterion in default build.\n")
            f.write(decl + "\n")
    known = set(CONTRACTS.read_text().splitlines())
    missing = [name for name in CHECKS if "#check " + name not in known]
    if missing:
        with CONTRACTS.open("a") as f:
            f.write("\n-- One-sequence physical kinetic and self-pairing trace.\n")
            for name in missing:
                f.write("#check " + name + "\n")
                if not name.startswith("H3Audit"):
                    f.write("#print axioms " + name + "\n")
    print(f"Audit registration: {len(missing)} new declaration checks")

if __name__ == "__main__":
    main()
