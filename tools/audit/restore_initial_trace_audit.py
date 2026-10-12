#!/usr/bin/env python3
"""Idempotently wire the Oct 12 H3 initial-audit chain into the library and Contracts.

Run from the repository root *after* extracting the companion Lean patch.
This intentionally edits existing files in-place rather than shipping a stale
~370 kB copy of PrimeTensor.lean over any local work.
"""
from pathlib import Path

ROOT = Path("PrimeTensor.lean")
CONTRACTS = Path("tools/audit/Contracts.lean")
MODULES = [
    "OneComponentInitialPhysicalHilbertGlobalFTC",
    "OneComponentInitialProjectedRHSKineticTrace",
    "OneComponentInitialEnergyDominatedProjectedRHS",
    "OneComponentInitialSubcriticalEnergyRate",
    "OneComponentInitialSubcriticalMomentumModulus",
    "OneComponentInitialSubcriticalKineticModulus",
    "OneComponentInitialWeakIdentifiedQuantitativeTrace",
    "OneComponentInitialAnchoredSchwartzProjectedRHS",
    "OneComponentInitialAnchoredSchwartzWeakSequence",
]
PREFIX = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit."
CHECKS = [
    "h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes",
    "h3Audit_initialOldJointProjectedRHS_exists_physicalHilbertRightLimit",
    "h3Audit_initialActualProjectedRHS_integrable_and_mass_of_h3Energy",
    "h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass",
    "h3Audit_initialSubcriticalEnergyRate_physicalMomentum_rightLimitRate",
    "h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate",
    "h3Audit_initialStrongPhysicalHilbertLimit_eq_of_weakInitialPairings",
    "h3Audit_initialSubcriticalEnergyRate_weakIdentifies_physicalMomentumRate",
    "H3AuditInitialAnchoredSchwartzPhysicalMomentum",
    "h3Audit_initialAnchoredSchwartzSource_weakPairing",
    "h3Audit_initialStrongPhysicalLimit_eq_of_anchoredSchwartzSource",
    "h3Audit_initialSubcriticalAnchoredSchwartz_physicalMomentumRate",
    "h3Audit_initialSubcriticalAnchoredSchwartz_kineticRate",
    "H3AuditInitialSchwartzWeakCofinalSequence",
    "h3Audit_initialAnchoredSchwartzSource_of_positiveDerivative_and_weakSequence",
    "h3Audit_initialSubcriticalEnergyRate_anchoredSchwartz_of_weakSequence",
    "h3Audit_initialSubcriticalWeakSequence_identifies_physicalAndKineticRate",
]


def add_root_imports():
    if not ROOT.is_file():
        raise SystemExit(f"Missing {ROOT}; run from ~/Repos/PrimeTensor-NS")
    old = ROOT.read_text()
    additions = ["import " + PREFIX + name for name in MODULES
                 if "import " + PREFIX + name not in old.splitlines()]
    if additions:
        with ROOT.open("a") as f:
            f.write("\n-- Initial physical H3 audit: restored into the default library build.\n")
            f.write("\n".join(additions) + "\n")
    print(f"{ROOT}: added {len(additions)} imports; {len(MODULES)} requested")


def add_contracts():
    if not CONTRACTS.is_file():
        raise SystemExit(f"Missing {CONTRACTS}; cannot restore the audit checks")
    old = CONTRACTS.read_text()
    to_add = [name for name in CHECKS if f"#check {name}\n" not in old]
    if to_add:
        with CONTRACTS.open("a") as f:
            f.write("\n-- Initial projected-source, momentum, and kinetic trace audit (Oct 12).\n")
            for name in to_add:
                f.write("#check " + name + "\n")
                if not name.startswith("H3Audit"):
                    f.write("#print axioms " + name + "\n")
    print(f"{CONTRACTS}: added {len(to_add)} contract checks")


if __name__ == "__main__":
    add_root_imports()
    add_contracts()
