#!/usr/bin/env python3
"""Register integrated actual Leray/H³² charges for selected outer highpass windows."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierIntegratedLerayH3Charge'
NAMESPACE = "PrimeTensor.FirstMonomialTriad."
THEOREMS = ('thirdFullPhysical_actualLeray_norm_le_H3Square244', 'thirdFullPhysical_actualLeray_and_H3Square_intervalIntegrable244', 'thirdFullPhysical_outerIntegratedLeray_norm_le_H3Cost244', 'thirdFullKinetic_initialAlignment_forcesLerayActionCost244', 'thirdFullKinetic_positiveH3Action_of_alignment244', 'thirdFullPhysical_outerForcedLeray_integratedH3Charge244', 'thirdFullPhysical_outerForcedLeray_positiveIntegratedH3Charge244', 'thirdFullPhysical_outerFrozenHighpass_kineticAnchor_norm_le244', 'thirdFullPhysical_outerForcedLeray_kineticAnchoredH3Charge244')
IMPORT = "import " + MODULE
CHECKS = tuple(item for name in THEOREMS for item in
    ("#check " + NAMESPACE + name, "#print axioms " + NAMESPACE + name))


def register(path: Path, lines, prepend=False):
    old = path.read_text(encoding="utf-8")
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        added = "\n".join(missing) + "\n"
        path.write_text(added + old if prepend else old.rstrip("\n") + "\n" + added,
                        encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--apply", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    rootlean = ROOT / "PrimeTensor.lean"
    auditlean = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for path in (source, rootlean, auditlean):
        if not path.is_file():
            parser.error(f"missing {path}")
    clean = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "",
        source.read_text(encoding="utf-8"), flags=re.S))
    if re.search(r"\b(?:sorry|admit|axiom)\b", clean):
        parser.error("Lean source contains a proof placeholder or introduced axiom")
    for name in THEOREMS:
        count = len(re.findall(r"(?m)^theorem\s+" + re.escape(name) + r"\b", clean))
        if count != 1:
            parser.error(f"missing or repeated theorem {name}: {count}")
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, required in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding="utf-8").splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f"expected exactly one {line} in {path}")
    print(f"PASS: integrated outer nonlinear Leray H³² charge: {len(THEOREMS)} theorems")

if __name__ == "__main__":
    main()
