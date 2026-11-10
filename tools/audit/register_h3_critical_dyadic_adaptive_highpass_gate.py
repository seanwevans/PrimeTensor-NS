#!/usr/bin/env python3
"""Register one-witness, all-cutoff physical H3 highpass Leray forcing gates."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicAdaptiveHighpassGate"
)
NS = "PrimeTensor.FirstMonomialTriad."
THEOREMS = (
    "thirdFullPhysical_nearCriticalAnchor_forces_allRadiusHighpassBudget244",
    "thirdFullPhysical_nearCriticalAnchor_forces_allRadiusLowOrHigh244",
    "thirdFullPhysical_nearCriticalAnchor_forces_adaptiveHighpassCharge244",
    "thirdFullPhysical_nearCriticalAnchor_forces_oneHighpassCoordinate244",
)
IMPORT = "import " + MODULE
CHECKS = tuple(line for name in THEOREMS for line in
    ("#check " + NS + name, "#print axioms " + NS + name))


def register(path: Path, items, prepend=False):
    old = path.read_text(encoding="utf-8")
    present = set(old.splitlines())
    missing = [entry for entry in items if entry not in present]
    if missing:
        addition = "\n".join(missing) + "\n"
        path.write_text(
            addition + old if prepend else old.rstrip("\n") + "\n" + addition,
            encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--apply", action="store_true")
    modes.add_argument("--check", action="store_true")
    args = parser.parse_args()

    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    root = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for path in (source, root, audit):
        if not path.is_file():
            parser.error(f"missing {path}")

    code = source.read_text(encoding="utf-8")
    scrubbed = re.sub(r"/-.*?-/", "", code, flags=re.S)
    scrubbed = re.sub(r"--[^\n]*", "", scrubbed)
    if re.search(r"\b(?:sorry|admit|axiom)\b", scrubbed):
        parser.error("unexpected proof placeholder or axiom")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+" + re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing or duplicate theorem {name}")
    if args.apply:
        register(root, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, entries in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding="utf-8").splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error(f"missing or duplicate registration: {path}: {entry}")
    print(f"PASS: one physical peak, all cutoff radii; {len(THEOREMS)} theorems")


if __name__ == "__main__":
    main()
