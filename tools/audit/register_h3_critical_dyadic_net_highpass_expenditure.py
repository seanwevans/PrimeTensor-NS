#!/usr/bin/env python3
"""Register net H3 dyadic source-peak/fifth-phase highpass expenditure proofs."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicNetHighpassExpenditure"
)
NS = "PrimeTensor.FirstMonomialTriad."
THEOREMS = (
    "thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244",
    "thirdFullPhysical_signedLogPlusFifthPhase_le_kineticLowHigh244",
    "thirdFullPhysical_nearCriticalAnchor_forces_adaptiveJointHighpassCharge244",
    "thirdFullPhysical_nearCriticalAnchor_forces_viscousPhaseHighpassDefect244",
)
IMPORT = "import " + MODULE
CHECKS = tuple(
    line for name in THEOREMS
    for line in ("#check " + NS + name, "#print axioms " + NS + name)
)


def register(path: Path, entries, prepend=False):
    old = path.read_text(encoding="utf-8")
    existing = set(old.splitlines())
    absent = [entry for entry in entries if entry not in existing]
    if absent:
        added = "\n".join(absent) + "\n"
        path.write_text(
            added + old if prepend else old.rstrip("\n") + "\n" + added,
            encoding="utf-8",
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--apply", action="store_true")
    modes.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    entry = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for path in (source, entry, audit):
        if not path.is_file():
            parser.error(f"missing file {path}")
    code = source.read_text(encoding="utf-8")
    code_without_comments = re.sub(r"/-.*?-/", "", code, flags=re.S)
    code_without_comments = re.sub(r"--[^\n]*", "", code_without_comments)
    if re.search(r"\b(?:sorry|admit|axiom)\b", code_without_comments):
        parser.error("proof placeholder or additional axiom")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+" + re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing or duplicate theorem: {name}")
    if args.apply:
        register(entry, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, wanted in ((entry, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding="utf-8").splitlines()
        for item in wanted:
            if lines.count(item) != 1:
                parser.error(f"missing or duplicate: {path}: {item}")
    print(f"PASS: physical dyadic net-growth/highpass expenditure; {len(THEOREMS)} theorems")


if __name__ == "__main__":
    main()
