#!/usr/bin/env python3
"""Register and inspect the critical physical H3 cubic-source clock gate."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalCubicPhysicalClockBarrier"
)
NS = "PrimeTensor.FirstMonomialTriad."
THEOREMS = (
    "thirdFullPhysical_criticalCubicRate_forces_actualSourceClock244",
    "thirdFullPhysical_actualSourceClock_deficit_excludesCriticalCubicRate244",
    "thirdFullPhysical_criticalCubicRate_forces_dyadicSourceCharge244",
)
IMPORT = "import " + MODULE
CHECKS = [line for name in THEOREMS for line in
          ("#check " + NS + name, "#print axioms " + NS + name)]


def register(path, entries, prepend=False):
    old = path.read_text(encoding="utf-8")
    have = set(old.splitlines())
    missing = [x for x in entries if x not in have]
    if missing:
        addition = "\n".join(missing) + "\n"
        path.write_text(addition + old if prepend else old.rstrip("\n") + "\n" + addition,
                        encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    modes = ap.add_mutually_exclusive_group(required=True)
    modes.add_argument("--apply", action="store_true")
    modes.add_argument("--check", action="store_true")
    args = ap.parse_args()
    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    root = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for p in (source, root, audit):
        if not p.exists():
            ap.error(f"missing {p}")
    code = source.read_text(encoding="utf-8")
    cleaned = re.sub(r"/-.*?-\/", "", code, flags=re.S)
    cleaned = re.sub(r"--[^\n]*", "", cleaned)
    if re.search(r"\b(?:sorry|admit|axiom)\b", cleaned):
        ap.error("proof placeholder or axiom")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+" + re.escape(name) + r"\b", code)) != 1:
            ap.error(f"missing/duplicate {name}")
    if args.apply:
        register(root, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for p, entries in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = p.read_text(encoding="utf-8").splitlines()
        for e in entries:
            if lines.count(e) != 1:
                ap.error(f"missing or duplicate registration: {p}: {e}")
    print(f"PASS: critical physical cubic-source clock; {len(THEOREMS)} theorems")


if __name__ == "__main__":
    main()
