#!/usr/bin/env python3
"""Register and inspect the critical dyadic H3 physical source-peak alternative."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicPhysicalSourcePeak"
)
NS = "PrimeTensor.FirstMonomialTriad."
THEOREMS = (
    "thirdFullPhysical_dyadicCubicCeiling_forces_criticalAnchorExcess244",
    "thirdFullPhysical_criticalDyadicAnchorOrActualCubicSourcePeak244",
    "thirdFullPhysical_nearCriticalAnchor_forces_actualCubicSourcePeak244",
    "thirdFullPhysical_nearCriticalAnchor_forces_thirdRadialLerayPeak244",
)
IMPORT = "import " + MODULE
CHECKS = tuple(item for name in THEOREMS for item in (
    "#check " + NS + name,
    "#print axioms " + NS + name,
))


def add_missing(path: Path, entries, prepend=False):
    old = path.read_text(encoding="utf-8")
    present = set(old.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        addition = "\n".join(missing) + "\n"
        path.write_text(
            addition + old if prepend else old.rstrip("\n") + "\n" + addition,
            encoding="utf-8",
        )


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--apply", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    root = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for path in (source, root, audit):
        if not path.is_file():
            parser.error(f"missing file: {path}")

    code = source.read_text(encoding="utf-8")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+" + re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing/duplicate declaration: {name}")
    cleaned = re.sub(r"/-.*?-/", "", code, flags=re.S)
    cleaned = re.sub(r"--[^\n]*", "", cleaned)
    if re.search(r"\b(?:sorry|admit|axiom)\b", cleaned):
        parser.error("proof placeholder or axiom in source")
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error("source has trailing whitespace")

    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)

    for path, entries in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding="utf-8").splitlines()
        for line in entries:
            if lines.count(line) != 1:
                parser.error(f"missing/duplicate registration: {path}: {line}")

    print(f"PASS: critical dyadic physical source peak; {len(THEOREMS)} theorems")


if __name__ == "__main__":
    main()
