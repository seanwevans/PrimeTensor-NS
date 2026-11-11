#!/usr/bin/env python3
"""Register exact physical H3 highpass cubic Hilbert/fifth/phase bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalHighpassFifthPhasePhysicalBridge'
NS = "PrimeTensor.FirstMonomialTriad."
DEFS = ('thirdFullPhysicalCriticalHighFifthBand244', 'thirdFullPhysicalCriticalHighSignedPhaseBand244')
THEOREMS = ('thirdFullPhysical_highpassThirdHilbert_eq_actualCubicBand244', 'thirdFullPhysical_highpassThirdHilbertSum_eq_actualCubicBand244', 'thirdFullPhysical_highpassThirdHilbert_le_twoHighFifthPhase244', 'thirdFullPhysical_nearCriticalAnchor_forces_highFifthPhaseBand244')
IMPORT = "import " + MODULE
CHECKS = tuple(
    line for name in DEFS + THEOREMS
    for line in ("#check " + NS + name, "#print axioms " + NS + name)
)

def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding="utf-8")
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        added = "\n".join(missing) + "\n"
        path.write_text(added + old if prepend else old.rstrip("\n") + "\n" + added,
                        encoding="utf-8")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--apply", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    src = ROOT / (MODULE.replace(".", "/") + ".lean")
    pt = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for f in (src, pt, audit):
        if not f.is_file():
            parser.error(f"missing file {f}")
    source = src.read_text(encoding="utf-8")
    source = re.sub(r"/-.*?-/", "", source, flags=re.S)
    source = re.sub(r"--[^\n]*", "", source)
    if re.search(r"\b(?:sorry|admit|axiom)\b", source):
        parser.error("placeholder proof or added axiom")
    for kind, found in (("noncomputable def", DEFS), ("theorem", THEOREMS)):
        for name in found:
            pattern = r"(?m)^" + re.escape(kind) + r"\s+" + re.escape(name) + r"\b"
            if len(re.findall(pattern, source)) != 1:
                parser.error(f"missing or duplicate {kind}: {name}")
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for f, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = f.read_text(encoding="utf-8").splitlines()
        for entry in wanted:
            if lines.count(entry) != 1:
                parser.error(f"missing or duplicate {entry} in {f}")
    print(f"PASS: physical highpass cubic/fifth/phase bridge ({len(DEFS)} defs, {len(THEOREMS)} theorems)")

if __name__ == "__main__":
    main()
