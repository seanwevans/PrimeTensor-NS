#!/usr/bin/env python3
"""Register the critical dyadic physical velocity-convolution source gate."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicVelocityConvolutionGate"
)
NS = "PrimeTensor.FirstMonomialTriad."
DEFINITIONS = (
    "thirdFullPhysicalCriticalOrderFourEnvelopeAt244",
)
THEOREMS = (
    "thirdFullPhysical_thirdRadialForcing_le_orderFourEnvelope244",
    "thirdFullPhysical_thirdRadialForcingMass_le_orderFourEnvelopeSquare244",
    "thirdFullPhysical_nearCriticalAnchor_forces_orderFourVelocityConvolution244",
    "thirdFullPhysical_dyadicOrderFourConvolutionCeiling_forces_criticalAnchorExcess244",
)
IMPORT = "import " + MODULE
CHECKS = tuple(
    line for name in (*DEFINITIONS, *THEOREMS)
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
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--apply", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    src = ROOT / (MODULE.replace(".", "/") + ".lean")
    root = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for path in (src, root, audit):
        if not path.is_file():
            parser.error(f"missing file: {path}")

    code = src.read_text(encoding="utf-8")
    cleaned = re.sub(r"/-.*?-/", "", code, flags=re.S)
    cleaned = re.sub(r"--[^\n]*", "", cleaned)
    if re.search(r"\b(?:sorry|admit|axiom)\b", cleaned):
        parser.error("unexpected proof placeholder or axiom")
    for name in DEFINITIONS:
        if len(re.findall(r"(?m)^noncomputable def\s+" + re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing/duplicate definition: {name}")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+" + re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing/duplicate theorem: {name}")
    if any(line.rstrip() != line for line in code.splitlines()):
        parser.error("trailing whitespace")

    if args.apply:
        register(root, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)

    for path, entries in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding="utf-8").splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error(f"registration not unique: {path}: {entry}")
    print(f"PASS: dyadic velocity-convolution gate; {len(THEOREMS)} theorems")


if __name__ == "__main__":
    main()
