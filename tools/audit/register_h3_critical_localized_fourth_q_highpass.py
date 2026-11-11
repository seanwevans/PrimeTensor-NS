#!/usr/bin/env python3
"""Idempotently register localized physical fourth-Q/temporal/third-Q highpass proofs."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalLocalizedFourthQHighpass"
)
NS = "PrimeTensor.FirstMonomialTriad."
DEFS = ("thirdFullPhysicalCriticalFourthTemporalHighpass244",)
THEOREMS = (
    "thirdFullKinetic_highpass_norm_le_highpass_oneRadialMoment244",
    "thirdFullPhysical_thirdRadialHighpass_le_fourthQHighpass244",
    "thirdFullPhysical_thirdRadialHighpass_fourthQHighpass_square244",
    "thirdFullPhysical_fourthQHighpass_eq_temporalHigh_sub_thirdQHigh244",
    "thirdFullPhysical_fourthQHighpassSquare_le_temporalHighThirdQHigh244",
    "thirdFullPhysical_fourthQHighpassSum_le_temporalHighThirdQHigh244",
    "thirdFullPhysical_signedLogFifthPhase_le_localizedFourthQ244",
    "thirdFullPhysical_nearCriticalAnchor_forces_localizedTemporalSixth244",
)
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
        path.write_text(
            added + old if prepend else old.rstrip("\n") + "\n" + added,
            encoding="utf-8",
        )

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
        parser.error("placeholder proof or additional axiom")
    for kind, names in (("noncomputable def", DEFS), ("theorem", THEOREMS)):
        for name in names:
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
    print(f"PASS: localized fourth-Q physical highpass ({len(DEFS)} def, {len(THEOREMS)} theorems)")

if __name__ == "__main__":
    main()
