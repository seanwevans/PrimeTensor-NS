#!/usr/bin/env python3
"""Register and audit the genuine H3 kinetic-low / Leray-highpass source gate."""
import argparse
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport."
    "FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicKineticHighpassForcing"
)
NS = "PrimeTensor.FirstMonomialTriad."
DEFINITIONS = (
    "thirdFullPhysicalCriticalThirdForcingKineticLowBudget244",
    "thirdFullPhysicalCriticalThirdForcingHighpass244",
)
THEOREMS = (
    "thirdFullPhysical_criticalThirdForcingHighpass_norm_sq_eq_integral244",
    "thirdFullPhysical_criticalThirdForcingLowSquare_le_kinetic244",
    "thirdFullKinetic_scalar_threeFourierLowHighSquare244",
    "thirdFullPhysical_criticalThirdForcingMass_kineticLowHigh244",
    "thirdFullPhysical_nearCriticalAnchor_forces_kineticLowOrForcingHigh244",
)
IMPORT = "import " + MODULE
CHECKS = tuple(line for name in (*DEFINITIONS, *THEOREMS)
               for line in ("#check " + NS + name,
                            "#print axioms " + NS + name))


def register(path: Path, entries, prepend=False):
    existing = path.read_text(encoding="utf-8")
    have = set(existing.splitlines())
    missing = [item for item in entries if item not in have]
    if missing:
        added = "\n".join(missing) + "\n"
        path.write_text(added + existing if prepend else
                        existing.rstrip("\n") + "\n" + added,
                        encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--apply", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    root = ROOT / "PrimeTensor.lean"
    audit = ROOT / "tools/audit/FirstMonomialTriad.lean"
    for p in (source, root, audit):
        if not p.is_file():
            parser.error(f"missing file {p}")

    code = source.read_text(encoding="utf-8")
    for name in DEFINITIONS:
        if len(re.findall(r"(?m)^noncomputable def\s+" +
                          re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing or duplicated definition {name}")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+" +
                          re.escape(name) + r"\b", code)) != 1:
            parser.error(f"missing or duplicated theorem {name}")
    cleaned = re.sub(r"/-.*?-/", "", code, flags=re.S)
    cleaned = re.sub(r"--[^\n]*", "", cleaned)
    if re.search(r"\b(?:sorry|admit|axiom)\b", cleaned):
        parser.error("source contains a proof placeholder or axiom")
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error("source contains trailing whitespace")

    if args.apply:
        register(root, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, entries in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding="utf-8").splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error(f"missing or duplicated registration {entry} in {path}")
    print(f"PASS: kinetic low/high forcing; {len(DEFINITIONS)} defs and {len(THEOREMS)} theorems")


if __name__ == "__main__":
    main()
