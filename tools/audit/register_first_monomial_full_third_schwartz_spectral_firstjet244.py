#!/usr/bin/env python3
"""Idempotently register the H³ spectral first-jet bridge to Schwartz transport."""
from pathlib import Path
import re

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzSpectralFirstJet244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = ('spectralFirstJet_difference_abs_le_weightedH3_244', 'spectralFirstJet_target_abs_le_weightedH3_244', 'spectralFirstJet_uniformAndVanishingGauges244', 'spectralFirstJet_produces_naturalGradientJets244', 'fullSchwartzGradientTransport_tendsto_of_spectralH3FirstJet244', 'h3Path_spectralH3FirstJet_implies_fullThirdObservable244')


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing {p}")
    content = SOURCE.read_text()
    if re.search(r"\b(sorry|admit)\b", content):
        raise SystemExit("Proof placeholder detected")
    declared = set(re.findall(r"^theorem\s+(\w+)", content, re.M))
    if not set(NAMES) <= declared:
        raise SystemExit("Missing theorem declarations")
    imp = "import " + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text("\n".join(lines + [imp]) + "\n")
    orig = AUDIT.read_text()
    xs = orig.splitlines()
    imports = list(dict.fromkeys([x for x in xs if x.startswith("import ")] + [imp]))
    rest = [x for x in xs if not x.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in NAMES:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for command in (f"#check {fq}", f"#print axioms {fq}"):
            if command not in rest:
                rest.append(command)
    updated = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if updated != orig:
        AUDIT.write_text(updated)
    print(f"Registered {len(NAMES)} spectral first-jet bridge theorems")


if __name__ == "__main__":
    main()
