#!/usr/bin/env python3
"""Idempotently register actual radius-dependent physical Sobolev bounds."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3QuantitativeCutoffSobolev"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "exists_uniform_radius_cutoff_fderiv_majorant",
    "exists_uniform_radius_cutoff_quantitative_L6",
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing required file: {p}")
    code = SOURCE.read_text()
    for n in NAMES:
        if ("theorem " + n) not in code:
            raise SystemExit(f"Missing theorem: {n}")
    imp = "import " + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text("\n".join(lines + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    body = [s for s in lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        symbol = "PrimeTensor.Bridge.Euclidean." + n
        for cmd in ("#check " + symbol, "#print axioms " + symbol):
            if cmd not in body:
                body.append(cmd)
    new = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != new:
        AUDIT.write_text(new)
    print("Registered radius-dependent quantitative cutoff Sobolev bounds")


if __name__ == "__main__":
    main()
