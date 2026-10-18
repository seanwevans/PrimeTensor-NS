#!/usr/bin/env python3
"""Idempotently register the full-third axis packet inverse Fourier bridge."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisInverseFourier244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "thirdFullAxisSixFourierComponent_apply244",
    "thirdFullAxisHilbertFourierComponent_apply244",
    "thirdFullAxisInverseSchwartz_fourier_component244",
    "thirdFullAxisInverseSchwartz_fourier_vector244",
    "thirdFullAxisInverseSchwartz_fourier_divergence244",
    "thirdFullAxisInverseSchwartz_fourier_hermitian244",
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing required file: {p}")
    source = SOURCE.read_text()
    for n in NAMES:
        if f"theorem {n}" not in source:
            raise SystemExit(f"Missing declaration: {n}")
    imp = "import " + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text("\n".join(roots + [imp]) + "\n")
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    body = [s for s in lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        q = "PrimeTensor.FirstMonomialTriad." + n
        for command in (f"#check {q}", f"#print axioms {q}"):
            if command not in body:
                body.append(command)
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if updated != original:
        AUDIT.write_text(updated)
    print("Registered full-third axis inverse-Fourier Schwartz bridge")

if __name__ == "__main__":
    main()
