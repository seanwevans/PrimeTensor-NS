#!/usr/bin/env python3
"""Register actual full-third real Schwartz spectral support theorem in CI and audit."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSpectrumSupport244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "thirdFullAxisSixCenter_reflect_zero244",
    "thirdFullAxisSixCenter_reflect_one244",
    "thirdFullAxisSixCenter_reflect_two244",
    "thirdFullAxisSixFourierPacket_zero_of_windows244",
    "thirdFullAxisSixFourierPacket_nonzero_center244",
    "thirdFullAxisSixFourierPacket_coherent_pair244",
    "thirdFullAxisRealSchwartzSpectrum_eq_packet244",
    "thirdFullAxisRealSchwartzSpectrum_coherent_pair244",
    "thirdFullAxisRealSchwartzTripleMass_zero_off_coherent244",
    "thirdFullAxisRealSchwartz_commutator_eq_fourier244",
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing required file: {p}")
    data = SOURCE.read_text()
    for n in NAMES:
        if f"theorem {n}" not in data:
            raise SystemExit(f"Missing theorem declaration: {n}")
    imp = "import " + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text("\n".join(roots + [imp]) + "\n")
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith("import ")] + [imp]))
    body = [x for x in lines if not x.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + n
        for command in (f"#check {qualified}", f"#print axioms {qualified}"):
            if command not in body:
                body.append(command)
    result = "\n".join(imports + [""] + body).rstrip() + "\n"
    if result != original:
        AUDIT.write_text(result)
    print("Registered real full-third Schwartz spectral support and commutator bridge")

if __name__ == "__main__":
    main()
