#!/usr/bin/env python3
"""Register the actual real-Schwartz mixed-derivative pair contraction."""
from pathlib import Path
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3SchwartzMixedPairContraction")
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalSchwartz_lineDeriv_comm",
    "lowNormalSchwartz_secondLineDeriv_pair_eq_mixed_square",
    "lowNormalRealSchwartz_axis_secondPair_eq_mixedSquare",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing theorem contract: {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    body = [s for s in lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + qualified, "#print axioms " + qualified):
            if cmd not in body:
                body.append(cmd)
    new = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != new:
        AUDIT.write_text(new)
    print("Registered exact physical Schwartz mixed pair contraction")

if __name__ == "__main__":
    main()
