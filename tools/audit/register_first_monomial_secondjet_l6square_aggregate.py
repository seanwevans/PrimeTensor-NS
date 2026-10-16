#!/usr/bin/env python3
"""Idempotent registration of the complete 27-jet L6-square Sobolev sum."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetL6SquareAggregate"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    ("def", "lowNormalSecondJetSobolevConstant"),
    ("def", "lowNormalRealSchwartz_secondJetL6Square"),
    ("def", "lowNormalRealSchwartz_secondJetFrechetL2Square"),
    ("theorem", "lowNormalRealSchwartz_secondJetL6Square_le_sobolev"),
    ("def", "lowNormalRealSchwartz_secondJetsL6SquareTotal"),
    ("def", "lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal"),
    ("theorem", "lowNormalRealSchwartz_secondJetsL6SquareTotal_le_sobolev"),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    code = SOURCE.read_text()
    for kind, name in DECLS:
        if f"{kind} {name}" not in code:
            raise SystemExit(f"Missing {kind}: {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    body = [s for s in lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for kind, name in DECLS:
        full = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + full, "#print axioms " + full):
            if cmd not in body:
                body.append(cmd)
    merged = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != merged:
        AUDIT.write_text(merged)
    print("Registered 27-slot squared homogeneous Sobolev aggregate")

if __name__ == "__main__":
    main()
