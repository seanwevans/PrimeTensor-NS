#!/usr/bin/env python3
"""Idempotently register exact 243-slot Holder factor energy multiplicities."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderSlotMassMultiplicities"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    ("def", "lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass"),
    ("def", "lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass"),
    ("def", "lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass"),
    ("theorem", "lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass_eq_card_mul_E3"),
    ("theorem", "lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass_eq_card_sq_mul_Q4"),
    ("theorem", "lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass_eq_card_sq_mul_Q4"),
    ("theorem", "lowNormalRealSchwartz_firstMonomialSlotMomentProduct_eq_E3_Q4"),
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing required file: {p}")
    body = SOURCE.read_text()
    for kind, name in DECLS:
        if f"{kind} {name}" not in body:
            raise SystemExit(f"Missing {kind} {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    rest = [s for s in lines if not s.startswith("import ")]
    while rest and not rest[0].strip():
        rest.pop(0)
    for _, name in DECLS:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + fq, "#print axioms " + fq):
            if cmd not in rest:
                rest.append(cmd)
    result = "\n".join(imports + [""] + rest).rstrip() + "\n"
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print("Registered exact 243-slot Holder factor multiplicities")

if __name__ == "__main__":
    main()
