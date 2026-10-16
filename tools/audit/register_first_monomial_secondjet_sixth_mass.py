#!/usr/bin/env python3
"""Register the actual 27-slot sixth-power Schwartz-mass inequality."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetSixthMassBound"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    "lowNormalSchwartz_eLpNorm_six_pow_eq_ofReal_integral",
    "lowNormalRealSchwartz_secondJets_sixthMass_le_L6SquareTotal_cube",
    "lowNormalRealSchwartz_secondJets_sixthMass_le_sobolev_E3_cube",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    body = SOURCE.read_text()
    for name in DECLS:
        if f"theorem {name}" not in body:
            raise SystemExit(f"Missing theorem: {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith("import ")] + [imp]))
    audit_body = [s for s in lines if not s.startswith("import ")]
    while audit_body and not audit_body[0].strip():
        audit_body.pop(0)
    for name in DECLS:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + fq, "#print axioms " + fq):
            if cmd not in audit_body:
                audit_body.append(cmd)
    merged = "\n".join(imports + [""] + audit_body).rstrip() + "\n"
    if AUDIT.read_text() != merged:
        AUDIT.write_text(merged)
    print("Registered the 27-slot Schwartz sixth-power mass bound")

if __name__ == "__main__":
    main()
