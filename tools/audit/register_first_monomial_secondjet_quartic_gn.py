#!/usr/bin/env python3
"""Register the real, unconditional 27-slot second-jet Gagliardo–Nirenberg bound."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetQuarticGN"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    ("def", "lowNormalRealSchwartzSecondJetsQuarticMass"),
    ("def", "lowNormalRealSchwartzSecondJetsSixthMass"),
    ("theorem", "lowNormalRealSchwartz_secondJets_quarticMass_sq_le_E2_mul_sixthMass"),
    ("theorem", "lowNormalRealSchwartz_secondJets_sixthMass_ofReal_le_E3"),
    ("theorem", "lowNormalRealSchwartz_secondJets_quarticGN_ennreal"),
    ("def", "lowNormalSecondJetSobolevRealConstant"),
    ("theorem", "lowNormalSecondJetSobolevRealConstant_nonneg"),
    ("theorem", "lowNormalSecondJetSobolevConstant_eq_ofReal"),
    ("theorem", "lowNormalRealSchwartz_secondJets_quarticGN_real"),
    ("theorem", "lowNormalRealSchwartz_secondJets_quarticGN_real_normalized"),
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing: {path}")
    source = SOURCE.read_text()
    for kind, name in DECLS:
        if f"{kind} {name}" not in source:
            raise SystemExit(f"Missing {kind}: {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")] + [imp]))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for kind, name in DECLS:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + fq, "#print axioms " + fq):
            if cmd not in body:
                body.append(cmd)
    text = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != text:
        AUDIT.write_text(text)
    print("Registered genuine 27-slot Schwartz quartic GN bound")


if __name__ == "__main__":
    main()
