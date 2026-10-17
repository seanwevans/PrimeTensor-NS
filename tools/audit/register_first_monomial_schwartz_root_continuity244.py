#!/usr/bin/env python3
"""Register full Schwartz L4-root norm continuity and three-jet closure."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3SchwartzRootContinuity244"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    ("theorem", "schwartzIntegralL4Root_le_add_difference244"),
    ("theorem", "schwartzIntegralL4Root_sub_comm244"),
    ("theorem", "schwartzIntegralL4Root_abs_sub_le_difference244"),
    ("theorem", "schwartzIntegralL4Root_tendsto_of_difference244"),
    ("def", "SchwartzThreeDifferenceJetConvergence244"),
    ("theorem", "SchwartzThreeDifferenceJetConvergence244.toStrongJets"),
    ("theorem", "lowNormalRealSchwartz_firstMonomial_tendsto_of_threeDifferenceJets244"),
    ("theorem", "h3PathCanonical_approximable_of_threeDifferenceJets244"),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    src = SOURCE.read_text()
    for kind, name in DECLS:
        if f"{kind} {name}" not in src:
            raise SystemExit(f"Missing declaration: {name}")
    imp = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text("\n".join(root_lines + [imp]) + "\n")
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith("import ")] + [imp]))
    body = [l for l in lines if not l.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check " + fq, "#print axioms " + fq):
            if cmd not in body:
                body.append(cmd)
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print("Registered physical Schwartz L4-root triangle and three-jet continuity")

if __name__ == "__main__":
    main()
