#!/usr/bin/env python3
"""Register the realized-Schwartz physical H3 interpolation and transport bounds."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPhysicalPathCriticalHalf244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    "lowNormalRealSchwartz_pathFirstMonomial_eq_schwartz244",
    "lowNormalRealSchwartz_pathInterpolation_eq_three_schwartz244",
    "lowNormalRealSchwartz_pathInterpolation_criticalHalf244",
    "lowNormalRealSchwartz_pathThirdTransport_criticalHalf244",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    src = SOURCE.read_text()
    for name in DECLS:
        if f"theorem {name}" not in src:
            raise SystemExit(f"Missing theorem: {name}")
    line = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if line not in root:
        ROOT.write_text("\n".join(root + [line]) + "\n")
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in audit_lines if x.startswith("import ")] + [line]))
    body = [x for x in audit_lines if not x.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for line in ("#check " + fq, "#print axioms " + fq):
            if line not in body:
                body.append(line)
    data = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != data:
        AUDIT.write_text(data)
    print("Registered realized-Schwartz H3 interpolation and transport critical-half bounds")

if __name__ == "__main__":
    main()
