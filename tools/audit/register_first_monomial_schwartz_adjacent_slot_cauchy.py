#!/usr/bin/env python3
"""Register the actual signed Schwartz slotwise Cauchy bounds idempotently."""
from pathlib import Path
MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentSlotCauchy")
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalSchwartz_integral_mul_sq_le",
    "lowNormalRealSchwartzH3Energy1_slot_cauchy",
    "lowNormalRealSchwartzH3Energy2_slot_cauchy",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    src = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in src:
            raise SystemExit(f"Missing theorem contract: {name}")
    imp = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text("\n".join(root_lines + [imp]) + "\n")
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in audit_lines if x.startswith("import ")] + [imp]))
    body = [x for x in audit_lines if not x.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for command in ("#check " + qualified, "#print axioms " + qualified):
            if command not in body:
                body.append(command)
    result = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print("Registered signed Schwartz Cauchy and adjacent H3 derivative slots")

if __name__ == "__main__":
    main()
