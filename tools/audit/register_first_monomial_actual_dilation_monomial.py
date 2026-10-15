#!/usr/bin/env python3
"""Register the actual 243-slot Point3 monomial scaling, idempotently."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3ActualDilationMonomial"
)
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
SRC = Path(MODULE.replace(".", "/") + ".lean")
NAMES = (
    "lowNormalRealSchwartzPoint3MonomialSlot_dilation",
    "lowNormalRealSchwartzPoint3Monomial_dilation",
)


def main():
    if not SRC.is_file():
        raise SystemExit(f"Missing Lean source: {SRC}")
    source = SRC.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing theorem: {name}")
    if not ROOT.is_file() or not AUDIT.is_file():
        raise SystemExit("Run in the PrimeTensor-NS repository root")
    root_lines = ROOT.read_text().splitlines()
    root_import = "import " + MODULE
    if root_import not in root_lines:
        ROOT.write_text("\n".join(root_lines + [root_import]) + "\n")
    lines = AUDIT.read_text().splitlines()
    # Lean imports must precede #check/#print commands.
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] + [root_import]
    ))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    audit_lines = imports + [""] + body
    for name in NAMES:
        qualified = "PrimeTensor.FirstMonomialTriad." + name
        for prefix in ("#check ", "#print axioms "):
            check_line = prefix + qualified
            if check_line not in audit_lines:
                audit_lines.append(check_line)
    result = "\n".join(audit_lines).rstrip() + "\n"
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print("Registered actual 243-slot physical monomial dilation contracts")


if __name__ == "__main__":
    main()
