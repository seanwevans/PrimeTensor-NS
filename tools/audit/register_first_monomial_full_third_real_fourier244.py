#!/usr/bin/env python3
"""Register the full REAL static third-transport Fourier identification."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealFourierIdentification244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = (
    "thirdGradient_realSlot_eq_complexRe244",
    "fullSchwartzGradientAxis_eq_complexRe244",
    "fullSchwartzGradientTransport_eq_complexRe244",
    "fullSchwartzGradientTransport_eq_fourierRe244",
    "fullThirdSchwartzFourierCoefficient244",
    "fullSchwartzThirdCommutator_eq_fullFourierRe244",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in DECLS:
        head = "noncomputable def" if name == "fullThirdSchwartzFourierCoefficient244" else "theorem"
        if f"{head} {name}" not in source:
            raise SystemExit(f"Missing declaration: {name}")
    import_stmt = f"import {MODULE}"
    root_lines = ROOT.read_text().splitlines()
    if import_stmt not in root_lines:
        ROOT.write_text("\n".join(root_lines + [import_stmt]) + "\n")
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [v for v in audit_lines if v.startswith("import ")] + [import_stmt]
    ))
    body = [v for v in audit_lines if not v.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fullname = "PrimeTensor.FirstMonomialTriad." + name
        for statement in (f"#check {fullname}", f"#print axioms {fullname}"):
            if statement not in body:
                body.append(statement)
    new_audit = "\n".join(imports + [""] + body).rstrip() + "\n"
    if AUDIT.read_text() != new_audit:
        AUDIT.write_text(new_audit)
    print("Registered full real third-gradient and complete transport Fourier identities")


if __name__ == "__main__":
    main()
