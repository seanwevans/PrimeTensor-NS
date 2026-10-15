#!/usr/bin/env python3
"""Idempotently register exact global critical-half shape criteria."""
from pathlib import Path

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3CriticalHalfUniformShape"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "lowNormalRealSchwartz_uniformCriticalHalf_iff_positiveShapeThreshold",
    "lowNormalRealSchwartz_exists_uniformCriticalHalf_iff_shapeThreshold",
    "lowNormalRealSchwartz_criticalHalfShapeExcess_real_smul",
    "lowNormalRealSchwartz_positiveShapeExcess_rulesOut_uniformCriticalHalf",
    "lowNormalRealSchwartz_Point3Solenoidal_real_smul",
    "lowNormalRealSchwartz_solenoidalUniformCriticalHalf_iff_shapeThreshold",
)


def write_if_changed(path: Path, s: str) -> None:
    if path.read_text() != s:
        path.write_text(s)


def main() -> None:
    if not SOURCE.is_file():
        raise SystemExit(f"Missing required source: {SOURCE}")
    src = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in src:
            raise SystemExit(f"Missing theorem contract: {name}")
    imp = "import " + MODULE
    for path in (ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        root_lines.append(imp)
    write_if_changed(ROOT, "\n".join(root_lines).rstrip() + "\n")

    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [s for s in lines if s.startswith("import ")] + [imp]
    ))
    body = [s for s in lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qname = "PrimeTensor.FirstMonomialTriad." + name
        for cmd in ("#check", "#print axioms"):
            statement = f"{cmd} {qname}"
            if statement not in body:
                body.append(statement)
    write_if_changed(AUDIT, "\n".join(imports + [""] + body).rstrip() + "\n")
    print("Registered positive-shape critical-half threshold contracts")


if __name__ == "__main__":
    main()
