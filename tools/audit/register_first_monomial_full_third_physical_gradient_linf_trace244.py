#!/usr/bin/env python3
"""Register the L2-L2-Linfty physical third-gradient strong-trace lemmas."""
from pathlib import Path
import re

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientLinfTrace244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
THEOREMS = (
    "h3PhysicalGradientLpTriple_eq_integral244",
    "h3PhysicalGradientLpTriple_tendsto244",
    "h3GradientLinf_norm_le_bound244",
    "h3GradientUniformLinf_tendsto244",
    "h3MatchedSchwartz_physicalThirdL2_tendsto244",
    "h3MatchedSchwartz_physicalFirstLinf_tendsto244",
    "h3MatchedSchwartz_physicalGradientLpTriple_tendsto244",
)
DEFS = (
    "h3PhysicalGradientLpTriple244",
    "h3ActualPhysicalFirstJetLinf244",
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing: {path}")
    source = SOURCE.read_text()
    if re.search(r"\b(sorry|admit)\b", source):
        raise SystemExit("Proof placeholder detected")
    for kw, names in (("theorem", THEOREMS), ("noncomputable def", DEFS)):
        for name in names:
            if not re.search(r"^" + kw + r"\s+" + re.escape(name) + r"\b", source, re.M):
                raise SystemExit(f"Missing {kw}: {name}")
    stmt = "import " + MODULE
    root_before = ROOT.read_text()
    if stmt not in root_before.splitlines():
        ROOT.write_text(root_before.rstrip() + "\n" + stmt + "\n")
    before = AUDIT.read_text()
    lines = before.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith("import ")] + [stmt]))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS + DEFS:
        fq = "PrimeTensor.FirstMonomialTriad." + name
        for line in ("#check " + fq, "#print axioms " + fq):
            if line not in body:
                body.append(line)
    revised = "\n".join(imports + [""] + body).rstrip() + "\n"
    if revised != before:
        AUDIT.write_text(revised)
    print("Registered physical H3 gradient strong L2-L2-Linfty trace")


if __name__ == "__main__":
    main()
