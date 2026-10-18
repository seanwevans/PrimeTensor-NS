#!/usr/bin/env python3
"""Idempotently register the full-third axis support proof on a checked checkout."""
from pathlib import Path

MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3FullThirdAxisWindowSupport244")
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = [
    "thirdFullAxisToFin244",
    "thirdFullAxisSixCenter244",
    "thirdFullAxisSixCenter_toFin244",
    "thirdFullAxis_coordinateBall_transfer244",
    "thirdFullAxisSixCenter_coordinateBall_zero_sum_coherent244",
    "thirdFullAxisWindowBump244",
    "thirdFullAxisWindowBump_contDiff244",
    "thirdFullAxisWindowBump_hasCompactSupport244",
    "thirdFullAxisWindowBump_at_center244",
    "thirdFullAxisWindowBump_nonzero_ball244",
    "thirdFullAxisWindowBump_coordinateBall244",
    "thirdFullAxisWindowBump_zero_sum_coherent244",
    "thirdFullAxisWindowBump_pair_coherent244",
    "thirdFullAxisWindowBump_noncoherent_product_zero244",
]

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        if not any(f"{kw} {name}" in source
                   for kw in ("theorem", "noncomputable def", "def")):
            raise SystemExit(f"Missing expected declaration: {name}")
    imp = "import " + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text("\n".join(root_lines + [imp]) + "\n")
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in old if x.startswith("import ")] + [imp]))
    body = [x for x in old if not x.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        for command in (f"#check PrimeTensor.FirstMonomialTriad.{name}",
                        f"#print axioms PrimeTensor.FirstMonomialTriad.{name}"):
            if command not in body:
                body.append(command)
    result = "\n".join(imports + [""] + body).rstrip() + "\n"
    if result != AUDIT.read_text():
        AUDIT.write_text(result)
    print("Registered full-third axis compact windows and coherent-support theorem")

if __name__ == "__main__":
    main()
