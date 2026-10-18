#!/usr/bin/env python3
"""Register full-third real Schwartz physical velocity and divergence proof."""
from pathlib import Path
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisRealSchwartz244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
NAMES = (
    "thirdFullAxisHilbertFourierComponent_hermitian244",
    "thirdFullAxisInverseSchwartz_im_zero244",
    "thirdFullAxisRealSchwartzComponent_apply244",
    "thirdFullAxisRealSchwartz_complexify_eq_inverse244",
    "thirdFullAxisRealSchwartz_fourier_component244",
    "thirdFullAxisRealSchwartz_fourier_vector244",
    "thirdFullAxisRealSchwartz_fourier_divergence244",
    "thirdFullAxisRealSchwartz_physical_divergence244",
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f"Missing required file: {path}")
    source = SOURCE.read_text()
    for name in NAMES:
        if f"theorem {name}" not in source:
            raise SystemExit(f"Missing declaration: {name}")
    imp = "import " + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text("\n".join(root + [imp]) + "\n")
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith("import ")] + [imp]))
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = "PrimeTensor.FirstMonomialTriad." + name
        for command in (f"#check {q}", f"#print axioms {q}"):
            if command not in body:
                body.append(command)
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if updated != original:
        AUDIT.write_text(updated)
    print("Registered real full-third axis Schwartz velocity and physical divergence")

if __name__ == "__main__":
    main()
