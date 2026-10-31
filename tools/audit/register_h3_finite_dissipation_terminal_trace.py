#!/usr/bin/env python3
"""Idempotently register the finite-H3-dissipation terminal-trace proof chain.

--apply: append root imports and audit proof checks without altering prior lines.
--check: verify both files and all registered declarations.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[2]
MODS = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationPointwise",
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace",
)
THEOREMS = (
    "h3Critical_energy3_le_energy0_add_dissipation3",
    "h3Critical_energy_le_kinetic_add_dissipation",
    "h3Critical_energy_le_kinetic_anchor_add_dissipation",
    "h3Critical_projected_source_le_kinetic_anchor_add_dissipation",
    "h3Critical_projected_source_integrable_of_finite_dissipation",
    "h3Critical_integrable_primitive_terminal_limit",
    "h3Critical_physicalL2_terminal_trace_of_finite_dissipation",
    "h3Critical_noL2Trace_incompatible_with_finite_dissipation",
)
PROOF_FILES = [ROOT / (m.replace(".", "/") + ".lean") for m in MODS]
ROOT_IMPORTS = ["import " + m for m in MODS]
AUDIT_CHECKS = [
    line for name in THEOREMS
    for line in (
        "#check PrimeTensor.Bridge.Euclidean." + name,
        "#print axioms PrimeTensor.Bridge.Euclidean." + name,
    )
]


def append_missing(path: Path, lines: list[str], *, at_head: bool = False) -> bool:
    old = path.read_text()
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if not missing:
        return False
    addition = "\n".join(missing) + "\n"
    path.write_text(addition + old if at_head else old.rstrip("\n") + "\n" + addition)
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    m = ap.add_mutually_exclusive_group(required=True)
    m.add_argument("--apply", action="store_true")
    m.add_argument("--check", action="store_true")
    args = ap.parse_args()

    root_module = ROOT / "PrimeTensor.lean"
    audit_file = ROOT / "tools/audit/FirstMonomialTriad.lean"
    needed = [root_module, audit_file, *PROOF_FILES]
    for p in needed:
        if not p.is_file():
            raise SystemExit(f"Missing: {p.relative_to(ROOT)}")
    if args.apply:
        append_missing(root_module, ROOT_IMPORTS)
        append_missing(audit_file, ROOT_IMPORTS, at_head=True)
        append_missing(audit_file, AUDIT_CHECKS)

    for p, lines in ((root_module, ROOT_IMPORTS), (audit_file, ROOT_IMPORTS), (audit_file, AUDIT_CHECKS)):
        text = p.read_text().splitlines()
        for line in lines:
            if text.count(line) != 1:
                raise SystemExit(f"Missing or duplicate registration in {p.relative_to(ROOT)}: {line}")

    for p, names in ((PROOF_FILES[0], THEOREMS[:4]), (PROOF_FILES[1], THEOREMS[4:])):
        content = p.read_text()
        for name in names:
            if content.count("theorem " + name + "\n") != 1:
                raise SystemExit(f"Missing or duplicate theorem in {p.relative_to(ROOT)}: {name}")
        for banned in ("sorry", "admit", "unsafe axiom"):
            if banned in content:
                raise SystemExit(f"Potential placeholder in {p.relative_to(ROOT)}: {banned}")
    print("PASS: 2 proof imports, 8 #check, 8 #print axioms, 8 theorem declarations")
    return 0


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    raise SystemExit(main())
