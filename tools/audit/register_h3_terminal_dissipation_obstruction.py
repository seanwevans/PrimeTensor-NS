#!/usr/bin/env python3
"""Idempotent registration for the terminal source/dissipation obstruction.

--apply appends the root/audit imports and declaration checks.
--check verifies source files and registration without modifying anything.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[2]
MOD = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalDissipationObstruction'
PATH = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_IMPORT = 'import ' + MOD
NAMES = (
    'h3Critical_physicalL2_trace_of_integrable_projected_source_on_tail',
    'h3Critical_noL2Trace_forces_projected_source_nonintegrable_on_every_tail',
    'h3Critical_projected_source_integrable_of_tail_dissipation',
    'h3Critical_noL2Trace_forces_full_dissipation_nonintegrable_on_every_tail',
)
AUDIT = tuple(line for name in NAMES for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path: Path, required: tuple[str, ...], at_head=False):
    original = path.read_text()
    present = set(original.splitlines())
    new_lines = [s for s in required if s not in present]
    if not new_lines:
        return
    block = '\n'.join(new_lines) + '\n'
    path.write_text(block + original if at_head else original.rstrip('\n') + '\n' + block)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = p.parse_args()
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (root, audit, PATH):
        if not path.is_file():
            p.error(f'missing: {path.relative_to(ROOT)}')
    if args.apply:
        append_missing(root, (ROOT_IMPORT,))
        append_missing(audit, (ROOT_IMPORT,), at_head=True)
        append_missing(audit, AUDIT)
    for path, required in ((root, (ROOT_IMPORT,)),
                           (audit, (ROOT_IMPORT,) + AUDIT)):
        lines = path.read_text().splitlines()
        for line in required:
            if lines.count(line) != 1:
                p.error(f'expected exactly one {line!r} in {path.relative_to(ROOT)}')
    content = PATH.read_text()
    for name in NAMES:
        if content.count('theorem ' + name + '\n') != 1:
            p.error(f'missing or duplicate theorem {name}')
    for forbidden in ('sorry', 'admit', 'unsafe axiom'):
        if forbidden in content:
            p.error(f'placeholder in {PATH.relative_to(ROOT)}: {forbidden}')
    print('PASS: terminal obstruction import, 4 theorems, 4 #check, 4 #print axioms')


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    main()
