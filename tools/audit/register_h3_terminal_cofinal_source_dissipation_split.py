#!/usr/bin/env python3
"""Idempotent registration of the H3 terminal cofinal source/dissipation split.

--apply: add the root import plus audit checks (preserving prior lines).
--check: require exactly one registration for each declaration, no writes.
"""

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
    'TerminalCofinalSourceDissipationSplit'
)
LEAN = ROOT / (MODULE.replace('.', '/') + '.lean')
IMPORT = 'import ' + MODULE
NAMES = (
    'h3Critical_projected_source_integrable_of_terminal_norm_ceiling',
    'h3Critical_noL2Trace_projected_source_cofinally_unbounded',
    'h3Critical_noL2Trace_fullEnergy_cofinally_unbounded',
    'h3Critical_noL2Trace_fullDissipation_cofinally_unbounded',
    'h3Critical_noL2Trace_laplacian_or_leray_nonintegrable_on_every_tail',
    'h3Critical_noL2Trace_laplacian_or_leray_cofinal_norm_spike',
)
CHECKS = tuple(
    item for name in NAMES for item in (
        '#check PrimeTensor.Bridge.Euclidean.' + name,
        '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
    )
)


def append_missing(path: Path, lines: tuple[str, ...], at_head: bool = False):
    before = path.read_text()
    present = set(before.splitlines())
    new = [line for line in lines if line not in present]
    if new:
        blob = '\n'.join(new) + '\n'
        path.write_text(blob + before if at_head else before.rstrip('\n') + '\n' + blob)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()

    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (LEAN, root, audit):
        if not path.is_file():
            parser.error('missing: ' + str(path.relative_to(ROOT)))
    if args.apply:
        append_missing(root, (IMPORT,))
        append_missing(audit, (IMPORT,), at_head=True)
        append_missing(audit, CHECKS)

    for path, items in ((root, (IMPORT,)), (audit, (IMPORT,) + CHECKS)):
        lines = path.read_text().splitlines()
        for line in items:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path.relative_to(ROOT)}')
    source = LEAN.read_text()
    for name in NAMES:
        if source.count('theorem ' + name + '\n') != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for forbidden in ('sorry', 'admit', 'unsafe axiom'):
        if forbidden in source:
            parser.error('placeholder in ' + str(LEAN.relative_to(ROOT)))
    print('PASS: 1 module, 6 theorems, 6 #check, 6 #print axioms')


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    main()
