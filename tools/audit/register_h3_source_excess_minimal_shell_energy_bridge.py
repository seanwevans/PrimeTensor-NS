#!/usr/bin/env python3
"""Register the canonical minimal-shell H3 energy and PDE-window bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellEnergyBridge'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = ('h3CriticalMinimalShellEnergyWindow',)
THEOREMS = (
    'h3Critical_highSnapshot_minimalShellEnergyExactClock',
    'h3Critical_noL2Trace_everyTail_minimalShellEnergyExactClock',
    'h3Critical_noL2Trace_cofinal_minimalShellEnergyExactClock',
    'h3Critical_noL2Trace_disjoint_minimalShellEnergyExactClock',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in DEFS + THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in entries if entry not in present]
    if missing:
        extra = '\n'.join(missing) + '\n'
        path.write_text(extra + old if prepend else old.rstrip('\n') + '\n' + extra,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error('expected exactly one ' + repr(entry) + ' in ' + str(path))
    code = SOURCE.read_text(encoding='utf-8')
    for name in DEFS:
        if len(re.findall(r'(?m)^def\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing or duplicate def: ' + name)
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, code):
            parser.error('forbidden placeholder: ' + bad)
    print('PASS:', len(DEFS), 'definition,', len(THEOREMS), 'theorems,', len(CHECKS), 'audit entries')


if __name__ == '__main__':
    main()
