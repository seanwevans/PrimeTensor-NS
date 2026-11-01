#!/usr/bin/env python3
"""Register actual physical PDE quartic H3 spectral temporal clock."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourceDropQuarticPhysicalClock')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_quarticClock_radialWeight_le_fourSixth',
    'h3Critical_quarticClock_scaledFiniteBandCost_le_twelve',
    'h3Critical_quarticClock_actualSpectralDisplacement_le_physical',
    'h3Critical_quarticClock_highpassSourceTemporalDisplacement_le_physical',
    'h3Critical_sourceDrop_quarticClock_endpointDissipationBudget',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [x for x in entries if x not in present]
    if missing:
        blob = '\n'.join(missing) + '\n'
        path.write_text(blob + old if prepend else old.rstrip('\n') + '\n' + blob,
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
        for x in entries:
            if lines.count(x) != 1:
                parser.error('expected exactly one ' + repr(x) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, source):
            parser.error('forbidden proof placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'axiom audits')


if __name__ == '__main__':
    main()
