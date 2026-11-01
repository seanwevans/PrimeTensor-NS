#!/usr/bin/env python3
"""Register cofinal constructive quartic persistence and physical H3 costs."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourcePeakCofinalConstructiveQuarticCosts')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions',
    'h3Critical_noL2Trace_cofinalAutomaticQuarticWidths_and_fullDissipationCosts',
    'h3Critical_quarticCofinalCost_finiteBudget_forces_weightedWidthCap',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    before = path.read_text(encoding='utf-8')
    present = set(before.splitlines())
    missing = [entry for entry in entries if entry not in present]
    if missing:
        blob = '\n'.join(missing) + '\n'
        path.write_text(blob + before if prepend else before.rstrip('\n') + '\n' + blob,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    choices = parser.add_mutually_exclusive_group(required=True)
    choices.add_argument('--apply', action='store_true')
    choices.add_argument('--check', action='store_true')
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
    contents = SOURCE.read_text(encoding='utf-8')
    for theorem in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(theorem) + r'\b', contents)) != 1:
            parser.error('missing/duplicate theorem: ' + theorem)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, contents):
            parser.error('forbidden proof placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'axiom audits')


if __name__ == '__main__':
    main()
