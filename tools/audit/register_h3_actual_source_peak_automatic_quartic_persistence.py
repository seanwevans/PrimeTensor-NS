#!/usr/bin/env python3
"""Register automatic local high-H3 dissipation persistence from a source peak."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourcePeakAutomaticQuarticPersistence')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_positiveSourceMargin_selectsDominantQuarticRadius',
    'h3Critical_quarticSourceDrop_initialTailDissipationBudget',
    'h3Critical_strictSourcePeak_automaticLocalHighDissipationPersistence',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(stmt for theorem in THEOREMS for stmt in (
    '#check PrimeTensor.Bridge.Euclidean.' + theorem,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + theorem,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else old.rstrip('\n') + '\n' + addition,
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
    for path, required in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        content = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if content.count(entry) != 1:
                parser.error('expected one occurrence of ' + repr(entry) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for theorem in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(theorem) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem: ' + theorem)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, source):
            parser.error('forbidden placeholder ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'axiom audits')


if __name__ == '__main__':
    main()
