#!/usr/bin/env python3
"""Register the actual highpass source spectral drop and PDE temporal-cost obstructions."""
import argparse
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualHighpassSourceSpectralDropObstruction')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_sourceDriven_dissipationDrop_highpassNorm_le_barrier',
    'h3Critical_sourceDriven_dissipationDrop_forces_spectralDisplacement',
    'h3Critical_sourceDriven_dissipationDrop_forces_temporalCost',
    'h3Critical_sourceDriven_dissipationDrop_minimalElapsedTime',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(entry for theorem in THEOREMS for entry in (
    '#check PrimeTensor.Bridge.Euclidean.' + theorem,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + theorem,
))


def install(path, entries, prepend=False):
    content = path.read_text(encoding='utf-8')
    present = set(content.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + content if prepend else
                        content.rstrip('\n') + '\n' + addition, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    act = parser.add_mutually_exclusive_group(required=True)
    act.add_argument('--apply', action='store_true')
    act.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing file: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error('expected one entry ' + repr(entry) + ' in ' + str(path))
    src = SOURCE.read_text(encoding='utf-8')
    for thm in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(thm) + r'\b', src)) != 1:
            parser.error('missing or duplicate theorem: ' + thm)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, src):
            parser.error('placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems and', len(CHECKS), 'audits')

if __name__ == '__main__':
    main()
