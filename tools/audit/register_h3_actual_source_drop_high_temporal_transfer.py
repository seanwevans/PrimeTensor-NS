#!/usr/bin/env python3
"""Register physical PDE source-drop/high-radial spectral motion bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualHighpassSourceDropHighRadialTemporalTransfer')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_sourceDrop_forces_temporalSpectralLowHighBudget',
    'h3Critical_sourceDrop_forces_highRadialSpectralMotion_or_PDEClock',
    'h3Critical_sourceDrop_PDEClock_and_highRadialCeiling_preclude_drop',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for theorem in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + theorem,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + theorem,
))


def install(path, lines, prepend=False):
    content = path.read_text(encoding='utf-8')
    present = set(content.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + content if prepend else
                        content.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, required in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if lines.count(entry) != 1:
                parser.error('expected one occurrence of ' + repr(entry) + ' in ' + str(path))
    content = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, content):
            parser.error('proof placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'audit checks')


if __name__ == '__main__':
    main()
