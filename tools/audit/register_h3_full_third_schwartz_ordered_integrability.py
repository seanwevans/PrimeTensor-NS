#!/usr/bin/env python3
"""Idempotently register the full-third ordered Schwartz integrability bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSchwartzOrderedIntegrability')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = ('thirdFullSchwartzOrderedSevenKernel244',)
THEOREMS = (
    'thirdFullSchwartzOrderedSevenKernel_integrable244',
    'thirdFullSchwartzComplexOrdered_eq_sevenKernel244',
    'thirdFullSchwartzComplexOrderedKernel_integrable244',
    'thirdFullSchwartzComplexSixthPowerFlux_integrable244',
    'thirdFullSchwartzComplexSixthPowerFlux_integral244',
    'thirdFullRealSchwartz_sixthPowerFlux_integral244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in DEFS + THEOREMS for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in entries if entry not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
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
                parser.error('expected exactly one ' + repr(entry) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for name in DEFS:
        if len(re.findall(r'(?m)^noncomputable\s+def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or duplicate definition: ' + name)
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(forbidden, source):
            parser.error('forbidden proof placeholder: ' + forbidden)
    print('PASS:', len(THEOREMS), 'theorems,', len(DEFS), 'definition,',
          len(CHECKS), 'axiom audit entries')


if __name__ == '__main__':
    main()
