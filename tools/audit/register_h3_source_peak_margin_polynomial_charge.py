#!/usr/bin/env python3
"""Register exact physical source margin vs quartic cost polynomial proofs."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourcePeakMarginPolynomialCharge')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_calibratedRadius_sourceMargin_fourthPowerIdentity',
    'h3Critical_calibratedFiniteCharge_forces_window_or_marginPolynomial',
    'h3Critical_noncompressedCalibratedCharge_forces_marginPolynomial',
    'h3Critical_physicalDissipationBudget_forces_marginPolynomial_or_width',
    'h3Critical_calibratedFamily_physicalCharges_force_marginPolynomial',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(stmt for name in THEOREMS for stmt in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    existing = path.read_text(encoding='utf-8')
    present = set(existing.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text(chunk + existing if prepend else existing.rstrip('\n') + '\n' + chunk,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error('expected one ' + repr(entry) + ' in ' + str(path))
    content = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, content):
            parser.error('forbidden proof placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'axiom audits')


if __name__ == '__main__':
    main()
