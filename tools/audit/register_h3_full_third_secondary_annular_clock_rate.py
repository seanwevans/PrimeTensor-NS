#!/usr/bin/env python3
"""Register the preserved cofinal secondary annular clock/rate obstruction."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryAnnularClockRate'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFull_scalar_secondaryAnnularClockOrRate244',
    'thirdFullPhysical_secondaryAnnularCharge_clockOrRate244',
    'thirdFullPhysical_secondaryHighRadialLedger_to_annularClockRate244',
    'thirdFullPhysical_noH3Trace_prescribedGauge_secondaryAnnularClockRate244',
)
DEFS = ('ThirdFullLateRetainedPrimarySecondaryAnnularClockRateCofinalLedger244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS + DEFS for row in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    known = set(old.splitlines())
    new = [line for line in lines if line not in known]
    if new:
        block = '\n'.join(new) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source_file = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (source_file, root_file, audit_file):
        if not file.is_file():
            parser.error(f'missing {file}')
    source = source_file.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing/repeated theorem: ' + name)
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing/repeated definition: ' + name)
    no_comments = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', no_comments):
        parser.error('proof placeholder found')
    if any(line.rstrip() != line for line in source.splitlines()):
        parser.error('trailing whitespace found')
    if args.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for file, lines in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        data = file.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if data.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {file}')
    print(f'PASS: secondary annular clock/rate: {len(THEOREMS)} theorems, '
          f'{len(DEFS)} defs, {len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
