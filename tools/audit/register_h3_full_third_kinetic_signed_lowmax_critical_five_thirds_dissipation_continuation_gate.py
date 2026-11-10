#!/usr/bin/env python3
"""Register and check the exact 5/3-weighted full H3 continuation criterion."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFiveThirdsDissipationContinuationGate'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_scalar_cubicRate_harmonicCriticalFiveThirds244',
    'thirdFullPhysical_noExtension_harmonicCriticalFiveThirdsDissipation244',
    'thirdFullPhysical_noExtension_criticalFiveThirdsDissipation_nonintegrable244',
    'thirdFullPhysical_criticalFiveThirdsDissipation_strictTail_forcesContinuation244',
    'thirdFullPhysical_criticalFiveThirdsDissipation_energyTail_forcesContinuation244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in THEOREMS for item in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(
            addition + old if prepend else old.rstrip('\n') + '\n' + addition,
            encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error(f'missing file: {path}')
    code = source.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error(f'missing/duplicate theorem: {name}')
    cleaned = re.sub(r'/-.*?-/', '', code, flags=re.S)
    cleaned = re.sub(r'--[^\n]*', '', cleaned)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', cleaned):
        parser.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('source contains trailing whitespace')
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate registration: {path}: {line}')
    print('PASS: exact 5/3-weighted full-H3 continuation criterion; '
          f'{len(THEOREMS)} declarations')


if __name__ == '__main__':
    main()
