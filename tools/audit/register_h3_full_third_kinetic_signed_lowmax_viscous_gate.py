#!/usr/bin/env python3
"""Register the signed LowMax physical H3 viscous alternative."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxViscousGate'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_strictGap_signedLowMax_viscousOrClock244',
    'thirdFullPhysical_strictGap_signedLowMax_twoTimeViscousCharge244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(
    line for name in THEOREMS
    for line in ('#check ' + NS + name, '#print axioms ' + NS + name)
)


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        data = '\n'.join(missing) + '\n'
        path.write_text(data + old if prepend else old.rstrip('\n') + '\n' + data,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (source, root, audit):
        if not file.is_file():
            parser.error(f'missing file: {file}')
    code = source.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error(f'missing/duplicate declaration: {name}')
    cleaned = re.sub(r'/-.*?-/', '', code, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', cleaned):
        parser.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate registration: {path}: {line}')
    print('PASS: signed LowMax physical H3 viscous gate; ' +
          f'{len(THEOREMS)} public theorems and {len(CHECKS)} audit lines')


if __name__ == '__main__':
    main()
