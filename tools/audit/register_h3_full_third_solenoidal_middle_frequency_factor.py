#!/usr/bin/env python3
"""Register the exact middle-frequency factor of complex solenoidal H3 flux."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalMiddleFrequencyFactor')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'thirdFullTriadSquareRadius_middleFrequencyIdentities244',
    'thirdFullComplexCubeGap_middleFrequencyFactor244',
    'thirdFullComplexCubeGap_middleFrequencyBound244',
    'thirdFullComplexSixthPowerFlux_middleFrequencyFactorization244',
    'thirdFullComplexSixthPowerFlux_zeroMiddle244',
    'thirdFullSchwartzSixthPowerFlux_middleFrequencyFactorization244',
)
IMPORT = 'import ' + MODULE
CHECKS = [line for name in THEOREMS for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
)]


def ensure_lines(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    new = [line for line in lines if line not in existing]
    if new:
        addition = '\n'.join(new) + '\n'
        path.write_text((addition + old) if prepend else
                        (old.rstrip('\n') + '\n' + addition), encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error(f'missing {path}')
    if args.apply:
        ensure_lines(ROOT_LEAN, (IMPORT,))
        ensure_lines(AUDIT, (IMPORT,), prepend=True)
        ensure_lines(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + tuple(CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error(f'expected exactly one {entry!r} in {path}')
    contents = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', contents)) != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', contents):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(THEOREMS)} theorems, {len(CHECKS)} axiom audit lines')


if __name__ == '__main__':
    main()
