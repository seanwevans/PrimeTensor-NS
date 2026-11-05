#!/usr/bin/env python3
"""Idempotently register the genuine solenoidal outer-minimum H3 Fourier budgets."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalOuterMinimumH3Budget')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'thirdFullComplexSixSymbol_swapFirstTwo244',
    'thirdFullComplexSixSymbol_swapLastTwo244',
    'thirdFullComplexSixthPowerFlux_swapFirstTwo244',
    'thirdFullComplexSixthPowerFlux_swapLastTwo244',
    'thirdFullComplexSixthPowerFlux_lowFirstH3Bound244',
    'thirdFullComplexSixthPowerFlux_lowLastH3Bound244',
    'thirdFull_integral_norm_le_rightOuter_L1244',
    'thirdFullSchwartzSixthPowerFlux_lowFirstIntegral_le_H3Moments244',
    'thirdFullSchwartzSixthPowerFlux_lowLastIntegral_le_H3Moments244',
    'thirdFullWeightedSchwartz_lowFirstIntegral_le_coordinateBound244',
    'thirdFullWeightedSchwartz_lowLastIntegral_le_coordinateBound244',
    'exists_thirdFullPhysicalSnapshot_outerMinimumH3Budgets244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in THEOREMS for item in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def ensure_lines(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    addition = [line for line in lines if line not in existing]
    if addition:
        payload = '\n'.join(addition) + '\n'
        path.write_text(payload + old if prepend else
                        old.rstrip('\n') + '\n' + payload,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for file in (SOURCE, ROOT_LEAN, AUDIT):
        if not file.is_file():
            parser.error(f'missing {file}')
    if args.apply:
        ensure_lines(ROOT_LEAN, (IMPORT,))
        ensure_lines(AUDIT, (IMPORT,), prepend=True)
        ensure_lines(AUDIT, CHECKS)
    for file, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        existing = file.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if existing.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {file}')
    src = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', src):
        parser.error('proof placeholder forbidden')
    print(f'PASS: {len(THEOREMS)} theorems; {len(CHECKS)} axiom-audit entries')


if __name__ == '__main__':
    main()
