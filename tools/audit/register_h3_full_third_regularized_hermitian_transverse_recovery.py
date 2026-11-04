#!/usr/bin/env python3
"""Register/audit smooth origin-regularized Hermitian transverse recovery."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MOD = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
       'FullThirdRegularizedHermitianTransverseRecovery')
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = (
    'thirdFullRegularizedInverseRadius244',
    'thirdFullRegularizedTransverseInput244',
    'thirdFullRegularizedRealSolenoidalSchwartz244',
)
THEOREMS = (
    'thirdFullRadialSquare_nonneg244',
    'thirdFullRegularizedRadialDen_pos244',
    'thirdFullRegularizedInverseRadius_contDiff244',
    'thirdFullRegularizedInverseRadius_even244',
    'thirdFullRegularizedTransverseInput_contDiff244',
    'thirdFullRegularizedTransverseInput_reality244',
    'thirdFullComplexTransverseNumerator_const_mul244',
    'thirdFullRegularizedTransverseInput_numerator244',
    'thirdFullRegularizedTransverseInput_numerator_solenoidal244',
    'thirdFullRegularizedRadialFactor_nonneg244',
    'thirdFullRegularizedRadialFactor_le_one244',
    'thirdFullRegularizedRadialFactor_error244',
    'thirdFullRegularizedInverseRadius_twice_square244',
    'thirdFullRegularizedHermitianProfile_exact244',
    'thirdFullRegularizedRealSolenoidalSchwartz_fourier244',
    'thirdFullRegularizedRealSolenoidalSchwartz_fourier_exact244',
    'thirdFullRegularizedRealSolenoidalSchwartz_physical_divergence244',
    'thirdFullRegularizedRealSolenoidalSchwartz_six_eq_flux244',
)
IMPORT = 'import ' + MOD
CHECKS = tuple(line for name in DEFS + THEOREMS for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
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
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, required in ((ROOT_LEAN, (IMPORT,)),
                           (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    body = SOURCE.read_text(encoding='utf-8')
    for kind, names in (('def', DEFS), ('theorem', THEOREMS)):
        for name in names:
            pattern = r'(?m)^(?:noncomputable\s+)?' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pattern, body)) != 1:
                parser.error(f'missing or duplicate {kind} {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(DEFS)} definitions, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} axiom-audit entries')

if __name__ == '__main__':
    main()
