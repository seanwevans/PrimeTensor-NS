#!/usr/bin/env python3
"""Install/check the finite-axis smooth regularized Leray numerator bridge."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MOD = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
       'FullThirdFiniteAxisRegularizedLerayNumerator')
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'thirdFullAxisDot_hilbertRadiusSquare244',
    'thirdFullAxisMixedDot_fin3_eq244',
    'h3FullThirdLerayCoefficient_scaled244',
    'h3FullThirdLerayAction_scaled244',
    'h3FullThirdLerayAction_axisNumerator244',
    'h3FullThirdFiniteLeray_eq_axisNumerator244',
    'h3FullThirdRegularizedFiniteLeray_axisFraction244',
)
IMPORT = 'import ' + MOD
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


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
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', body)) != 1:
            parser.error(f'missing or duplicate theorem {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(THEOREMS)} theorems, {len(CHECKS)} axiom-audit entries')


if __name__ == '__main__':
    main()
