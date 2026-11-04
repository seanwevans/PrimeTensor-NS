#!/usr/bin/env python3
"""Register exact global L2-L2-L1 estimates for full solenoidal H3 flux budget."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalBudgetMomentControl')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = (
    'thirdFullBudgetMomentAmplitude244',
    'thirdFullBudgetFirstMoment244',
    'thirdFullBudgetFourierMass244',
)
THEOREMS = (
    'thirdFullBudgetMoments_integrable244',
    'thirdFullBudgetMoments_nonneg244',
    'thirdFullSchwartzSixthFluxBudget_le_twoMomentProducts244',
    'thirdFullSchwartzSixthFluxBudget_le_squareMomentDensity244',
    'thirdFullSchwartzSixthFluxTotalBudget_le_L2FirstMoment244',
    'thirdFullSchwartzSixthFluxTotalBudget_uniform_of_moments244',
    'thirdFullSchwartzSixthPowerFlux_movingAnnulus_vanishes_of_moments244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in DEFS + THEOREMS for item in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
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
            parser.error('missing ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, required in ((ROOT_LEAN, (IMPORT,)),
                           (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error('expected exactly one ' + repr(line) + ' in ' + str(path))
    body = SOURCE.read_text(encoding='utf-8')
    for name in DEFS:
        pattern = r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b'
        if len(re.findall(pattern, body)) != 1:
            parser.error('missing or duplicate definition ' + name)
    for name in THEOREMS:
        pattern = r'(?m)^theorem\s+' + re.escape(name) + r'\b'
        if len(re.findall(pattern, body)) != 1:
            parser.error('missing or duplicate theorem ' + name)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(DEFS)} definitions, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} axiom-audit entries')

if __name__ == '__main__':
    main()
