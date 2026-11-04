#!/usr/bin/env python3
"""Idempotently register the unrestricted physical H3 sixth-power flux identity."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MOD = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
       'FullThirdSchwartzPhysicalFluxIdentity')
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
BRIDGE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/'
                 'Transport/FullThirdSchwartzPhysicalSevenBridge.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
BRIDGE_THEOREMS = (
    'thirdFullSchwartzGradientFourier_eq_halfIntegral244',
    'thirdFullSchwartzPhysicalHalfSeven_eq_gradient_add_triad244',
    'thirdFullSchwartzPhysicalHalfSeven_fourierCoefficient244',
)
THEOREMS = (
    'fullThirdSchwartzFourierCoefficient_eq_physicalHalfIntegral244',
    'fullThirdSchwartzFourierCoefficient_eq_sixthPowerFlux244',
    'fullThirdSeventhPhase_divThree_real_eq_imag244',
    'fullSchwartzThirdCommutator_eq_sixthPowerFlux_integral244',
)
IMPORT = 'import ' + MOD
CHECKS = tuple(line for name in BRIDGE_THEOREMS + THEOREMS for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [v for v in lines if v not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, BRIDGE, ROOT_LEAN, AUDIT):
        if not path.exists():
            parser.error('missing required path: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        content_lines = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if content_lines.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    for path, names in ((SOURCE, THEOREMS), (BRIDGE, BRIDGE_THEOREMS)):
        src = path.read_text(encoding='utf-8')
        for name in names:
            if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
                parser.error('missing or duplicate theorem: ' + name)
        for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
            if re.search(forbidden, src):
                parser.error('proof placeholder detected: ' + forbidden)
    print(f'PASS: {len(BRIDGE_THEOREMS) + len(THEOREMS)} theorems, '
          f'{len(CHECKS)} axiom-audit entries')


if __name__ == '__main__':
    main()
