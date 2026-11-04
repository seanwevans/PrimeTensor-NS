#!/usr/bin/env python3
"""Register the H3 corrected sixth-power flux and physical matched-family limit."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MOD = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
       'FullThirdSchwartzLongitudinalFluxDefect')
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'thirdFullComplexSix_eq_flux_add_longitudinal244',
    'thirdFullComplexLongitudinalFluxDefect_zero_of_solenoidal244',
    'thirdFullSchwartzComplexSix_eq_flux_add_longitudinal244',
    'thirdFullSchwartz_correctedFlux_integrable244',
    'thirdFullSchwartz_correctedFlux_integral244',
    'fullThirdSchwartzFourierCoefficient_eq_correctedFlux244',
    'fullSchwartzThirdCommutator_eq_correctedFlux244',
    'h3MatchedSchwartz_correctedFlux_tendsto244',
    'h3Path_matchedSchwartz_correctedFlux_tendsto_physical244',
)
DEFS = (
    'thirdFullComplexLongitudinalFluxDefect244',
    'thirdFullSchwartzLongitudinalFluxDefect244',
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
        content = '\n'.join(missing) + '\n'
        path.write_text((content + old) if prepend else
                        (old.rstrip('\n') + '\n' + content), encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    g = parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--apply', action='store_true')
    g.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for p in (SOURCE, ROOT_LEAN, AUDIT):
        if not p.is_file():
            parser.error(f'missing {p}')
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for p, expected in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        actual = p.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if actual.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {p}')
    source = SOURCE.read_text(encoding='utf-8')
    for kind, names in (('theorem', THEOREMS), ('def', DEFS)):
        for name in names:
            if len(re.findall(r'(?m)^(?:noncomputable\s+)?' + kind + r'\s+' + re.escape(name) + r'\b', source)) != 1:
                parser.error(f'missing or duplicate {kind} {name}')
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(forbidden, source):
            parser.error(f'forbidden proof placeholder: {forbidden}')
    print(f'PASS: {len(THEOREMS)} theorems, {len(DEFS)} definitions, '
          f'{len(CHECKS)} axiom-audit entries')

if __name__ == '__main__':
    main()
