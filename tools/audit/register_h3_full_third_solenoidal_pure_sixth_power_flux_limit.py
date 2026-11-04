#!/usr/bin/env python3
"""Register the exact solenoidal removal of the H3 longitudinal Fourier defect."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]
MOD = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
       'FullThirdSolenoidalPureSixthPowerFluxLimit')
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'thirdFullSchwartz_longitudinalDefect_zero_of_complexDivergence244',
    'thirdFullSchwartz_commutator_eq_pureFlux_of_complexDivergence244',
    'thirdFullSchwartz_pureFlux_tendsto_of_complexDivergence244',
    'exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244',
)
IMPORT = 'import ' + MOD
CHECKS = tuple(line for name in THEOREMS for line in (
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
    for name in THEOREMS:
        pattern = r'(?m)^theorem\s+' + re.escape(name) + r'\b'
        if len(re.findall(pattern, body)) != 1:
            parser.error('missing or duplicate theorem ' + name)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(THEOREMS)} theorems, {len(CHECKS)} axiom-audit entries')

if __name__ == '__main__':
    main()
