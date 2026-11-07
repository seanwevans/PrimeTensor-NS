#!/usr/bin/env python3
"""Register actual kinetic-only low-band source and H3 time-modulus proofs."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticLowBandSourceLipschitz'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244',
    'thirdFullPhysical_actualLowBandSource_kineticCeiling244',
    'thirdFullPhysical_actualLowBandFourierSource_kineticCeiling244',
    'thirdFullPhysical_kineticLowBandFourierCoordinateLipschitz244',
    'thirdFullPhysical_kineticLowRadialH3Lipschitz244',
    'thirdFullPhysical_secondarySelectedTimes_fixedLowBandDrift244',
)
DEFS = ('thirdFullPhysicalKineticLowBandSourceCeiling244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(s for name in THEOREMS + DEFS for s in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    new = [line for line in lines if line not in seen]
    if new:
        block = '\n'.join(new) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source_file = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source_file, root_file, audit_file):
        if not path.is_file():
            parser.error(f'missing {path}')
    source = source_file.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/repeated theorem {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/repeated definition {name}')
    without_comments = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
        parser.error('proof placeholder found')
    if any(line.rstrip() != line for line in source.splitlines()):
        parser.error('trailing whitespace found')
    if args.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for path, lines in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        data = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if data.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: kinetic physical low-band source/time, '
          f'{len(THEOREMS)} theorems, {len(DEFS)} definitions, '
          f'{len(CHECKS)} proof/axiom checks')


if __name__ == '__main__':
    main()
