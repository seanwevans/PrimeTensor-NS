#!/usr/bin/env python3
"""Register the solenoidal weighted H3 strong-recovery high-frequency tail checkpoint."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalUniformHighRadialRecovery')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = (
    'thirdFullSpectralHighRadialApply244',
    'thirdFullSpectralVelocityHighRadialApply244',
)
THEOREMS = (
    'thirdFullSpectralHighRadialApply_ae244',
    'thirdFullSpectralHighRadialApply_norm_le244',
    'thirdFullSpectralHighRadialApply_add244',
    'thirdFullSpectralHighRadialApply_norm_sq244',
    'thirdFullSpectralHighRadialApply_norm_tendsto_zero244',
    'thirdFullSpectralVelocityHighRadialApply_add244',
    'thirdFullSpectralVelocityHighRadialApply_norm_le244',
    'thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244',
    'thirdFullWeightedRecovery_eventuallyUniformHighRadial244',
    'thirdFullWeightedSchwartz_highRadialSixthMoment_le244',
    'thirdFullWeightedSchwartz_vectorHighRadialSixthMoment_le244',
    'exists_thirdFullPhysicalSnapshot_globalFluxAndUniformHighRadial244',
)
IMPORT = 'import ' + MODULE
CHECKS = [line for name in DEFS + THEOREMS for line in (
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
    for path, entries in ((ROOT_LEAN, (IMPORT,)),
                          (AUDIT, (IMPORT,) + tuple(CHECKS))):
        body = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if body.count(entry) != 1:
                parser.error(f'expected exactly one {entry!r} in {path}')
    src = SOURCE.read_text(encoding='utf-8')
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error(f'missing or duplicate definition: {name}')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', src):
        parser.error('proof placeholder forbidden')
    print(f'PASS: {len(DEFS)} definitions, {len(THEOREMS)} theorems; '
          f'{len(CHECKS)} declaration/axiom audit lines')


if __name__ == '__main__':
    main()
