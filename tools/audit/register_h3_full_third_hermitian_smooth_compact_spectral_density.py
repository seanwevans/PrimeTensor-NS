#!/usr/bin/env python3
"""Register and structurally audit compact Hermitian H3 spectral density."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdHermitianSmoothCompactSpectralDensity')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = (
    'h3HermitianConjugateReflectCLM244',
    'h3FourierHermitianAverageCLM244',
    'h3HermitianSmoothCompactAverage244',
)
THEOREMS = (
    'h3HermitianConjugateReflectCLM_ae244',
    'h3FourierConjL2L_involutive244',
    'h3FourierHermitianAverageCLM_apply244',
    'h3FourierHermitianAverageCLM_fixed244',
    'h3HermitianSmoothCompactAverage_contDiff244',
    'h3HermitianSmoothCompactAverage_hasCompactSupport244',
    'h3HermitianSmoothCompactAverage_reality244',
    'h3HermitianSmoothCompactAverage_toLp244',
    'exists_h3HermitianSmoothCompactSpectralApprox244',
    'exists_h3HermitianSmoothCompactSpectralVelocityApprox244',
    'exists_h3RealSolenoidalProjectedCompactSpectralApprox244',
    'exists_h3RealSolenoidalProjectedCompactSpectralSequence244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for n in DEFS + THEOREMS for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + n,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + n,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
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
    for p in (SOURCE, ROOT_LEAN, AUDIT):
        if not p.is_file():
            parser.error(f'missing {p}')
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for p, expected in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = p.read_text(encoding='utf-8').splitlines()
        for item in expected:
            if lines.count(item) != 1:
                parser.error(f'expected exactly one occurrence of {item!r} in {p}')
    src = SOURCE.read_text(encoding='utf-8')
    for kind, names in (('def', DEFS), ('theorem', THEOREMS)):
        for name in names:
            pattern = r'(?m)^(?:noncomputable\s+)?(?:@\[simp\]\s*)?' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pattern, src)) != 1:
                parser.error(f'missing or duplicate {kind} {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', src):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(DEFS)} definitions, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} audit entries')


if __name__ == '__main__':
    main()
