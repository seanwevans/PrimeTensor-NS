#!/usr/bin/env python3
"""Register and audit strong weighted H3 convergence of radial regularization."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MOD = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
       'FullThirdRegularizedRadialStrongH3Convergence')
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = (
    'h3FullThirdRegularizationScale244',
    'h3FullThirdRadialRecoveryFactor244',
    'h3FullThirdRadialRecoveryRaw244',
    'h3FullThirdRadialRecoveryL2244',
    'h3FullThirdRadialRecoveryVelocity244',
)
THEOREMS = (
    'h3FullThirdRegularizationScale_pos244',
    'h3FullThirdRegularizationScale_tendsto_zero244',
    'h3FullThirdRadialRecoveryFactor_bounds244',
    'h3FullThirdRadialRecoveryFactor_continuous244',
    'h3FullThirdRadialRecoveryFactor_tendsto_one244',
    'h3FullThirdFourier_ae_nonzero244',
    'h3FullThirdRadialRecoveryRaw_memLp244',
    'h3FullThirdRadialRecoveryRaw_error_le244',
    'h3FullThirdRadialRecoveryRaw_error_tendsto_zero244',
    'h3FullThirdRadialRecoveryRaw_errorSq_aestronglyMeasurable244',
    'h3FullThirdRadialRecoveryRaw_errorSq_le244',
    'h3FullThirdRadialRecoveryL2_sub_norm_sq244',
    'h3FullThirdRadialRecoveryL2_norm_sq_tendsto_zero244',
    'h3FullThirdRadialRecoveryL2_tendsto244',
    'h3FullThirdRadialRecoveryVelocity_tendsto244',
    'h3FullThirdRadialRecoveryVelocity_cauchy244',
    'h3FullThirdRadialRecoveryFactor_eq_axis244',
)
IMPORT = 'import ' + MOD
CHECKS = tuple(s for d in DEFS + THEOREMS for s in (
    '#check PrimeTensor.FirstMonomialTriad.' + d,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + d,
))


def install(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition, encoding='utf-8')


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
            pat = r'(?m)^(?:noncomputable\s+)?(?:@\[simp\]\s+)?' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pat, body)) != 1:
                parser.error(f'missing/duplicate {kind} {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('forbidden proof placeholder')
    print(f'PASS: {len(DEFS)} defs, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} axiom-audit entries')


if __name__ == '__main__':
    main()
