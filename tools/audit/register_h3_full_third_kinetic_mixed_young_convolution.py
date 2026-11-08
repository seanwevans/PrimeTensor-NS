#!/usr/bin/env python3
"""Register asymmetric Fourier Young estimate for native mixed sixth-flux budgets."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticMixedYoungConvolution'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullKineticPolarAmplitude244',)
THEOREMS = (
    'thirdFullKinetic_mixedYoung_quadratic244',
    'thirdFullKinetic_mixedYoung_scaled244',
    'thirdFullKineticPolarAmplitude_nonneg244',
    'thirdFullKinetic_lowMax_mixedBudget_le_amplitudes244',
    'thirdFullKinetic_lowMax_mixedBudget_le_L2L2L1244',
    'thirdFullKinetic_lowMax_mixedBudget_scaled244',
    'thirdFullKinetic_lowMax_mixedFlux_le_scaledL2L2L1244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS) for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    lines = set(old.splitlines())
    missing = [line for line in wanted if line not in lines]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    p = argparse.ArgumentParser()
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = p.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            p.error(f'missing file: {path}')
    src = source.read_text(encoding='utf-8')
    for kind, names in ((r'noncomputable\s+def', DEFS), (r'theorem', THEOREMS)):
        for name in names:
            pat = r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pat, src)) != 1:
                p.error(f'declaration missing or repeated: {name}')
    sans_comments = re.sub(r'/-.*?-/', '', src, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', sans_comments):
        p.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in src.splitlines()):
        p.error('trailing whitespace')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                p.error(f'missing or duplicate registration in {path}: {line}')
    print(f'PASS: kinetic mixed Fourier Young: {len(DEFS)} definitions, '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} audit declarations')


if __name__ == '__main__':
    main()
