#!/usr/bin/env python3
"""Register compact-gap uniform low-max solenoidal sixth Fourier flux theorems."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticCompactGapLowMaxFlux'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullKineticGapUniformLowMaxCarrier244',)
THEOREMS = (
    'thirdFullPhysical_strictSlab_independentRecovery_highMaxUniform244',
    'thirdFullPhysical_strictGap_adverseThird_uniformLowMax244',
    'thirdFullPhysical_kineticCumulativeMarginOrGapLowMax244',
    'thirdFullPhysical_noH3Trace_kineticCompactGapLowMaxCarriers244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS) for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def add_missing(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
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
    code = source.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            p.error(f'theorem missing or repeated: {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^def\s+' + re.escape(name) + r'\b', code)) != 1:
            p.error(f'definition missing or repeated: {name}')
    no_comments = re.sub(r'/-.*?-/', '', code, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', no_comments):
        p.error('placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
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
    print(f'PASS: kinetic compact-gap low-max flux: {len(DEFS)} definitions, '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} audited declarations')


if __name__ == '__main__':
    main()
