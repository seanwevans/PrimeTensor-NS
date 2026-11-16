#!/usr/bin/env python3
"""Register full-convolution three-band second temporal variation and audit."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandFluxSecondVariation')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_curvatures_factor244',
    'thirdFullThreeBand_inviscidCurvatures_negative244',
    'thirdFullThreeBand_curvatures_at_ten_formula244',
    'thirdFullThreeBand_curvatures_at_ten_signs244',
    'thirdFullThreeBand_opposedFluxCurvatures_at_ten244',
)
DEFS = (
    'thirdFullThreeBandLowerFluxCurvature244',
    'thirdFullThreeBandUpperFluxCurvature244',
    'thirdFullThreeBandLowerCurvatureShape244',
    'thirdFullThreeBandUpperCurvatureShape244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS)
               for line in ('#check ' + NS + name,
                            '#print axioms ' + NS + name))


def add_missing(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(added + old if prepend else
                        old.rstrip('\n') + '\n' + added, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    args = parser.parse_args()
    lean = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for f in (lean, root, audit):
        if not f.is_file():
            parser.error(f'missing file {f}')
    src = lean.read_text(encoding='utf-8')
    stripped = re.sub(r'/-.*?-/', '', src, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    if re.search(r'\b(?:sorry|admit|axiom)\b', stripped):
        parser.error('placeholder proof or new axiom')
    if any(line != line.rstrip() for line in src.splitlines()):
        parser.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error(f'missing or repeated theorem: {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^def\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error(f'missing or repeated definition: {name}')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for f, expected in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=f.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line)!=1:
                parser.error(f'missing/duplicate registration in {f}: {line}')
    print(f'PASS: three-band flux second variation: {len(THEOREMS)} theorems, '
          f'{len(DEFS)} definitions, {len(CHECKS)} trust probes')

if __name__ == '__main__':
    main()
