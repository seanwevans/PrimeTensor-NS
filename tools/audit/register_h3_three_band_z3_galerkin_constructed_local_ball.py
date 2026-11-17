#!/usr/bin/env python3
"""Register constructed local finite Galerkin moving-ball persistence."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedLocalBall')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3MovingRadiusWindow_pos244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_continuousAt244',
    'thirdFullThreeBand_z3GalerkinFiniteField_constructedLocalMovingBall244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def add_missing(path, rows, prepend=False):
    text = path.read_text(encoding='utf-8')
    seen = set(text.splitlines())
    missing = [row for row in rows if row not in seen]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + text if prepend else text.rstrip('\n') + '\n' + block,
                        encoding='utf-8')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, root, audit):
        if not p.is_file():
            parser.error('missing source/registry: ' + str(p))
    code = source.read_text(encoding='utf-8')
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrubbed):
        parser.error('forbidden proof escape')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', scrubbed)) != 1:
            parser.error('missing or duplicated theorem: ' + name)
    if any(line.rstrip() != line for line in code.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for p, rows in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = p.read_text(encoding='utf-8').splitlines()
        for row in rows:
            if lines.count(row) != 1:
                parser.error(f'missing or duplicated registry line: {p.name}: {row}')
    print('PASS: constructed finite Galerkin local ball registry; '
          f'{len(THEOREMS)} theorems and {len(CHECKS)} axiom/declaration probes')

if __name__ == '__main__':
    main()
