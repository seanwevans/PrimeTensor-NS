#!/usr/bin/env python3
"""Register genuine infinite full-Leray-source Fourier completion."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteLeraySourceLimit')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinQuadratic_allOutputs50000_244',
    'thirdFullThreeBand_z3Galerkin_sourceModeCauchy244',
    'thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244',
    'thirdFullThreeBand_z3Galerkin_actualInfiniteSourceLimit244',
    'thirdFullThreeBand_z3Galerkin_exists_constructedInfiniteSourceLimit244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def add_missing(path: Path, rows, prepend=False):
    original = path.read_text(encoding='utf-8')
    known = set(original.splitlines())
    missing = [row for row in rows if row not in known]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + original if prepend else original.rstrip('\n') + '\n' + block,
                        encoding='utf-8')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error('missing: ' + str(path))
    code = source.read_text(encoding='utf-8')
    scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub = re.sub(r'--[^\n]*', '', scrub)
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub):
        parser.error('unproved/unsafe declaration')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate theorem: ' + name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registry line: ' + str(path) + ': ' + row)
    print(f'PASS: infinite Leray source: {len(THEOREMS)} theorems; {len(CHECKS)} audit probes')

if __name__ == '__main__':
    main()
