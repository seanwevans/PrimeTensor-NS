#!/usr/bin/env python3
"""Idempotent registration of constructed Fourier solenoidal local existence."""
from pathlib import Path
import argparse
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3ConstructedSolenoidalLocalExistence')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinFiniteODE_transversePreserved244',
    'thirdFullThreeBand_z3Galerkin_uniformLimit_transverse244',
    'thirdFullThreeBand_z3ProjectedInitial_solenoidalLocalExistence244',
    'thirdFullThreeBand_z3FixedCubes_solenoidalLocalExistence244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def add_missing(path: Path, rows, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    new = [row for row in rows if row not in present]
    if new:
        block = '\n'.join(new) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
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
            parser.error('missing file: ' + str(path))
    code = source.read_text(encoding='utf-8')
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrubbed):
        parser.error('incomplete or unsafe declaration')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace in Lean source')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registration: ' + str(path) + ': ' + row)
    print('PASS: four constructed solenoidal theorems; eight axiom probes')

if __name__ == '__main__':
    main()
