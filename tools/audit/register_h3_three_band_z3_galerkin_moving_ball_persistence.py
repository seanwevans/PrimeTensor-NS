#!/usr/bin/env python3
"""Register cutoff-independent Galerkin moving analytic-ball comparison and persistence."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinMovingBallPersistence')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3ScalarMovingBall_comparison244',
    'thirdFullThreeBand_z3SmoothWienerDerivative_cutoff_bound244',
    'thirdFullThreeBand_z3SmoothMovingMass_continuousOn244',
    'thirdFullThreeBand_z3SmoothMovingDerivative_bounded244',
    'thirdFullThreeBand_z3SmoothMovingBall_persists244',
    'thirdFullThreeBand_z3MovingBall_persists_of_strict_initial244',
    'thirdFullThreeBand_z3FiniteGalerkin_degreeCap_exists244',
    'thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244',
    'thirdFullThreeBand_z3MovingBall_cutoffFreeHighRadius244',
    'thirdFullThreeBand_z3MovingBall_cutoffFreeODEResidual244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for theorem in THEOREMS for row in (
    '#check ' + NS + theorem,
    '#print axioms ' + NS + theorem,
))


def insert_missing(path: Path, rows, prepend=False):
    original = path.read_text(encoding='utf-8')
    present = set(original.splitlines())
    missing = [x for x in rows if x not in present]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + original if prepend else original.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument('--apply', action='store_true')
    actions.add_argument('--check', action='store_true')
    opts = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, root, audit):
        if not p.is_file():
            parser.error('missing file: ' + str(p))
    code = source.read_text(encoding='utf-8')
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', scrubbed):
        parser.error('forbidden unproved assertion')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for theorem in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(theorem) + r'\b', code)) != 1:
            parser.error('missing or duplicated theorem: ' + theorem)
    if opts.apply:
        insert_missing(root, (IMPORT,))
        insert_missing(audit, (IMPORT,), prepend=True)
        insert_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error(f'missing or duplicate registration: {path}: {row}')
    print(f'PASS: Galerkin moving ball persistence: {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} declaration/axiom probes')


if __name__ == '__main__':
    main()
