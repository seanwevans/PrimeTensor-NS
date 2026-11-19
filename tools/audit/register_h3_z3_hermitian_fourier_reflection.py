#!/usr/bin/env python3
"""Idempotent source/index registration for Z3 Fourier Hermitian reflection."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3HermitianFourierReflection')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3BandConj_apply244',
    'thirdFullThreeBand_z3BandConj_involutive244',
    'thirdFullThreeBand_z3BandConj_add244',
    'thirdFullThreeBand_z3BandConj_realSmul244',
    'thirdFullThreeBand_z3BandConj_zero244',
    'thirdFullThreeBand_z3BandConj_norm244',
    'thirdFullThreeBand_z3BandConj_continuous244',
    'thirdFullThreeBand_z3ComplexFrequency_neg244',
    'thirdFullThreeBand_z3ComplexFrequency_norm_neg244',
    'thirdFullThreeBand_z3Degree_neg244',
    'thirdFullThreeBand_z3Weight_neg244',
    'thirdFullThreeBand_z3HermitianReflect_involutive244',
    'thirdFullThreeBand_z3HermitianAverage_reality244',
    'thirdFullThreeBand_z3HermitianAverage_norm244',
    'thirdFullThreeBand_z3FixedCoreCube_neg244',
    'thirdFullThreeBand_z3FiniteExtend_Hermitian244',
    'thirdFullThreeBand_z3Hermitian_initialRestriction244',
    'thirdFullThreeBand_z3Hermitian_uniformLimit244',
    'thirdFullThreeBand_z3GalerkinHermitian_uniformLimit244',
)
DEFS = (
    'thirdFullThreeBandZ3BandConj244',
    'thirdFullThreeBandZ3FourierHermitian244',
    'thirdFullThreeBandZ3HermitianReflect244',
    'thirdFullThreeBandZ3HermitianAverage244',
)
IMPORT = 'import ' + MODULE
PROBES = tuple(row for name in (*DEFS, *THEOREMS) for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))


def add_missing(path: Path, rows, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    extra = [line for line in rows if line not in present]
    if extra:
        block = '\n'.join(extra) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
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
    for path in (source, root, audit):
        if not path.is_file():
            parser.error('missing required source: ' + str(path))
    code = source.read_text(encoding='utf-8')
    scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub = re.sub(r'--[^\n]*', '', scrub)
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub):
        parser.error('incomplete/unsafe proof')
    for name in THEOREMS:
        matches = re.findall(r'(?m)^(?:@\[[^\n]*\]\s*)?theorem\s+' +
                             re.escape(name) + r'\b', code)
        if len(matches) != 1:
            parser.error('missing/duplicate theorem: ' + name)
    for name in DEFS:
        if len(re.findall(r'(?m)^def\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate definition: ' + name)
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace in Lean source')
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, PROBES)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *PROBES))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error('missing/duplicate registration: ' + str(path) + ': ' + line)
    print(f'PASS: {len(THEOREMS)} Hermitian theorems, {len(DEFS)} definitions, {len(PROBES)} audit probes')


if __name__ == '__main__':
    main()
