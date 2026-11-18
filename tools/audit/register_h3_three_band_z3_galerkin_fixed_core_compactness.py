#!/usr/bin/env python3
"""Register the cutoff-independent fixed finite Fourier core and two-cutoff estimates."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinFixedCoreCompactness')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinWiener_sub_le244',
    'thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244',
    'thirdFullThreeBand_z3GalerkinWiener_differenceTail244',
    'thirdFullThreeBand_z3GalerkinWiener_fixedCore_split244',
    'thirdFullThreeBand_z3Galerkin_degree_lt_mem_fixedCube244',
    'thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244',
    'thirdFullThreeBand_z3Galerkin_twoCutoff_small_of_fixedCore244',
    'thirdFullThreeBand_z3Galerkin_exists_twoCutoff_fixedCore244',
)
DEFS = ('thirdFullThreeBandZ3GalerkinFixedCoreCube244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in (*DEFS, *THEOREMS) for row in (
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
            parser.error('missing file: ' + str(path))
    code = source.read_text(encoding='utf-8')
    scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub = re.sub(r'--[^\n]*', '', scrub)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrub):
        parser.error('unproved or unsafe assertion in Lean source')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace in Lean source')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate theorem: ' + name)
    for name in DEFS:
        if len(re.findall(r'(?m)^def\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate definition: ' + name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registration: ' + str(path) + ': ' + row)
    print(f'PASS: Z3 fixed-core registry: {len(DEFS)} definition, '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} probes')

if __name__ == '__main__':
    main()
