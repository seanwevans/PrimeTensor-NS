#!/usr/bin/env python3
"""Register the fresh finite Z3 Galerkin Picard local-existence bridge."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinFiniteODELocalExistence')
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = (
    'thirdFullThreeBandZ3GalerkinFiniteState244',
    'thirdFullThreeBandZ3GalerkinFiniteExtend244',
    'thirdFullThreeBandZ3GalerkinFiniteField244',
)
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinFiniteExtend_on244',
    'thirdFullThreeBand_z3GalerkinFiniteExtend_off244',
    'thirdFullThreeBand_z3GalerkinFiniteExtend_contDiff244',
    'thirdFullThreeBand_z3GalerkinFiniteField_coord_contDiff244',
    'thirdFullThreeBand_z3GalerkinFiniteField_contDiff244',
    'thirdFullThreeBand_z3GalerkinFiniteField_exists_local244',
)
IMPORT = 'import ' + MODULE
CHECKS = [item for name in (*DEFS, *THEOREMS) for item in
          ('#check ' + NS + name, '#print axioms ' + NS + name)]

def insert(path, rows, prepend=False):
    src = path.read_text(encoding='utf-8')
    have = set(src.splitlines())
    missing = [r for r in rows if r not in have]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + src if prepend else src.rstrip('\n') + '\n' + block,
                        encoding='utf-8')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = ap.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, root, audit):
        if not p.is_file():
            ap.error('Missing: ' + str(p))
    code = source.read_text(encoding='utf-8')
    scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub = re.sub(r'--[^\n]*', '', scrub)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrub):
        ap.error('forbidden declaration or proof escape')
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:def|abbrev)\s+' + re.escape(name) + r'\b', scrub)) != 1:
            ap.error('missing or duplicated definition ' + name)
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', scrub)) != 1:
            ap.error('missing or duplicated theorem ' + name)
    if any(line.rstrip() != line for line in code.splitlines()):
        ap.error('trailing whitespace')
    if args.apply:
        insert(root, [IMPORT])
        insert(audit, [IMPORT], prepend=True)
        insert(audit, CHECKS)
    for p, want in ((root, [IMPORT]), (audit, [IMPORT, *CHECKS])):
        lines = p.read_text(encoding='utf-8').splitlines()
        for line in want:
            if lines.count(line) != 1:
                ap.error(f'missing or duplicate registry line in {p.name}: {line}')
    print('PASS: finite Galerkin local-existence source and registry checks')

if __name__ == '__main__':
    main()
