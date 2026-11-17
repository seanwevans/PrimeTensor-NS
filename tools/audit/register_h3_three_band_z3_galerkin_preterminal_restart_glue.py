#!/usr/bin/env python3
"""Register finite Z3 complete-Leray preterminal endpoint Picard restart and paste."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinPreterminalRestartGlue')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinPreterminalTimes_exists244',
    'thirdFullThreeBand_z3GalerkinPreterminalPicardRestart244',
    'thirdFullThreeBand_z3GalerkinRestartGlue_before244',
    'thirdFullThreeBand_z3GalerkinRestartGlue_after244',
    'thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244',
    'thirdFullThreeBand_z3GalerkinRestartGlue_rightODE244',
    'thirdFullThreeBand_z3GalerkinPreterminalGluedRestart244',
)
DEFINITIONS = ('thirdFullThreeBandZ3GalerkinRestartGlue244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in (*DEFINITIONS, *THEOREMS) for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))


def insert_missing(path: Path, rows, prepend=False):
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
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrubbed):
        parser.error('forbidden assertion in Lean source')
    if any(ln != ln.rstrip() for ln in code.splitlines()):
        parser.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate theorem: ' + name)
    for name in DEFINITIONS:
        if len(re.findall(r'(?m)^(?:noncomputable )?def\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate definition: ' + name)
    if args.apply:
        insert_missing(root, (IMPORT,))
        insert_missing(audit, (IMPORT,), prepend=True)
        insert_missing(audit, CHECKS)
    for path, required in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        existing = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if existing.count(entry) != 1:
                parser.error('missing/duplicate registration: ' + str(path) + ': ' + entry)
    print(f'PASS: Z3 Galerkin endpoint Picard restart registry: '
          f'{len(THEOREMS)} theorems, {len(DEFINITIONS)} definition, '
          f'{len(CHECKS)} probes')


if __name__ == '__main__':
    main()
