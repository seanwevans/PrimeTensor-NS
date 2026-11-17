#!/usr/bin/env python3
"""Register strong finite Galerkin continuation through the Picard joining time."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinRestartSeam')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinRestartGlue_seamHasDerivAt244',
    'thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
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
    if args.apply:
        insert_missing(ROOT / 'PrimeTensor.lean', (IMPORT,))
        insert_missing(audit, (IMPORT,), prepend=True)
        insert_missing(audit, CHECKS)
    for path, required in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        existing = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if existing.count(entry) != 1:
                parser.error('missing/duplicate registration: ' + str(path) + ': ' + entry)
    print(f'PASS: Z3 Galerkin two-sided restart seam registry: '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} probes')


if __name__ == '__main__':
    main()
