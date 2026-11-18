#!/usr/bin/env python3
"""Register infinite Z3 Fourier Wiener limit and full strong convergence theorems."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteWienerLimit')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3Galerkin_zeroExtend_arbitraryFiniteMass_le244',
    'thirdFullThreeBand_z3Galerkin_uniformCoordinateLimit_finiteHighMass244',
    'thirdFullThreeBand_z3Galerkin_limit_highWiener_summable244',
    'thirdFullThreeBand_z3Galerkin_finiteToInfinite_fixedCore244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244',
    'thirdFullThreeBand_z3Galerkin_exists_actualInfiniteWienerLimit244',
)
DEFS = ('thirdFullThreeBandZ3InfiniteWienerMass244',)
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
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrubbed):
        parser.error('unproved or unsafe declaration')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for keyword, names in (('theorem', THEOREMS), ('def', DEFS)):
        for name in names:
            if len(re.findall(r'(?m)^(?:noncomputable\s+)?' + keyword + r'\s+' + re.escape(name) + r'\b', code)) != 1:
                parser.error('missing/duplicate ' + keyword + ': ' + name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registry row: '+str(path)+': '+row)
    print('PASS: infinite Z3 Wiener limit: {} theorems, {} definitions, {} probes'.format(
        len(THEOREMS), len(DEFS), len(CHECKS)))
if __name__ == '__main__':
    main()
