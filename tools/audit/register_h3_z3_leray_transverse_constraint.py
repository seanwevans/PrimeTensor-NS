#!/usr/bin/env python3
"""Register the finite/infinite transverse Fourier Leray constraint proofs."""
from pathlib import Path
import argparse
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3LerayTransverseConstraint')
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullThreeBandZ3FourierIsTransverse244',
        'thirdFullThreeBandZ3ProjectedInitial244')
THEOREMS = (
    'thirdFullThreeBand_z3ComplexLeray_transverse244',
    'thirdFullThreeBand_z3ComplexTransport_transverse244',
    'thirdFullThreeBand_z3GalerkinQuadratic_transverse244',
    'thirdFullThreeBand_z3InfiniteOrderedLeray_transverse244',
    'thirdFullThreeBand_z3InfiniteOrderedLeray_transverse_of_mass244',
    'thirdFullThreeBand_z3GalerkinNSField_longitudinalHeat244',
    'thirdFullThreeBand_z3ProjectedInitial_admissible244',
    'thirdFullThreeBand_z3ProjectedInitial_transverse244',
    'thirdFullThreeBand_z3ProjectedInitial_localFourierExistence244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(v for n in (*DEFS, *THEOREMS) for v in
               ('#check ' + NS + n, '#print axioms ' + NS + n))

def add_missing(path, rows, prepend=False):
    original = path.read_text(encoding='utf-8')
    existing = set(original.splitlines())
    missing = [r for r in rows if r not in existing]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + original if prepend else original.rstrip('\n') + '\n' + block,
                        encoding='utf-8')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    entry = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, entry, audit):
        if not path.is_file():
            parser.error('missing '+str(path))
    code = source.read_text(encoding='utf-8')
    clean = re.sub(r'/-.*?-/', '', code, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', clean):
        parser.error('unsafe or incomplete declaration')
    if any(l != l.rstrip() for l in code.splitlines()):
        parser.error('trailing whitespace')
    for word, names in [('theorem',THEOREMS),('def',DEFS)]:
        for n in names:
            if len(re.findall(r'(?m)^(?:noncomputable\s+)?'+word+r'\s+'+re.escape(n)+r'\b', code)) != 1:
                parser.error('missing or duplicate '+word+' '+n)
    if args.apply:
        add_missing(entry, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((entry, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error('missing/duplicate audit entry '+str(path)+' '+line)
    print(f'PASS: transverse Z3 Leray: {len(THEOREMS)} theorems; '
          f'{len(DEFS)} definitions; {len(CHECKS)} probes')

if __name__ == '__main__':
    main()
