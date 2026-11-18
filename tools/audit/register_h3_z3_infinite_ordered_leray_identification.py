#!/usr/bin/env python3
"""Register the infinite ordered Z3 Leray convolution identification theorems."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3InfiniteOrderedLerayIdentification')
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = (
    'thirdFullThreeBandZ3InfiniteOrderedLeray244',
    'thirdFullThreeBandZ3GalerkinExhausts244',
)
THEOREMS = (
    'thirdFullThreeBand_z3InfiniteWiener_unweightedSummable244',
    'thirdFullThreeBand_z3InfiniteWiener_frequencyAmplitude500_244',
    'thirdFullThreeBand_z3InfiniteOrderedLeray_summable244',
    'thirdFullThreeBand_z3GalerkinQuadratic_partnerFilter244',
    'thirdFullThreeBand_z3Galerkin_partnerFilter_tendsto244',
    'thirdFullThreeBand_z3GalerkinQuadratic_exhausting_tendstoInfinite244',
    'thirdFullThreeBand_z3GalerkinQuadratic_toInfiniteField_stability244',
    'thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244',
    'thirdFullThreeBand_z3Galerkin_exists_identifiedInfiniteLeray244',
)
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
            parser.error('missing path: ' + str(path))
    code = source.read_text(encoding='utf-8')
    stripped = re.sub(r'/-.*?-/', '', code, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', stripped):
        parser.error('unproved or unsafe declarations')
    if any(x != x.rstrip() for x in code.splitlines()):
        parser.error('trailing whitespace')
    for keyword, names in (('theorem', THEOREMS), ('def', DEFS)):
        for name in names:
            if len(re.findall(r'(?m)^(?:noncomputable\s+)?'+keyword+r'\s+'+re.escape(name)+r'\b', code)) != 1:
                parser.error('missing/duplicate '+keyword+': '+name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registration: '+str(path)+': '+row)
    print('PASS: Z3 infinite Leray identification: {} theorems, {} definitions, {} probes'.format(
        len(THEOREMS), len(DEFS), len(CHECKS)))

if __name__ == '__main__':
    main()
