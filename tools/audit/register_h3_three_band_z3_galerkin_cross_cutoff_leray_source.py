#!/usr/bin/env python3
"""Register exact cross-cutoff full Leray-source Cauchy theorems."""
import argparse
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinCrossCutoffLeraySource')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3ComplexTransport_zeroLeft244',
    'thirdFullThreeBand_z3ComplexTransport_zeroRight244',
    'thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244',
    'thirdFullThreeBand_z3GalerkinTwoCutoff_sourceLipschitz1000_244',
    'thirdFullThreeBand_z3GalerkinTwoCutoff_fullFieldLipschitz1010_244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_fullNSFieldCauchy244',
    'thirdFullThreeBand_z3Galerkin_exists_constructedFullLeraySourceCauchy244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def add_missing(path: Path, rows, prepend=False):
    content = path.read_text(encoding='utf-8')
    present = set(content.splitlines())
    missing = [row for row in rows if row not in present]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + content if prepend else content.rstrip('\n') + '\n' + block,
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
        parser.error('source contains trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing/duplicate theorem: '+name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registration: '+str(path)+': '+row)
    print(f'PASS: Z3 true two-cutoff Leray source, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} check/axiom probes')

if __name__ == '__main__':
    main()
