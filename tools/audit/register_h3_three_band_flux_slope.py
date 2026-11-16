#!/usr/bin/env python3
"""Register the generated-mode Leray geometry and flux-slope algebra."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandGeneratedModesFluxSlope')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_newWaveSquares244',
    'thirdFullThreeBand_newProjectedSquares244',
    'thirdFullThreeBand_newLeakCoefficients244',
    'thirdFullThreeBand_upperFluxSlope_factor244',
    'thirdFullThreeBand_upperFluxSlope_positive_iff244',
    'thirdFullThreeBand_lowerFluxSlope_negative244',
    'thirdFullThreeBand_upperFluxSlope_negative_at_six244',
    'thirdFullThreeBand_upperFluxSlope_positive_at_ten244',
    'thirdFullThreeBand_highGain_upperFluxDrops_at_six244',
    'thirdFullThreeBand_newOuterLeak_positive244',
)
DEFS = (
    'thirdFullThreeBandWaveNeg244',
    'thirdFullThreeBandNewDifferenceWave244',
    'thirdFullThreeBandNewOuterLeftWave244',
    'thirdFullThreeBandNewOuterRightWave244',
    'thirdFullThreeBandNewDifferenceSourceIm244',
    'thirdFullThreeBandNewOuterLeftSource244',
    'thirdFullThreeBandNewOuterRightSource244',
    'thirdFullThreeBandNewDifferenceProjectedIm244',
    'thirdFullThreeBandNewOuterLeftProjected244',
    'thirdFullThreeBandNewOuterRightProjected244',
    'thirdFullThreeBandNewPairLeakCoefficient244',
    'thirdFullThreeBandNewOuterLeakCoefficient244',
    'thirdFullThreeBandLowerFluxSlope244',
    'thirdFullThreeBandUpperFluxSlope244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS)
               for line in ('#check ' + NS + name, '#print axioms ' + NS + name))


def add_missing(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (path, root, audit):
        if not file.is_file():
            parser.error(f'missing: {file}')
    code = path.read_text(encoding='utf-8')
    code_no_comments = re.sub(r'/-.*?-/', '', code, flags=re.S)
    code_no_comments = re.sub(r'--[^\n]*', '', code_no_comments)
    if re.search(r'\b(?:sorry|admit|axiom)\b', code_no_comments):
        parser.error('placeholder proof or added axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for kind, symbols in (('theorem', THEOREMS), ('def', DEFS)):
        for name in symbols:
            pattern = r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pattern, code)) != 1:
                parser.error(f'missing or repeated {kind}: {name}')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for file, entries in ((root, [IMPORT]), (audit, [IMPORT, *CHECKS])):
        lines = file.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error(f'missing or duplicate registration in {file}: {entry}')
    print(f'PASS: generated-mode flux slope: {len(THEOREMS)} theorems, '
          f'{len(DEFS)} definitions, {len(CHECKS)} audit probes')


if __name__ == '__main__':
    main()
