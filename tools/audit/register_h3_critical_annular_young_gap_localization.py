#!/usr/bin/env python3
"""Register q-annular weighted Young-gap and actual physical Fourier localization."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungGapLocalization'
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFullKinetic_annularAntiHeat_norm_le244', 'thirdFullKinetic_annularAntiHeat_weightedSquare244', 'thirdFullKinetic_midpointAnnulus_weightedSquare244', 'thirdFullPhysical_actualAnnularYoungGap_pointwise244', 'thirdFullPhysical_actualAnnularYoungGap_integral244')
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS
               for line in ('#check ' + NS + name, '#print axioms ' + NS + name))


def register(path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [x for x in wanted if x not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(added + old if prepend else old.rstrip('\n') + '\n' + added,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    pt = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (src, pt, audit):
        if not path.is_file():
            parser.error(f'missing file: {path}')
    source = src.read_text(encoding='utf-8')
    clean = re.sub(r'/-.*?-/', '', source, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    if re.search(r'\b(?:sorry|admit|axiom)\b', clean):
        parser.error('placeholder proof or new axiom')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', clean)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for item in wanted:
            if lines.count(item) != 1:
                parser.error(f'missing or duplicate: {item} in {path}')
    print(f'PASS: q-annular physical Young-gap localization ({len(THEOREMS)} theorems)')

if __name__ == '__main__':
    main()
