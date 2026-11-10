#!/usr/bin/env python3
"""Register and audit two-scale physical critical H3 fifth-order absorption."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalTwoScaleFifthAbsorption'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_twoScale_halfFifth_scalar244',
    'thirdFullPhysical_nearCriticalAnchor_forces_twoScaleFifthHeat244',
    'thirdFullPhysical_nearCriticalAnchor_forces_halfFifthAbsorption244',
    'thirdFullPhysical_nearCriticalAnchor_forces_highSixthDeficit244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(entry for n in THEOREMS
               for entry in ('#check ' + NS + n, '#print axioms ' + NS + n))

def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        add = '\n'.join(missing) + '\n'
        path.write_text(add + old if prepend else old.rstrip('\n') + '\n' + add,
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
    for file in (src, pt, audit):
        if not file.is_file():
            parser.error(f'missing file {file}')
    content = src.read_text(encoding='utf-8')
    content = re.sub(r'/\-.*?\-/', '', content, flags=re.S)
    content = re.sub(r'--[^\n]*', '', content)
    if re.search(r'\b(?:sorry|admit|axiom)\b', content):
        parser.error('placeholder or added axiom')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error(f'missing or duplicate theorem {name}')
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for file, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = file.read_text(encoding='utf-8').splitlines()
        for entry in wanted:
            if lines.count(entry) != 1:
                parser.error(f'missing or duplicate {entry} in {file}')
    print(f'PASS: two-scale physical fifth absorption ({len(THEOREMS)} theorems)')

if __name__ == '__main__':
    main()
