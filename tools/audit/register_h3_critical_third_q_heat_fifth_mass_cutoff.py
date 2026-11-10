#!/usr/bin/env python3
"""Register and audit the physical third-Q low-fifth/high-sixth cutoff step."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalThirdQHeatFifthMassCutoff'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullPhysicalCriticalThirdQHeatHighpass244',)
THEOREMS = (
    'thirdFullKinetic_fifthSixthLowBand_density_le244',
    'thirdFullPhysical_thirdQHeatLowSquare_le_fifthCoordinate244',
    'thirdFullPhysical_thirdQHeatLowSquare_le_fifthMass244',
    'thirdFullPhysical_thirdQHeatSquare_le_fifthPlusHigh244',
    'thirdFullPhysical_nearCriticalAnchor_forces_fifthTemporalHighSixth244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in DEFS + THEOREMS for line in
               ('#check ' + NS + name, '#print axioms ' + NS + name))

def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
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
    for p in (src, pt, audit):
        if not p.is_file():
            parser.error(f'missing file {p}')
    content = src.read_text(encoding='utf-8')
    content = re.sub(r'/-.*?-/', '', content, flags=re.S)
    content = re.sub(r'--[^\n]*', '', content)
    if re.search(r'\b(?:sorry|admit|axiom)\b', content):
        parser.error('placeholder proof or additional axiom')
    for kind, names in (('theorem', THEOREMS), ('noncomputable def', DEFS)):
        for name in names:
            if len(re.findall(r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b', content)) != 1:
                parser.error(f'missing/duplicate declaration: {name}')
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for p, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = p.read_text(encoding='utf-8').splitlines()
        for e in wanted:
            if lines.count(e) != 1:
                parser.error(f'missing/duplicate registry entry: {p}: {e}')
    print(f'PASS: third-Q physical low-fifth/high-sixth gate ({len(THEOREMS)} theorems)')

if __name__ == '__main__':
    main()
