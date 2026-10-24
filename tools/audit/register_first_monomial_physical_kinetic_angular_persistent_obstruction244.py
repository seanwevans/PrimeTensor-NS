#!/usr/bin/env python3
"""Register physical Gram angular cofinal obstruction and zero-mass alternative."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularPersistentObstruction244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('H3PhysicalAngularGramCofinalBursts244',)
THEOREMS = (
    'h3Path_physicalAngularGramTailVanishing_of_noCofinalBursts244',
    'h3Path_physicalAngularGram_cofinalBursts_of_noUnitTrace244',
    'h3Path_physicalAngularGram_cofinalBursts_of_noVelocityTrace244',
    'h3Path_physicalAngularGram_cofinalUnitSpeedAction_of_noVelocityTrace244',
    'h3Path_physicalAngularGram_arbitrarilyShortBursts_of_cofinal244',
    'h3Path_physicalAngularGram_arbitrarilyShortBursts_of_noVelocityTrace244',
    'h3Path_physicalAngularGram_exactMassTrace_or_cofinalBursts244',
    'h3Path_physicalAngularGram_allKineticTrace_or_cofinalBursts244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Proof placeholder or axiom found')
    for name in DEFS:
        if not re.search(r'^def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    rest = [x for x in lines if not x.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + qualified, '#print axioms ' + qualified):
            if cmd not in rest:
                rest.append(cmd)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(DEFS)} definition and {len(THEOREMS)} theorems.')

if __name__ == '__main__':
    main()
