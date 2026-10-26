#!/usr/bin/env python3
"""Register exact cubic-annulus physical-PDE clock witnesses and alternatives."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
          'SpectralFiniteAnnulusPDEExactClockAlternative244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('h3PathCubicAnnulusExactPDEWidth244',)
THEOREMS = (
    'h3Path_cubicAnnulusExactPDEWidth_valid244',
    'h3Path_cubicAnnulusExactPDEWidth_costTrichotomy244',
    'h3Path_cubicHighSnapshot_has_exactPDEClock244',
    'h3Path_noL2Trace_forces_cubicExactPDEClocks244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproven placeholder or axiom found')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFS:
        if not re.search(r'^\s*(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(DEFS)} exact-clock definition and {len(THEOREMS)} theorems.')

if __name__ == '__main__':
    main()
