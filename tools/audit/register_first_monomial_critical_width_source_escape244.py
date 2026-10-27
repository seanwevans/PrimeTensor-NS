#!/usr/bin/env python3
"""Register critical annular width versus physical projected-source escape."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalWidthSourceEscape244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_criticalWidthCap_boundsOuter244', 'h3Path_criticalWidth_or_projectedSourceLarge244', 'h3Path_criticalWidthCap_forces_sourceSquareEscape244', 'h3Path_noL2Trace_finiteDissipation_widthCap_sourceSquareEscape244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    src = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', src, re.M):
        raise SystemExit('Unproved placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip(): rest.pop(0)
    for name in THEOREMS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in rest: rest.append(command)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != old: AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} critical width/source escape theorems')

if __name__ == '__main__': main()
