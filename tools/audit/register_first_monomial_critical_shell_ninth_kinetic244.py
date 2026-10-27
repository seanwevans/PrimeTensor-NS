#!/usr/bin/env python3
"""Register the critical ninth/eighth physical kinetic shell alternatives."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalShellNinthKinetic244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_widthShell_ninthEighth_or_sixthMass244', 'h3Path_widthShell_sixthMassVanishing_ninthEighthEscape244', 'h3Path_noL2Trace_finiteDissipation_ninthEighthEnergeticShell244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    src = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)',src,re.M):
        raise SystemExit('Unproved placeholder/axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+'+re.escape(name)+r'\b',src,re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp='import '+MODULE
    root_lines=ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines+[imp])+'\n')
    old=AUDIT.read_text()
    lines=old.splitlines()
    imports=list(dict.fromkeys([l for l in lines if l.startswith('import ')]+[imp]))
    rest=[l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        q='PrimeTensor.FirstMonomialTriad.'+name
        for cmd in ('#check '+q, '#print axioms '+q):
            if cmd not in rest: rest.append(cmd)
    new='\n'.join(imports+['']+rest).rstrip()+'\n'
    if new != old: AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} critical kinetic-shell theorems')
if __name__ == '__main__': main()
