#!/usr/bin/env python3
"""Register the high-energy corridor's synchronized spectral and physical dissipation clocks."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralHighEnergyRadialSynchronization244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_highEnergyRequest_forces_spectralThreshold244',
    'h3Path_highEnergyRequest_forces_jointRadialClock244',
    'h3Path_cofinalHighEnergy_forces_jointRadialSequence244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Unproven placeholder/axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*(?:noncomputable\s+)?theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp='import '+MODULE
    lines=ROOT.read_text().splitlines()
    if imp not in lines: ROOT.write_text('\n'.join(lines+[imp])+'\n')
    old=AUDIT.read_text()
    lines=old.splitlines()
    imports=list(dict.fromkeys([l for l in lines if l.startswith('import ')]+[imp]))
    rest=[l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip(): rest.pop(0)
    for name in THEOREMS:
        qualified='PrimeTensor.FirstMonomialTriad.'+name
        for command in ('#check '+qualified, '#print axioms '+qualified):
            if command not in rest: rest.append(command)
    new='\n'.join(imports+['']+rest).rstrip()+'\n'
    if new!=old: AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} high-energy/radial synchronization theorems.')

if __name__ == '__main__': main()
