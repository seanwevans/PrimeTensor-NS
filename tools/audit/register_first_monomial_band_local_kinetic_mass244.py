#!/usr/bin/env python3
"""Register exact physical annulus/raw Fourier kinetic mass transfer."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKinetic'
          'ProjectedSourceSpectralFiniteAnnulusPDEBandLocalKineticMass244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_actualAnnularDissipation_eq_bandIntegral244',
    'h3Path_actualBandDissipation_le_bandRawKinetic244',
    'h3Path_actualAnnularDissipation_le_bandRawKinetic244',
    'h3Path_firstCrossing_forces_bandKineticMass244',
    'h3Path_noL2Trace_minimalFirstCrossing_bandKineticCost244',
)
DEFINITIONS = ('h3PathActualBandRawKineticMass244',)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', src, re.M):
        raise SystemExit('Unexpected unproven placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFINITIONS:
        if not re.search(r'^\s*noncomputable def\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS + DEFINITIONS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} band-local kinetic theorems and {len(DEFINITIONS)} definition.')

if __name__ == '__main__':
    main()
