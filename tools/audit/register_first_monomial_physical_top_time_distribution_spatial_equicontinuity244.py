#!/usr/bin/env python3
"""Register spatial equicontinuity to physical time-distribution results."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionSpatialEquicontinuity244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_compactUniformTimeOscillation_of_spatialLipschitz244',
    'h3Preterminal_signedPhysicalMomentum_continuousAt_time244',
    'h3Preterminal_signedOscillation_of_localSpatialLipschitz244',
    'h3Path_interiorSignedOscillation_of_spatialLipschitz244',
    'h3Path_distributionalMomentum_of_spatialLipschitz244',
    'h3Path_nonzeroPhysicalFTCDefect_forces_spatialLipschitzFailure244',
)
DEFS = (
    'h3PreterminalSignedMomentumLocalSpatialLipschitzOnElapsed244',
    'h3PathInteriorTimeSignedSpatialLipschitzAt244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder found')
    for kind, names in (('theorem', THEOREMS), ('def', DEFS)):
        for name in names:
            if not re.search(r'^' + kind + r'\s+' + re.escape(name) + r'\b', source, re.M):
                raise SystemExit(f'Missing {kind}: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS + DEFS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} theorems and {len(DEFS)} definitions.')

if __name__ == '__main__':
    main()
