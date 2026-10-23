#!/usr/bin/env python3
"""Register weak-FTC Grönwall selected-physical eighth-moment transfer."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopWeakFTCSelectedUniqueness244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_selectedPhysicalOverlap_of_weakFTCSlab244', 'h3Path_velocityRawEightMoments_of_weakFTCSlab244', 'h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_weakFTCSlabCoverage244', 'h3Path_weakFTCSlab_of_geometricSlab_and_globalWeakFTC244', 'h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_geometricSlabs_and_globalWeakFTC244', 'h3Path_selectedPhysicalOverlap_of_geometricSlab_and_globalOldPressure244', 'h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_geometricSlabs_and_globalOldPressure244')
DEFS = ('h3PathVelocityGeometricSlabCoveredAt244', 'h3PathVelocityWeakFTCSlabCoveredAt244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Proof placeholder found')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFS:
        if not re.search(r'^def\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    rest = [l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in rest:
                rest.append(command)
    result = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if result != original:
        AUDIT.write_text(result)
    print(f'Registered {len(DEFS)} definitions and {len(THEOREMS)} theorems')

if __name__ == '__main__':
    main()
