#!/usr/bin/env python3
"""Register physical kinetic/L1/eighth-moment escape reductions."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopKineticL1EightMomentAlternative244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244',
    'h3Path_rawVelocityFourierConjL2_le_sqrtKineticAnchor244',
    'h3Path_velocityRawFourierL1MassComponent_eq244',
    'h3Path_unboundedPhysicalTop_forces_eightMoment_of_rawFourierL1Ceiling244',
    'h3Path_unboundedPhysicalTop_forces_rawL1_or_eightMomentEscape244',
    'h3Path_unboundedPhysicalTop_forces_eightMoment_of_spectralH3Ceiling244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required project file: {p}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Lean placeholder found')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in body:
                body.append(command)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if original != new:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} kinetic/L1/eighth-moment theorems')

if __name__ == '__main__':
    main()
