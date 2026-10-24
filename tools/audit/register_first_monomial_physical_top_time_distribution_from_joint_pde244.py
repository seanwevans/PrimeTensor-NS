#!/usr/bin/env python3
"""Register classical-PDE joint-temporal-continuity to time-distribution bridge."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionFromJointPDE244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_distributionalMomentum_of_oldTemporalDerivativeJointlyContinuous244',
    'h3Path_timeTestMomentum_of_oldTemporalDerivativeJointlyContinuous244',
    'h3Path_solenoidalWeakFTC_of_oldTemporalDerivativeJointlyContinuous244',
    'h3Path_nonzeroPhysicalFTCDefect_forces_oldJointFailure244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder found')
    for theorem in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(theorem) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {theorem}')
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
    for name in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} classical-PDE-to-distribution declarations.')

if __name__ == '__main__':
    main()
