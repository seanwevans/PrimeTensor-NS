#!/usr/bin/env python3
"""Register physical kinetic logarithmic action and signed top phase budget."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalIntegratedKineticLogPhaseBudget244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathPhysicalKineticLogLossRate244',
    'h3PathPhysicalKineticLogLossPrimitive244',
    'h3PathPhysicalIntegratedTopPhaseProfile244',
)
THEOREMS = (
    'h3Path_physicalKinetic_derivative_eq_diffusion0_244',
    'h3Path_physicalKineticLogLoss_hasDerivAt244',
    'h3Path_physicalKineticLogLoss_integral_eq_endpoint244',
    'h3Path_physicalVariance_deriv_eq_neg_middleTopPhase244',
    'h3Path_physicalVariance_integral_middleTopPhase_eq_drop244',
    'h3Path_physicalMiddle_le_kineticLog_gradient244',
    'h3Path_physicalMiddle_integral_le_kineticLog_gradient244',
    'h3Path_physicalTopPhase_integral_ge_after_kineticLog_gradient244',
    'h3Path_nearYoung_forces_integratedTopPhase_after_kineticLog244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for name in DEFS:
        if not re.search(r'^noncomputable def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print(f'Registered {len(DEFS) + len(THEOREMS)} kinetic-log and signed-phase declarations')

if __name__ == '__main__':
    main()
