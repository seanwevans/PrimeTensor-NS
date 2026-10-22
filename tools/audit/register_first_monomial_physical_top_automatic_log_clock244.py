#!/usr/bin/env python3
"""Register automatic signed-log integrability and physical integrated cubic clock."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopAutomaticLogClock244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3_scalar_signedRate_intervalIntegrable_of_upperDerivative244',
    'h3Path_topSignedLog_intervalIntegrable_automatic244',
    'h3Path_topFifthPhaseJoint_intervalIntegrable_automatic244',
    'h3Path_topJointAction_eq_cubic_sub_log_automatic244',
    'h3Path_topLogGrowth_le_integratedActualCubicClock244',
    'h3Path_unboundedTopLog_forces_unboundedCubicAction244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
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
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} automatic top-log/cubic action declarations')

if __name__ == '__main__':
    main()
