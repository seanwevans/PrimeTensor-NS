#!/usr/bin/env python3
"""Register spatially persistent actual physical H3 gradient spikes."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetActualGradientSpatialOpenBall244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_actualVelocityGradient_spatialContinuous244',
    'h3Path_actualGradientSpike_persistsOnSpatialBall244',
    'h3Path_noL2Trace_exactAnchor_higherBudget_actualGradientSpatialOpenBall244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproved placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    existing = AUDIT.read_text()
    lines = existing.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        fullname = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fullname, '#print axioms ' + fullname):
            if command not in rest:
                rest.append(command)
    result = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if result != existing:
        AUDIT.write_text(result)
    print(f'Registered {len(THEOREMS)} actual spatial gradient open-ball theorems')

if __name__ == '__main__':
    main()
