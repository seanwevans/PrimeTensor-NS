#!/usr/bin/env python3
"""Register the same-anchor higher-order spacetime-budget PDE clock rate barrier."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetPDERates244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_scalar_higherRadialLinearCap_forces_rate244', 'h3Path_scalar_higherRadialQuadraticCap_forces_rate244', 'h3Path_scalar_higherBudget_exactPDE_threeScale244', 'h3Path_noL2Trace_exactAnchor_higherBudget_forces_physicalPDERates244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    body = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', body, re.M):
        raise SystemExit('Unproved placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', body, re.M):
            raise SystemExit('Missing theorem: '+name)
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    tail = [x for x in lines if not x.startswith('import ')]
    while tail and not tail[0].strip():
        tail.pop(0)
    for name in THEOREMS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + full, '#print axioms ' + full):
            if cmd not in tail:
                tail.append(cmd)
    new = '\n'.join(imports + [''] + tail).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} higher-budget exact PDE clock rate declarations')

if __name__ == '__main__':
    main()
