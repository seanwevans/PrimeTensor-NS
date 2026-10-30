#!/usr/bin/env python3
"""Register actual spectral-energy gate on all-orders critical H3 canonical witnesses."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetSpectralEnergyGate244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_higherBudget_energyFourth_to_spectralFourth244',
    'h3Path_scalar_higherSharpEnergyCost_forces_energyEscape244',
    'h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing {path}')
    src = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', src, re.M):
        raise SystemExit('Proof placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    current = ROOT.read_text().splitlines()
    if imp not in current:
        ROOT.write_text('\n'.join(current + [imp]) + '\n')
    prev = AUDIT.read_text()
    lines = prev.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        fully = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fully, '#print axioms ' + fully):
            if cmd not in body:
                body.append(cmd)
    changed = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if changed != prev:
        AUDIT.write_text(changed)
    print(f'Registered {len(THEOREMS)} spectral-energy gate theorems')

if __name__ == '__main__':
    main()
