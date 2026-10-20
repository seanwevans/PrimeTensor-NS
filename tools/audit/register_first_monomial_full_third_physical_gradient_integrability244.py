#!/usr/bin/env python3
"""Register the physical H3 gradient L2-L2-Linfty integrability frontier."""
from pathlib import Path
import re

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientIntegrability244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3ActualPhysicalGradientThirdJet_memLp_two244',
    'h3ActualPhysicalGradientFirstJet_bound244',
    'h3ActualPhysicalGradientFirstJet_memLp_top244',
    'h3ActualPhysicalGradientTriple_integrable244',
    'h3ActualPhysicalGradientAxesIntegrable244',
    'h3PhysicalFullThird_discrepancy_eq_gradientOnly244',
    'h3PhysicalFullThird_eq_canonical_iff_gradient_eq244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', source):
        raise SystemExit('Proof placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    statement = 'import ' + MODULE
    root_old = ROOT.read_text()
    if statement not in root_old.splitlines():
        ROOT.write_text(root_old.rstrip() + '\n' + statement + '\n')
    audit_old = AUDIT.read_text()
    lines = audit_old.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [statement]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for decl in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + decl
        for line in ('#check ' + qualified, '#print axioms ' + qualified):
            if line not in body:
                body.append(line)
    revised = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if revised != audit_old:
        AUDIT.write_text(revised)
    print('Registered physical gradient L2-L2-Linfty bridge and signed-gap reduction')


if __name__ == '__main__':
    main()
