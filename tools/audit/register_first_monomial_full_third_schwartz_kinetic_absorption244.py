#!/usr/bin/env python3
"""Register the actual Schwartz kinetic-absorption top-cubic frontier."""
from pathlib import Path
import re

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzKineticAbsorption244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_realSchwartz_anchorKineticAbsorbedBalance244',
    'h3Path_realSchwartz_anchoredHighGrowthForcesTopAdversity244',
    'h3Path_realSchwartz_topDissipationGrowthCorridor244',
    'h3Path_realSchwartz_topEnergy_pos_of_signedAdversity244',
    'h3Path_noExtension_realSchwartzTopAdverse_onEverySubtail244',
    'h3Path_noExtension_realSchwartzTopFrequencyCorridor244',
    'h3Path_extension_of_realSchwartzTopSpectralDominance244',
    'h3Path_extension_of_realSchwartzTopCubicEnvelope244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', src):
        raise SystemExit('Forbidden placeholder in proof source')
    actual = set(re.findall(r'^theorem\s+(\w+)', src, re.M))
    missing = set(THEOREMS) - actual
    if missing:
        raise SystemExit('Missing declarations: '+', '.join(sorted(missing)))
    imp = 'import ' + MODULE
    rlines = ROOT.read_text().splitlines()
    if imp not in rlines:
        ROOT.write_text('\n'.join(rlines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [imp]
    ))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {full}', f'#print axioms {full}'):
            if check not in body:
                body.append(check)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} kinetic-absorption Schwartz theorems')

if __name__ == '__main__':
    main()
