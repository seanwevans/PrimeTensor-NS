#!/usr/bin/env python3
"""Register the real Schwartz / canonical path H3 energy equalities."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPathEnergyIdentification244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'lowNormalRealSchwartz_pathEnergy0_eq',
    'lowNormalRealSchwartz_pathEnergy1_eq',
    'lowNormalRealSchwartz_pathEnergy2_eq',
    'lowNormalRealSchwartz_pathEnergy3_eq',
    'lowNormalRealSchwartz_pathTopDissipation_eq',
    'schwartzPath_topDissipation_le_full',
    'lowNormalRealSchwartz_pathEnergy_eq',
    'lowNormalRealSchwartz_pathThirdTransport_physicalEnergies244',
)

def main():
    for file in (SOURCE, ROOT, AUDIT):
        if not file.is_file():
            raise SystemExit(f'Missing required file: {file}')
    code = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in code:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in old if s.startswith('import ')] + [imp]))
    body = [s for s in old if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for line in (f'#check {fq}', f'#print axioms {fq}'):
            if line not in body:
                body.append(line)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != AUDIT.read_text():
        AUDIT.write_text(new)
    print('Registered physical H3 energies for Schwartz-realized path slices')

if __name__ == '__main__':
    main()
