#!/usr/bin/env python3
"""Idempotently register the exact Schwartz difference-energy Sobolev bridge."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzDifferenceEnergyBridge244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('theorem', 'schwartzLineDeriv_sub244'),
    ('theorem', 'schwartzTwoLineDerivs_sub244'),
    ('theorem', 'schwartzThreeLineDerivs_sub244'),
    ('def', 'schwartzVelocityDifference244'),
    ('theorem', 'schwartzThirdJetDifference_squareMass_eq_energy3244'),
    ('theorem', 'schwartzSecondJetDifference_quarticMass_eq244'),
    ('theorem', 'schwartzSecondJetDifference_quarticGN_energy244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered exact Schwartz jet difference E3/Q4 identities and quartic GN transfer')

if __name__ == '__main__':
    main()
