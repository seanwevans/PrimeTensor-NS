#!/usr/bin/env python3
"""Register the exact 21-term ordered full-third-commutator triad symbol."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdOrderedTriadSymbol244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('noncomputable def', 'thirdTriadAxisDot244'),
    ('noncomputable def', 'thirdTriadThreefold244'),
    ('theorem', 'thirdTriadThreefold_eq_prod244'),
    ('noncomputable def', 'thirdGradientOrderedTriadOrders244'),
    ('noncomputable def', 'thirdInterpolationOrderedTriadOrders244'),
    ('theorem', 'thirdGradientOrderedTriadOrders_eq244'),
    ('theorem', 'thirdInterpolationOrderedTriadOrders_eq244'),
    ('noncomputable def', 'thirdFullOrderedTriadRealSymbol244'),
    ('theorem', 'thirdFullOrderedTriadRealSymbol_eq244'),
    ('theorem', 'thirdOrderedTriadQuadratic_nonneg244'),
    ('theorem', 'thirdOrderedTriadQuadratic_pos_of_second_ne_zero244'),
    ('theorem', 'thirdOrderedTriadQuadratic_pos_of_nonzero244'),
    ('theorem', 'thirdOrderedSolenoidalTriad_coordinates244'),
    ('theorem', 'thirdOrderedSolenoidalTriad_nonzero_symbol244'),
)

def main():
    for f in (SOURCE, ROOT, AUDIT):
        if not f.is_file():
            raise SystemExit(f'Missing required file: {f}')
    source = SOURCE.read_text()
    for head, name in DECLS:
        if f'{head} {name}' not in source:
            raise SystemExit(f'Missing {head} {name}')
    line = f'import {MODULE}'
    root_lines = ROOT.read_text().splitlines()
    if line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [line]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [v for v in audit_lines if v.startswith('import ')] + [line]
    ))
    body = [v for v in audit_lines if not v.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for statement in (f'#check {full}', f'#print axioms {full}'):
            if statement not in body:
                body.append(statement)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered exact ordered third-commutator derivative symbol')

if __name__ == '__main__':
    main()
