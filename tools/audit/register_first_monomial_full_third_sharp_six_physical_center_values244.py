#!/usr/bin/env python3
"""Idempotently register the six genuine full-third physical sharp coefficients."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSharpSixPhysicalCenterValues244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
  'thirdFullSharpPhysicalOrderedAt244',
  'thirdFullSharpPhysicalOrderedAt_twice_corrected244',
  'thirdFullSharpPhysicalSixOrdered_values244',
  'thirdFullSharpPhysicalSixOrdered_sum_neg192244',
  'thirdFullPositiveSectorPhysicalCore_sharpPair_eq_orderedAt244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Disallowed proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in source and f'def {name}' not in source:
            raise SystemExit(f'Missing audit declaration: {name}')
    imp = 'import ' + MODULE
    current = ROOT.read_text().splitlines()
    if imp not in current:
        ROOT.write_text('\n'.join(current + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {q}', f'#print axioms {q}'):
            if check not in body:
                body.append(check)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered six actual five-index sharp physical coefficients')

if __name__ == '__main__':
    main()
