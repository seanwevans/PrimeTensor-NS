#!/usr/bin/env python3
"""Idempotently register the exact moving-germ physical six-orbit proofs."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalVariableSixOrbit244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPositiveSectorPhysicalCore_eq_sharp_form_variable244',
    'thirdFullPositiveSectorPhysicalCore_eq_twice_corrected_variable244',
    'thirdFullSharpProjectedPhysicalSixOrbit244',
    'thirdFullSharpProjectedPhysicalSixOrbit_eq_hermitian244',
    'thirdFullSharpProjectedPhysicalSixOrbit_continuous244',
    'thirdFullSharpProjectedPhysicalSixOrbit_exists_negative_tube244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Disallowed proof placeholder in Lean source')
    for name in NAMES:
        if f'theorem {name}' not in source and f'def {name}' not in source:
            raise SystemExit(f'Missing audited declaration: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {qualified}', f'#print axioms {qualified}'):
            if check not in body:
                body.append(check)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered variable full-third physical six-orbit kernel')


if __name__ == '__main__':
    main()
