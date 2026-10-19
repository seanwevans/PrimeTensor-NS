#!/usr/bin/env python3
"""Register the exact physical six-sector to projected Hermitian orbit bridge."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPositiveSectorHermitianBridge244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPositiveTransportedCorrected_eq_singlePhysicalSix244',
    'thirdFullPositivePhysicalSixTransportedCore_eq_projectedHermitian244',
    'thirdFullPositivePhysicalSixPolynomials_eq_window_hermitian244',
    'thirdFullPositivePhysicalSixPolynomialIntegrals_hermitian244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for item in (f'#check {q}', f'#print axioms {q}'):
            if item not in body:
                body.append(item)
    update = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if update != original:
        AUDIT.write_text(update)
    print('Registered projected Hermitian six-sector bridge')

if __name__ == '__main__':
    main()
