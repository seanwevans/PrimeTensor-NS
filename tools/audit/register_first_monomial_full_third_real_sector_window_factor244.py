#!/usr/bin/env python3
"""Register cutoff-free real physical sector polynomial identities."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorWindowFactor244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPositiveSectorBareGerm244',
    'thirdFullPositiveSectorWindowProduct244',
    'thirdFullPositiveSectorBareTriple244',
    'thirdFullPositiveSectorRealTripleFactor_window244',
    'thirdFullPositiveSectorGradientAxisCore244',
    'thirdFullPositiveSectorGradientAxis_window244',
    'thirdFullPositiveSectorGradientTotalCore244',
    'thirdFullPositiveSectorGradientTotal_window244',
    'thirdFullPositiveSectorInterpolationCore244',
    'thirdFullPositiveSectorInterpolation_window244',
    'thirdFullPositiveSectorPhysicalCore244',
    'thirdFullPositiveSectorPhysicalPolynomial_window244',
    'thirdFullPositiveSectorActualImag_window_core244',
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
    print('Registered exact common-window factor for all real full-third physical sectors')

if __name__ == '__main__':
    main()
