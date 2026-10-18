#!/usr/bin/env python3
"""Register the genuine frequency-dependent transverse full-third Hermitian germ."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdProjectedHermitianGerm244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisDot_mul_right244',
    'thirdFullAxisDot_mul_left244',
    'thirdFullPhysicalOrderedSymbol_pol_scaling244',
    'thirdFullAxisDot_comm244',
    'thirdFullPhysicalSixSymbol_pol_scaling244',
    'thirdFullFixedCenterTransverseGerm244',
    'thirdFullFixedCenterTransverseGerm_solenoidal244',
    'thirdFullFixedCenterTransverseGerm_at_center244',
    'thirdFullFixedCenterTransverseGerm_continuous244',
    'thirdFullProjectedHermitianKernel244',
    'thirdFullProjectedHermitianKernel_transverse244',
    'thirdFullProjectedHermitianKernel_continuous244',
    'thirdFullProjectedHermitianKernel_at_center244',
    'thirdFullProjectedHermitianKernel_exists_negative_closedBall244',
    'thirdFullWindowedProjectedHermitianKernel244',
    'thirdFullWindowedProjectedHermitianKernel_factor244',
    'thirdFullWindowedProjectedHermitianKernel_negative244',
    'thirdFullWindowedProjectedHermitianKernel_zero_of_first_window244',
    'thirdFullProjectedHermitianKernel_exists_solenoidal_negative_tube244',
    'thirdFullProjectedHermitianKernel_exists_negative_local_integral244',
)

def main():
    for f in (SOURCE, ROOT, AUDIT):
        if not f.is_file():
            raise SystemExit(f'Missing required file: {f}')
    source = SOURCE.read_text()
    for name in NAMES:
        if not any(f'{head} {name}' in source for head in ('theorem', 'noncomputable def', 'def')):
            raise SystemExit(f'Missing declaration: {name}')
    import_line = f'import {MODULE}'
    root = ROOT.read_text().splitlines()
    if import_line not in root:
        ROOT.write_text('\n'.join(root + [import_line]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in old if line.startswith('import ')] + [import_line]
    ))
    body = [line for line in old if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        fullname = 'PrimeTensor.FirstMonomialTriad.' + name
        for stmt in (f'#check {fullname}', f'#print axioms {fullname}'):
            if stmt not in body:
                body.append(stmt)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != AUDIT.read_text():
        AUDIT.write_text(result)
    print('Registered full-third projected Hermitian germ, solenoidality, sign, and local integral')

if __name__ == '__main__':
    main()
