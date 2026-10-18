#!/usr/bin/env python3
"""Register the strict local Fourier sign and polynomial Leray germ for full H3 transport."""
from pathlib import Path

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdHermitianLocalTube244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdTriadAxisDot_continuous_of_continuous244',
    'thirdFullPhysicalOrderedSymbol_continuous244',
    'thirdFullPhysicalSixSymbol_continuous244',
    'thirdFullMiddleFrequency244',
    'thirdFullMiddleFrequency_continuous244',
    'thirdFullHermitianMomentumKernel244',
    'thirdFullHermitianMomentumKernel_eq244',
    'thirdFullHermitianMomentumKernel_continuous244',
    'thirdFullHermitianMomentumKernel_at_conserving_triad244',
    'thirdFullHermitianMomentumKernel_exists_negative_center244',
    'thirdFullHermitianMomentumKernel_eventually_negative244',
    'thirdFullHermitianMomentumKernel_exists_negative_closedBall244',
    'thirdFullHermitianMomentumKernel_exists_negative_tube244',
    'thirdFullHermitianMomentumKernel_exists_negative_local_integral244',
    'thirdFullTransversePolynomial244',
    'thirdFullTransversePolynomial_solenoidal244',
    'thirdFullTransversePolynomial_at_transverse244',
    'thirdFullTransversePolynomial_continuous244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    for name in NAMES:
        if f'def {name}' not in src and f'theorem {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = f'import {MODULE}'
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([ln for ln in audit_lines if ln.startswith('import ')] + [imp]))
    body = [ln for ln in audit_lines if not ln.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        ref = 'PrimeTensor.FirstMonomialTriad.' + name
        for stmt in (f'#check {ref}', f'#print axioms {ref}'):
            if stmt not in body:
                body.append(stmt)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != AUDIT.read_text():
        AUDIT.write_text(result)
    print('Registered full-third Hermitian strict local sign and polynomial solenoidal germ')

if __name__ == '__main__':
    main()
