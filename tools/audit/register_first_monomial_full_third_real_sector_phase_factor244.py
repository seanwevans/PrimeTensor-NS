#!/usr/bin/env python3
"""Idempotently audit the physical coherent-sector cubic Fourier phase."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorPhaseFactor244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullThreeWindowFactors_phase244',
    'thirdFullThreeWindowFactors_imag244',
    'thirdFullPositiveSectorRealTripleFactor244',
    'thirdFullPositiveSector_actual_triple_eq_real_mul_I244',
    'thirdFullPositiveSector_actual_triple_imag244',
    'thirdFullPositiveSector_actual_triple_re_zero244',
    'thirdFullPositiveSector_actual_interpolation244',
    'thirdFullPositiveSector_gradient_slot_phase244',
    'thirdFullGradientSevenWeight_im_zero244',
    'thirdFullPositiveSector_gradient_slot_imag244',
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    s = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in s and f'def {name}' not in s:
            raise SystemExit(f'Missing audited declaration: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    body = [l for l in lines if not l.startswith('import ')]
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
    print('Registered actual full-third six-sector cubic phase and interpolation audit')


if __name__ == '__main__':
    main()
