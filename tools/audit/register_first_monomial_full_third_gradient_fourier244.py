#!/usr/bin/env python3
"""Register actual 3+3+1 seven-derivative Fourier bridge and audit checks."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGradientFourierBridge244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'thirdGradientSchwartzKernel244',
    'thirdGradientSchwartzKernel_integrable244',
    'thirdGradientSchwartz_integral_eq_triad244',
    'thirdGradientSchwartzAxisComplex244',
    'thirdGradientSchwartzAxisFourier244',
    'thirdGradientSchwartzAxisComplex_eq_fourier244',
    'thirdGradientSchwartzTotalComplex244',
    'thirdGradientFourierTotalComplex244',
    'thirdGradientSchwartzTotalComplex_eq_fourier244',
)


def main():
    for f in (SOURCE, ROOT, AUDIT):
        if not f.is_file():
            raise SystemExit(f'Missing: {f}')
    source = SOURCE.read_text()
    for name in DECLS:
        if not any(f'{prefix} {name}' in source for prefix in ('def', 'noncomputable def', 'theorem')):
            raise SystemExit(f'Missing declaration: {name}')
    stmt = f'import {MODULE}'
    root_lines = ROOT.read_text().splitlines()
    if stmt not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [stmt]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in audit_lines if line.startswith('import ')] + [stmt]))
    body = [line for line in audit_lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qualified = f'PrimeTensor.FirstMonomialTriad.{name}'
        for statement in (f'#check {qualified}', f'#print axioms {qualified}'):
            if statement not in body:
                body.append(statement)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print('Registered actual full-gradient 3+3+1 Fourier transform bridge')

if __name__ == '__main__':
    main()
