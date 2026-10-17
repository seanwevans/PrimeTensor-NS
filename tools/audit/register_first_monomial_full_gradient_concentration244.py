#!/usr/bin/env python3
"""Idempotently register the physical Schwartz gradient/concentration frontier."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzFullGradientConcentration244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'fullGradientTriple244',
    'fullGradientTriple_dilation244',
    'fullGradientTriple_real_smul244',
    'fullSchwartzGradientAxis244',
    'fullSchwartzGradientAxis_dilation244',
    'fullSchwartzGradientAxis_real_smul244',
    'fullSchwartzGradientTransport244',
    'fullSchwartzGradientTransport_dilation244',
    'fullSchwartzGradientTransport_real_smul244',
    'fullSchwartzThirdCommutator244',
    'fullSchwartzThirdCommutator_dilation244',
    'fullSchwartzThirdCommutator_real_smul244',
    'fixedKineticSchwartzConcentration_gradient_eq244',
    'fixedKineticSchwartzConcentration_fullThird_eq244',
    'fullSchwartzThirdCommutator_oriented_positive244',
    'fixedKineticSchwartzConcentration_exceeds_fullThird_absorption244',
    'fullSchwartzThirdCommutator_nonzero_forces_static_obstruction244',
)

def main():
    for file in (SOURCE, ROOT, AUDIT):
        if not file.is_file():
            raise SystemExit(f'Missing required file: {file}')
    text = SOURCE.read_text()
    for decl in DECLS:
        if not any(f'{head} {decl}' in text for head in ('theorem', 'noncomputable def')):
            raise SystemExit(f'Missing declaration {decl}')
    import_line = f'import {MODULE}'
    root_lines = ROOT.read_text().splitlines()
    if import_line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [import_line]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [x for x in audit_lines if x.startswith('import ')] + [import_line]
    ))
    body = [x for x in audit_lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for decl in DECLS:
        full = 'PrimeTensor.FirstMonomialTriad.' + decl
        for cmd in (f'#check {full}', f'#print axioms {full}'):
            if cmd not in body:
                body.append(cmd)
    final = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != final:
        AUDIT.write_text(final)
    print('Registered full third-order gradient concentration frontier')

if __name__ == '__main__':
    main()
