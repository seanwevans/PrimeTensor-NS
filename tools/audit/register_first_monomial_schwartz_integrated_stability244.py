#!/usr/bin/env python3
"""Idempotently register genuine integrated real 2-4-4 Schwartz stability."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzIntegratedStability244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'schwartzIntegralL2Root244',
    'schwartzIntegralL4Root244',
    'schwartzTripleIntegral244',
    'schwartzTripleIntegral_abs_le_roots244',
    'schwartzTripleIntegral_telescoping244',
    'schwartzTripleIntegral_difference_le244',
    'schwartzPhysicalSlotPerturbation244',
    'lowNormalRealSchwartz_fullMonomial_integratedStability244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src and f'def {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    import_line = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if import_line not in lines:
        ROOT.write_text('\n'.join(lines + [import_line]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([l for l in audit_lines if l.startswith('import ')] + [import_line]))
    body = [l for l in audit_lines if not l.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered actual 243-slot integrated Schwartz L2-L4-L4 stability')

if __name__ == '__main__':
    main()
