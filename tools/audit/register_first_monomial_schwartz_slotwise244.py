#!/usr/bin/env python3
"""Register 243-slot trilinear stability and physical approximation criterion."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSlotwiseStability244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'criticalHalf_trilinear_telescoping244',
    'criticalHalf_trilinear_abs_difference_le244',
    'criticalHalf_finite_trilinear_difference_le244',
    'H3SchwartzSlotwiseCriticalHalfApproximable244',
    'h3PathCanonical_slotwise_implies_approximable244',
    'h3PathCanonical_thirdTransport_criticalHalf_of_slotwise244',
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
    root_lines = ROOT.read_text().splitlines()
    if import_line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [import_line]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [import_line]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in body:
                body.append(command)
    update = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != update:
        AUDIT.write_text(update)
    print('Registered 243-slot Schwartz trilinear stability and approximation criteria')

if __name__ == '__main__':
    main()
