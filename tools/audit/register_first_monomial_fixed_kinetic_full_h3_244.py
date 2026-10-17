#!/usr/bin/env python3
"""Idempotently register fixed-kinetic full H3 transport obstruction proofs."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FixedKineticFullH3Obstruction244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'fixedKinetic_secondEnergy_real_smul244',
    'fixedKinetic_thirdEnergy_real_smul244',
    'fixedKineticSchwartzConcentration_energy2_eq244',
    'fixedKineticSchwartzConcentration_energy3_eq244',
    'fixedKineticSchwartzConcentration_fullEnergy_eq244',
    'fixedKineticSchwartzConcentration_exceeds_fullH3_absorption244',
    'lowNormalQuarter_exists_fixedKinetic_fullH3_absorption_counterexample244',
    'lowNormalQuarter_fixedKinetic_forces_gradient_compensation244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing expected file: {path}')
    source = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem: {name}')
    import_line = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if import_line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [import_line]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in audit_lines if line.startswith('import ')] + [import_line]
    ))
    body = [line for line in audit_lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in body:
                body.append(cmd)
    next_content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != next_content:
        AUDIT.write_text(next_content)
    print('Registered fixed-kinetic full H3 concentration barrier')

if __name__ == '__main__':
    main()
