#!/usr/bin/env python3
"""Register an actual fixed-kinetic solenoidal Schwartz absorption obstruction."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FixedKineticConcentrationBarrier244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'fixedKineticSchwartzConcentration244',
    'fixedKineticSchwartzConcentration_solenoidal244',
    'fixedKineticSchwartzConcentration_energy0_eq244',
    'fixedKineticSchwartzConcentration_energy1_eq244',
    'fixedKineticSchwartzConcentration_monomial_eq244',
    'fixedKineticSchwartzConcentration_dissipation_eq244',
    'fixedKineticSchwartzConcentration_exceeds_absorption244',
    'lowNormalQuarterOppositeSchwartz_Point3Solenoidal244',
    'lowNormalQuarter_exists_fixedKinetic_absorption_counterexample244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    content = SOURCE.read_text()
    for name in DECLS:
        if name not in content:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in body:
                body.append(command)
    output = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != output:
        AUDIT.write_text(output)
    print('Registered fixed-kinetic concentration obstruction')

if __name__ == '__main__':
    main()
