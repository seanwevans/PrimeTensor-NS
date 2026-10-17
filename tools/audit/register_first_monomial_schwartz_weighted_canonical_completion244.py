#!/usr/bin/env python3
"""Register native weighted H3 canonical real signed 243-slot completion."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzWeightedCanonicalCompletion244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ENERGY = Path('PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/'
              'FirstMonomialTriadLowQuarterPoint3SchwartzMatchedEnergyCauchy244.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'WeightedH3MatchedSchwartzCompletion244',
    'exists_weightedH3MatchedSchwartzCompletion244',
    'weightedH3MatchedSchwartzCompletion_completed_eq244',
    'weightedH3CanonicalSchwartzWitness244',
    'weightedH3CanonicalSignedFirstMonomial244',
    'weightedH3CanonicalSignedFirstMonomial_eq_of_matched244',
    'weightedH3CanonicalSignedFirstMonomial_tendsto244',
    'weightedH3CanonicalSignedFirstMonomial_unique244',
)


def main():
    for p in (SOURCE, ENERGY, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    code = SOURCE.read_text()
    for name in DECLS:
        if name not in code:
            raise SystemExit(f'Missing declaration: {name}')
    assert 'theorem exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244' in ENERGY.read_text()
    module_import = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if module_import not in lines:
        ROOT.write_text('\n'.join(lines + [module_import]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in old if s.startswith('import ')] + [module_import]))
    body = [s for s in old if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    checks = ['exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244'] + list(DECLS)
    for name in checks:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + qualified, '#print axioms ' + qualified):
            if cmd not in body:
                body.append(cmd)
    merged = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != merged:
        AUDIT.write_text(merged)
    print('Registered canonical weighted H3 signed first-monomial completion')

if __name__ == '__main__':
    main()
