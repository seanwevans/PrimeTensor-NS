#!/usr/bin/env python3
"""Register the weighted H3 canonical 108-jet cross-energy continuity bridge."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3WeightedCanonicalCrossEnergy244')
SRC = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'weightedH3CanonicalCrossSecondJetEnergy244',
    'weightedH3CanonicalCrossThirdJetEnergy244',
    'weightedH3CanonicalCrossJetEnergy244',
    'weightedH3CanonicalCrossSecondJetEnergy_nonneg244',
    'weightedH3CanonicalCrossThirdJetEnergy_nonneg244',
    'weightedH3CanonicalCrossJetEnergy_nonneg244',
    'continuous_weightedH3CanonicalCrossSecondJetEnergy244',
    'continuous_weightedH3CanonicalCrossThirdJetEnergy244',
    'continuous_weightedH3CanonicalCrossJetEnergy244',
    'weightedH3CanonicalCrossSecondJetEnergy_self244',
    'weightedH3CanonicalCrossThirdJetEnergy_self244',
    'weightedH3CanonicalCrossJetEnergy_self244',
    'weightedH3MatchedSchwartzCompletion_crossSecondEnergy_tendsto244',
    'weightedH3MatchedSchwartzCompletion_crossThirdEnergy_tendsto244',
    'weightedH3MatchedSchwartzCompletion_crossEnergies_tendsto244',
    'weightedH3CanonicalCrossJetEnergy_tendsto_zero_of_tendsto244',
)

def main():
    for f in (SRC, ROOT, AUDIT):
        if not f.is_file():
            raise SystemExit(f'Missing required file: {f}')
    source = SRC.read_text()
    for decl in DECLS:
        if not any(f'{kind} {decl}' in source for kind in ('theorem', 'def')):
            raise SystemExit(f'Declaration not found: {decl}')
    line = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if line not in root:
        ROOT.write_text('\n'.join(root + [line]) + '\n')
    audit = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([l for l in audit if l.startswith('import ')] + [line]))
    rest = [l for l in audit if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for decl in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + decl
        for check in ('#check ' + qualified, '#print axioms ' + qualified):
            if check not in rest:
                rest.append(check)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered canonical H3 two-state Schwartz cross energies')

if __name__ == '__main__':
    main()
