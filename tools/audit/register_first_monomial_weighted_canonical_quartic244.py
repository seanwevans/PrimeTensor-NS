#!/usr/bin/env python3
"""Register canonical weighted-H3 quartic continuity / zero-endpoint theorem."""
from pathlib import Path

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3WeightedCanonicalQuarticBound244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'weightedH3CanonicalSecondJetEnergy244'),
    ('def', 'weightedH3CanonicalThirdJetEnergy244'),
    ('theorem', 'continuous_weightedH3CanonicalSecondJetEnergy244'),
    ('theorem', 'continuous_weightedH3CanonicalThirdJetEnergy244'),
    ('theorem', 'weightedH3CanonicalSecondJetEnergy_nonneg244'),
    ('theorem', 'weightedH3CanonicalThirdJetEnergy_nonneg244'),
    ('theorem', 'weightedH3MatchedSchwartzCompletion_secondEnergy_eq244'),
    ('theorem', 'weightedH3MatchedSchwartzCompletion_thirdEnergy_eq244'),
    ('theorem', 'weightedH3MatchedSchwartzCompletion_secondEnergy_tendsto244'),
    ('theorem', 'weightedH3MatchedSchwartzCompletion_thirdEnergy_tendsto244'),
    ('theorem', 'weightedH3CanonicalSignedFirstMonomial_quarticBound244'),
    ('theorem', 'weightedH3CanonicalThirdJetEnergy_zero244'),
    ('theorem', 'weightedH3CanonicalSignedFirstMonomial_zero244'),
    ('theorem', 'weightedH3CanonicalSignedFirstMonomial_continuousAt_zero244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in content:
            raise SystemExit(f'Missing {kind} declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([v for v in old if v.startswith('import ')] + [imp]))
    remaining = [v for v in old if not v.startswith('import ')]
    while remaining and not remaining[0].strip():
        remaining.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for directive in ('#check ' + q, '#print axioms ' + q):
            if directive not in remaining:
                remaining.append(directive)
    merged = '\n'.join(imports + [''] + remaining).rstrip() + '\n'
    if merged != AUDIT.read_text():
        AUDIT.write_text(merged)
    print('Registered weighted H3 canonical quartic bounds and zero continuity')

if __name__ == '__main__':
    main()
