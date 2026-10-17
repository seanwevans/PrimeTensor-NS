#!/usr/bin/env python3
"""Register orderwise L2/L4 graph control of all 243 Schwartz slots."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzOrderwiseGraph244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'schwartzThirdJetDifferenceRoot244'),
    ('def', 'schwartzSecondJetDifferenceRoot244'),
    ('def', 'schwartzThirdJetGraphDistance244'),
    ('def', 'schwartzSecondJetGraphDistance244'),
    ('def', 'schwartzMixedJetGraphDistance244'),
    ('theorem', 'schwartzMixedJetGraphDistance_nonneg244'),
    ('theorem', 'schwartzMixedJetGraphDistance_bounds_slots244'),
    ('def', 'SchwartzMixedJetGraphCauchy244'),
    ('theorem', 'SchwartzMixedJetGraphCauchy244.toStrongJets'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_existsLimit_of_mixedJetGraph244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered orderwise mixed Schwartz jet graph distance and signed monomial limit')

if __name__ == '__main__':
    main()
