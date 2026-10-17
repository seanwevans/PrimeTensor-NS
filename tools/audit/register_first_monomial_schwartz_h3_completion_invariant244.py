#!/usr/bin/env python3
"""Register the actual H3 Schwartz Cauchy-completion observable and invariance."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzH3CompletionInvariant244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'Schwartz243SingleFieldRootBound244'),
    ('theorem', 'schwartzPhysicalSlotPerturbation_le_mixedGraph244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_crossGraph_bound244'),
    ('structure', 'SchwartzH3CauchyFamily244'),
    ('def', 'completedSchwartzH3FirstMonomial244'),
    ('theorem', 'completedSchwartzH3FirstMonomial_tendsto244'),
    ('def', 'SchwartzH3FamiliesCrossGraphVanishing244'),
    ('theorem', 'completedSchwartzH3FirstMonomial_eq_of_crossGraph244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered completed H3 signed transport observable and cross-graph invariance')

if __name__ == '__main__':
    main()
