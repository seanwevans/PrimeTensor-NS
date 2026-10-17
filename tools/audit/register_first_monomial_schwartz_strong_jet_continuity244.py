#!/usr/bin/env python3
"""Register Schwarz strong-jet continuity in root and theorem audits."""
from pathlib import Path

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3SchwartzStrongJetContinuity244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('abbrev', 'SchwartzStrongJetSlots244'),
    ('def', 'SchwartzStrongJetConvergence244'),
    ('theorem', 'schwartzPhysicalSlotPerturbation_tendsto_zero244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_tendsto_of_strongJets244'),
    ('theorem', 'h3PathCanonical_approximable_of_strongSchwartzJets244'),
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
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered 243-slot strong Schwartz jet continuity and PDE-facing approximation criterion')

if __name__ == '__main__':
    main()
