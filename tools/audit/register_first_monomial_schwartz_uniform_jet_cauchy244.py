#!/usr/bin/env python3
"""Register strong jet Cauchy to canonical signed Schwartz monomial completion."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzUniformJetCauchy244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'Schwartz243UniformJetRoots244'),
    ('def', 'Schwartz243StrongJetCauchy244'),
    ('theorem', 'schwartz243_slotErrors_of_uniformStrongJets244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_cauchy_of_uniformStrongJets244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_existsLimit_of_uniformStrongJets244'),
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
    print('Registered uniform Schwartz 243-slot jet Cauchy/limit theorem')

if __name__ == '__main__':
    main()
