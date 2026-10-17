#!/usr/bin/env python3
"""Register the signed 243-slot Cauchy/completion criteria in PrimeTensor's audits."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzCauchyCompletion244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'Schwartz243SlotErrorCauchy244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_cauchy_of_slotErrors244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_existsLimit_of_slotErrors244'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_limits_eq_of_crossError244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
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
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered Schwartz 243-slot Cauchy completion and cross-sequence uniqueness')

if __name__ == '__main__':
    main()
