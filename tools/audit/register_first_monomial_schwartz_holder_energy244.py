#!/usr/bin/env python3
"""Idempotently register the 243-slot Holder to global-energy closure."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderEnergy244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'lowNormalRealSchwartz_firstMonomial_holder244_energyMass',
    'lowNormalRealSchwartz_firstMonomial_holder244_energyGN',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem {name}')
    import_line = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if import_line not in root:
        ROOT.write_text('\n'.join(root + [import_line]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [import_line]))
    body = [ln for ln in lines if not ln.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in body:
                body.append(command)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != content:
        AUDIT.write_text(content)
    print('Registered 243-slot Holder global E2/E3 energy closure')

if __name__ == '__main__':
    main()
