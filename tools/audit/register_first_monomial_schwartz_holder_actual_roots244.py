#!/usr/bin/env python3
"""Register the 243-slot actual Schwartz root identities and norm bridge."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderActualRoots244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'actualHolderRoots244_nonneg',
    'actualHolderRoots244_powers',
    'actualHolderRoots244_globalMasses',
    'actualHolderRoots244_realSlot_of_normIdentities',
    'lowNormalRealSchwartz_firstMonomial_holder244_energyGN_of_normIdentities',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in body:
                body.append(command)
    new_audit = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != new_audit:
        AUDIT.write_text(new_audit)
    print('Registered actual Schwartz 243-slot roots and Lp normalization frontier')

if __name__ == '__main__':
    main()
