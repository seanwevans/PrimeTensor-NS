#!/usr/bin/env python3
"""Register the real full-third twelve-sector integral localization bridge."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealCoherentIntegralTube244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisCoherentPairCenterSet_isCompact244',
    'thirdFullAxisCoherentPairCenterSet_mem244',
    'thirdFullAxisRealSchwartzTripleMass_mem_coherent_tube244',
    'thirdFullAxisRealSchwartzTripleMass_zero_off_tube244',
    'thirdFullAxisRealSchwartz_exists_width_in_coherent_tube244',
    'thirdFullAxisRealSchwartzTripleComponent_zero_of_mass244',
    'thirdFullAxisRealSchwartzWeightedTrilinear_zero_off_tube244',
    'thirdFullAxisRealSchwartzWeightedTrilinear_integral_eq_tube244',
    'thirdFullAxisRealSchwartzWeightedTrilinear_exists_integral_tube244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    src = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [imp]
    ))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {q}', f'#print axioms {q}'):
            if cmd not in body:
                body.append(cmd)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != original:
        AUDIT.write_text(result)
    print('Registered full-third coherent-orbit integral tube')

if __name__ == '__main__':
    main()
