#!/usr/bin/env python3
"""Register the exact full E3 comparison for second-jet Frechet squares."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetFrechetFullEnergy'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy',
    'lowNormalRealSchwartz_thirdJet_coordinateSum_eq_E3',
    'lowNormalRealSchwartz_secondJet_frechetEnergy_le_card_mul_E3',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for name in NAMES:
        if not any(f'{kind} {name}' in source for kind in ('def', 'theorem')):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in audit_lines if s.startswith('import ')] + [imp]))
    body = [s for s in audit_lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered full 27-to-81 second-jet Frechet energy inequality')

if __name__ == '__main__':
    main()
