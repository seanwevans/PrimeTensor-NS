#!/usr/bin/env python3
"""Register the actual Axis Depth.three Hermitian six-packet Schwartz field."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdAxisSchwartzPacket244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisComplexDot244',
    'thirdFullAxisComplexWindowPacket244',
    'thirdFullAxisComplexWindowPacket_solenoidal244',
    'thirdFullAxisComplexWindowPacket_contDiff244',
    'thirdFullAxisComplexWindowPacket_hasCompactSupport244',
    'thirdFullFixedCenterTransverseGerm_contDiff244',
    'thirdFullAxisPositiveThreePacket244',
    'thirdFullAxisPositiveThreePacket_solenoidal244',
    'thirdFullAxisPositiveThreePacket_contDiff244',
    'thirdFullAxisPositiveThreePacket_hasCompactSupport244',
    'thirdFullAxisHermitianize244',
    'thirdFullAxisHermitianize_reality244',
    'thirdFullAxisHermitianize_solenoidal244',
    'thirdFullAxisHermitianize_contDiff244',
    'thirdFullAxisHermitianize_hasCompactSupport244',
    'thirdFullAxisSixFourierPacket244',
    'thirdFullAxisSixFourierPacket_solenoidal244',
    'thirdFullAxisSixFourierPacket_reality244',
    'thirdFullAxisSixFourierPacket_contDiff244',
    'thirdFullAxisSixFourierPacket_hasCompactSupport244',
    'thirdFullAxisSixSchwartzPacket244',
    'thirdFullAxisSixSchwartzPacket_apply244',
    'thirdFullAxisSixSchwartzPacket_solenoidal244',
    'thirdFullAxisSixSchwartzPacket_reality244',
)

def main():
    for file in (SOURCE, ROOT, AUDIT):
        if not file.is_file():
            raise SystemExit(f'Missing prerequisite: {file}')
    s = SOURCE.read_text()
    for name in NAMES:
        if not any(f'{kind} {name}' in s for kind in ('theorem', 'noncomputable def', 'def')):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    original = ROOT.read_text().splitlines()
    if imp not in original:
        ROOT.write_text('\n'.join(original + [imp]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in old if line.startswith('import ')] + [imp]
    ))
    body = [line for line in old if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {q}', f'#print axioms {q}'):
            if cmd not in body:
                body.append(cmd)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != AUDIT.read_text():
        AUDIT.write_text(result)
    print('Registered full-third Hermitian Axis Schwartz packet')

if __name__ == '__main__':
    main()
