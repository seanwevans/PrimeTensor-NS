#!/usr/bin/env python3
"""Register the actual full-third unforced sign and exact NS balance frontier."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdUnforcedSignFrontier244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'fullSchwartzThirdCommutator_negate244',
    'fullSchwartzTopDissipation_negate244',
    'fullSchwartzH3Energy_negate244',
    'fullSchwartzKineticEnergy_negate244',
    'thirdFullSchwartz_oneSeed_adverseUnforcedTransport244',
    'thirdFullSchwartz_fixedKinetic_unforcedAdverse244',
    'thirdFullSchwartz_fixedKinetic_viscousTwoAdverse244',
    'FullThirdUnforcedStaticCoercivity244',
    'thirdFullSchwartz_no_unforced_staticCoercivity244',
    'h3Path_energySlope_pos_of_fullThird_adverseSlice244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    for name in NAMES:
        if not any((prefix + name) in source for prefix in ('theorem ', 'def ')):
            raise SystemExit('Missing declaration: ' + name)
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Forbidden proof placeholder')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for item in (f'#check {q}', f'#print axioms {q}'):
            if item not in body:
                body.append(item)
    update = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if update != original:
        AUDIT.write_text(update)
    print('Registered full-third unforced sign frontier')

if __name__ == '__main__':
    main()
