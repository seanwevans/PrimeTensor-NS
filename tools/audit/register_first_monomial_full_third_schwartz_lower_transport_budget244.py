#!/usr/bin/env python3
"""Register the full Schwartz lower-transport budget module, idempotently."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzLowerTransportBudget244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'lowNormalRealSchwartzH3FullDissipation244',
    'thirdFullSchwartz_lowerDissipation_le_energy244',
    'thirdFullSchwartz_fullDissipation_le_top_add_energy244',
    'thirdFullSchwartz_fixedKinetic_completeViscousAdverse244',
    'FullThirdUnforcedCompleteStaticCoercivity244',
    'thirdFullSchwartz_no_completeStaticCoercivity244',
    'h3Path_exactEnergyBalance_fullThirdSchwartz_noT0_244',
    'h3Path_lowerTransport_abs_le_schwartzEnergy244',
    'h3Path_energySlope_pos_of_completeSchwartzGradientBudget244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    import re
    if re.search(r'\b(sorry|admit)\b', source):
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if not re.search(r'\b(?:theorem|def)\s+' + re.escape(name) + r'\b', source):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {q}', f'#print axioms {q}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered full Schwartz lower-transport budget')

if __name__ == '__main__':
    main()
