#!/usr/bin/env python3
"""Register the full real-Schwartz physical dissipation and exact NS balance."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzDissipationBalance244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('thirdFullPhysicalDissipation0_eq_energy1_244', 'thirdFullPhysicalDissipation1_eq_energy2_244', 'thirdFullPhysicalDissipation2_eq_energy3_244', 'thirdFullPhysicalDissipation_eq_lowerEnergies_add_top244', 'thirdFullSchwartz_pathFullDissipation_eq244', 'h3Path_exactEnergyBalance_fullThirdSchwartz244', 'h3Path_energySlope_pos_of_realSchwartzFullBudget244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if any(token in source for token in ('sorry', 'admit')):
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
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
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered full Schwartz dissipation/NS balance')

if __name__ == '__main__':
    main()
